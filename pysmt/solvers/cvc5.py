#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
from __future__ import absolute_import

from pysmt.exceptions import SolverAPINotFound

try:
    import cvc5
except ImportError:
    raise SolverAPINotFound("CVC5 not found, run `pip install cvc5`")

import pysmt.typing as types
from pysmt.logics import PYSMT_LOGICS, ARRAYS_CONST_LOGICS

from pysmt.solvers.solver import Solver, Converter, SolverOptions, ComplexExpr
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              InternalSolverError,
                              NonLinearError, PysmtValueError, ModelUnsatError, ModelUnavilableError,
                              PysmtTypeError)
from pysmt.walkers import DagWalker
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.eager import EagerModel
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.constants import Fraction, is_pysmt_integer, to_python_integer

# SEE https://cvc5.github.io/docs/cvc5-1.1.1/api/python/pythonic/pythonic.html
class CVC5Options(SolverOptions):

    def __init__(self, **base_options):
        SolverOptions.__init__(self, **base_options)
        # TODO: CVC5 Supports UnsatCore extraction
        # but we did not wrapped it yet. (See #349)
        if self.unsat_cores_mode is not None:
            raise PysmtValueError("'unsat_cores_mode' option not supported.")

    @staticmethod
    def _set_option(cvc5solver, name, value):
        try:
            cvc5solver.setOption(name, value)
        except:
            raise PysmtValueError("Error setting the option '%s=%s'" % (name,value))

    def __call__(self, solver):
        if solver.logic_name == "QF_SLIA":
            self._set_option(solver.cvc5solver,
                             "strings-exp", "true")
        # https://github.com/cvc5/cvc5/issues/5323
        self._set_option(solver.cvc5solver,
                         "fmf-fun", "true")
        self._set_option(solver.cvc5solver,
                         "produce-models", str(self.generate_models).lower())
        self._set_option(solver.cvc5solver,
                         "incremental", str(self.incremental).lower())
        if self.random_seed is not None:
            self._set_option(solver.cvc5solver,
                             "seed", str(self.random_seed))

        for k,v in self.solver_options.items():
            self._set_option(solver.cvc5solver, str(k), str(v))

# EOC self.KindOptions


class CVC5Solver(Solver, SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = PYSMT_LOGICS -\
             ARRAYS_CONST_LOGICS -\
             set(l for l in PYSMT_LOGICS if l.theory.strings)

    OptionsClass = CVC5Options
    
    SOLVERFOR_LOGIC_NAMES=['AUFLIA', 'ALIA', 'AUFLIRA', 'AUFNIRA', 'LRA', 'LIA', 'NIA',
                           'NRA', 'QF_ABV', 'QF_AUFBV', 'QF_AUFLIA', 'QF_ALIA', 'QF_AX',
                           'QF_BV', 'BV', 'UFBV', 'QF_IDL', 'QF_LIA', 'QF_LRA', 'QF_NIA',
                           'QF_NRA', 'QF_RDL', 'QF_UF', 'UF', 'QF_UFBV', 'QF_UFIDL', 
                           'QF_UFLIA', 'QF_UFLRA', 'QF_UFNRA', 'QF_UFNIA', 'UFLRA', 'UFNIA']

    def __init__(self, environment, logic, **options):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        **options)

        self.logic_name = str(logic)
        if "t" in self.logic_name:
            # Custom Type extension
            self.logic_name = self.logic_name.replace("t","")
        if self.logic_name == "QF_BOOL":
            self.logic_name = "QF_LRA"
        elif self.logic_name == "BOOL":
            self.logic_name = "LRA"
        if str(self.logic_name) in CVC5Solver.SOLVERFOR_LOGIC_NAMES:
            self.cvc5solver = cvc5.SolverFor(str(self.logic_name))
        else:
            self.cvc5solver = cvc5.Solver()
        self.options(self)
        self.declarations = set()
        self.mgr = environment.formula_manager

        self.reset_assertions()
        self.converter = CVC5Converter(environment, self.cvc5solver)

        return

    def reset_assertions(self):
        self.cvc5solver.resetAssertions()
        self.options(self)

    def declare_variable(self, var):
        raise NotImplementedError
    
    @clear_pending_pop
    def define_fun_rec(self, name, args, rtype, expr): 
        # note that name is str type
        self.converter._rec_funcs[name] = (args, rtype, expr) # zenan: lazy define rec_fun
        return None

    def add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.converter.convert(formula)
        self.cvc5solver.assertFormula(term)
        return

    def get_model(self):
        assignment = {}
        for s in self.environment.formula_manager.get_all_symbols():
            if s.is_term():
                if s.symbol_type().is_custom_type(): continue
                v = self.get_value(s)
                assignment[s] = v
        return EagerModel(assignment=assignment, environment=self.environment)

    def solve(self, assumptions=None):
        if assumptions is not None:
            conj_assumptions = self.environment.formula_manager.And(assumptions)
            self.Kind_assumption = self.converter.convert(conj_assumptions)
            res = self.cvc5solver.checkSat(self.Kind_assumption)
        else:
            try:
                res = self.cvc5solver.checkSat()
            except Exception as e:
                raise InternalSolverError(e)

        # Convert returned type
        self.res_type = res
        if cvc5.Result.isUnknown(res):
            raise SolverReturnedUnknownResultError()
        elif cvc5.Result.isUnsat(res):
            raise ModelUnsatError("cvc5 returns unsat")
        else:
            return cvc5.Result.isSat(res)

    # def push(self, levels=1):
    #     if not self.options.incremental:
    #         # The exceptions from self.Kind are not raised correctly
    #         # (probably due to the wrapper)
    #         # Therefore, we need to check that we can actually do a push
    #         raise NotImplementedError("The solver is not incremental")

    #     for _ in range(levels):
    #         self.self.Kind.push()
    #     return

    # def pop(self, levels=1):
    #     for _ in range(levels):
    #         self.self.Kind.pop()
    #     return

    # def print_model(self, name_filter=None):
    #     if name_filter is None:
    #         var_set = self.declarations
    #     else:
    #         var_set = (var for var in self.declarations\
    #                    if name_filter(var))
    #     for var in var_set:
    #         print("%s = %s", (var.symbol_name(), self.get_value(var)))
    #     return

    def get_value(self, item):
        if not hasattr(self, 'res_type'):
            raise ModelUnavilableError("model is not available, ensure `check-sat` is executed")
        self._assert_no_function_type(item)
        term = self.converter.convert(item)
        if isinstance(term, ComplexExpr):
            real, image = term
            self.Kind_res = self.self.Kind.getValue(real)
            real_res = self.converter.back(self.Kind_res)
            self.Kind_res = self.self.Kind.getValue(image)
            image_res = self.converter.back(self.Kind_res)
            res = self.converter.mgr.ToComplex(real_res, image_res)
        else:
            cvc5_res = self.cvc5solver.getValue(term)
            res = self.converter.back(cvc5_res)
            if self.environment.stc.get_type(item).is_real_type() and \
                self.environment.stc.get_type(res).is_int_type():
                res = self.environment.formula_manager.Real(Fraction(res.constant_value(), 1))
        return res

    def _exit(self):
        del self.cvc5solver

    def set_option(self, name, value):
        """Sets an option.

        :param name and value: Option to be set
        :type name: String
        :type value: String
        """
        self.cvc5.setOption(name, value)



class CVC5Converter(Converter, DagWalker):

    def __init__(self, environment, cvc5_solver):
        DagWalker.__init__(self, environment)
        
        self.mkConst = cvc5_solver.mkConst
        self.mkReal = cvc5_solver.mkReal
        self.mkInteger = cvc5_solver.mkInteger
        self.mkBoolean = cvc5_solver.mkBoolean
        self.mkBitVector = cvc5_solver.mkBitVector
        self.mkVar = cvc5_solver.mkVar
        self.mkFunctionSort = cvc5_solver.mkFunctionSort
        self.mkTerm = cvc5_solver.mkTerm
        self.defineFun = cvc5_solver.defineFun
        self.defineFunRec = cvc5_solver.defineFunRec
        self.mkOp = cvc5_solver.mkOp
        self.mkPi = cvc5_solver.mkPi
        self.Kind = cvc5.Kind

        self.realType = cvc5_solver.getRealSort()
        self.intType = cvc5_solver.getIntegerSort()
        self.boolType = cvc5_solver.getBooleanSort()
        self.stringType = cvc5_solver.getStringSort()

        self.aux_id = 0 # count for auxiliary variable
        self.declared_vars = {} 
        self._cvc5_func_decl_cache = {}
        self._rec_funcs = {}
        self._back_memoization = {}
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type
        return

    def declare_variable(self, var):
        """
        Note: mkVar() can only be used for variables that are bound by a quantifier
        Use mkConst() instead. See more: https://github.com/cvc5/cvc5/issues/4828
        """
        if not var.is_symbol():
            raise PysmtTypeError("Trying to declare as a variable something "
                                 "that is not a symbol: %s" % var)
        sname = var.symbol_name()
        if sname not in self.declared_vars:
            symbol_type = var.symbol_type()
            if symbol_type.is_complex_type():
                real_name = sname + "_real"
                real_decl = self.mkConst(self.realType, real_name)
                image_name = sname + "_image"
                image_decl = self.mkConst(self.realType, image_name)
                decl = ComplexExpr(real_decl, image_decl)
                self.declared_vars[var] = decl
            else:
                cvc5_type = self._type_to_cvc5(var.symbol_type())
                decl = self.mkConst(cvc5_type, var.symbol_name())
                self.declared_vars[var] = decl

    def body_walk(self, formula):
        """ This is for define-fun-rec
            we refresh the stack to convert the formula
        """
        copy_stack = self.stack
        self.stack = []
        z3term = self.walk(formula)
        self.stack = copy_stack
        return z3term
    
    def back(self, expr):
        res = None
        if not expr.hasOp():
            res = self._back_single_term(expr, args=())
        else:
            stack = [expr]
            while len(stack) > 0:
                current = stack.pop()
                key = current.getId()
                if key not in self._back_memoization:
                    self._back_memoization[key] = None
                    stack.append(current)
                    for c in current:
                        stack.append(c)
                elif self._back_memoization[key] is None:
                    args = [self._back_memoization[c.getId()] for c in current]
                    res = self._back_single_term(current, args)
                    self._back_memoization[key] = res
                else:
                    pass
            res = self._back_memoization[expr.getId()]
        # raise PysmtTypeError("Unsupported expression: %s" % expr)
        return res
        
    
    def _back_single_term(self, expr, args):
        if expr.hasOp(): # detect complex expressions
            args = [self.mgr.ToReal(a) for a in args if a is not None]
        if expr.isBooleanValue():
            v = expr.getBooleanValue()
            res = self.mgr.Bool(v)
        elif expr.isIntegerValue():
            v = expr.getIntegerValue()
            res = self.mgr.Int(int(v))
        elif expr.isRealValue():
            v = str(expr.getRealValue())
            res = self.mgr.Real(Fraction(v))
        elif expr.isBitVectorValue():
            bv = expr.getBitVectorValue().toString()
            width = bv.getSize()
            res = self.mgr.BV(int(v), width)
        elif expr.isStringValue():
            v = expr.getStringValue().toString()
            res = self.mgr.String(v)
        elif expr.isConstArray():
            const_ = expr.getConstArrayBase()
            array_type = self._cvc5_type_to_type(const_.getType())
            base_value = self.back(const_)
            res = self.mgr.Array(array_type.index_type,
                                    base_value)
        elif expr.getKind() == self.Kind.PI:
            res = self.mgr.PI()
        elif expr.getKind() == self.Kind.APPLY_UF:
            decl = expr.getOperator()
            decl_name = decl.toString()
            if decl_name in self.declared_vars:
                decl = self.declared_vars[decl_name]
            else:
                decl_type = decl.getSort()
                decl_type = self._cvc5_type_to_type(decl_type)
                decl = self.mgr.Symbol(decl_name, decl_type)
                self.declared_vars[decl_name] = decl
            res = self.mgr.Function(decl, args)
        elif expr.getKind() == self.Kind.ITE:
            res = self.mgr.Ite(args[0], args[1], args[2])
        elif expr.getKind() == self.Kind.EQUAL:
            res = self.mgr.Equals(args[0], args[1])
        elif expr.getKind() == self.Kind.DISTINCT:
            res = self.mgr.Distinct(args)
        elif expr.getKind() == self.Kind.AND:
            res = self.mgr.And(args)
        elif expr.getKind() == self.Kind.OR:
            res = self.mgr.Or(args)
        elif expr.getKind() == self.Kind.NOT:
            res = self.mgr.Not(args[0])
        elif expr.getKind() == self.Kind.IMPLIES:
            res = self.mgr.Implies(args[0], args[1])
        elif expr.getKind() == self.Kind.LEQ:
            res = self.mgr.LE(args[0], args[1])
        elif expr.getKind() == self.Kind.LT:
            res = self.mgr.LT(args[0], args[1])
        elif expr.getKind() == self.Kind.GEQ:
            res = self.mgr.GE(args[0], args[1])
        elif expr.getKind() == self.Kind.GT:
            res = self.mgr.GT(args[0], args[1])
        elif expr.getKind() == self.Kind.ADD:
            res = self.mgr.Plus(args)
        elif expr.getKind() == self.Kind.SUB:
            res = self.mgr.Minus(args[0], args[1])
        elif expr.getKind() == self.Kind.MULT:
            res = self.mgr.Times(args)
        elif expr.getKind() == self.Kind.DIVISION:
            res = self.mgr.Div(args[0], args[1])
        elif expr.getKind() == self.Kind.POW:
            res = self.mgr.Pow(args[0], args[1])
        elif expr.getKind() == self.Kind.SQRT:
            res = self.mgr.Sqrt(args[0])
        elif expr.getKind() == self.Kind.INTERNAL_KIND:
            op = self.parse_op(expr)
            return op(*args)
        else:
            raise PysmtTypeError(f"Unsupported expression: {expr}, whose Sort is {expr.getSort()} Kind is {expr.getKind()}")        
        return res

    def parse_op(self, expr):
        str_expr = str(expr)
        str_op = str_expr.split(" ")[0][1:]
        if str_op == "+":
            return self.mgr.Plus
        elif str_op == "-":
            return self.mgr.Minus
        elif str_op == "*":
            return self.mgr.Times
        elif str_op == "/":
            return self.mgr.Div
        else:
            raise PysmtTypeError(f"Unsupported operator {str_op} in the expression: {expr}")

    @catch_conversion_error
    def convert(self, formula):
        return self.walk(formula)

    """_summary_
        The following are constant and symbol conversion
    """
    def walk_symbol(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        if formula not in self.declared_vars:
            self.declare_variable(formula)
        return self.declared_vars[formula]

    def walk_real_constant(self, formula, **kwargs):
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        if d == 1.0:
            return self.mkReal(str(n))
        else:
            return self.mkReal(str(n), str(d))

    def walk_int_constant(self, formula, **kwargs):
        assert is_pysmt_integer(formula.constant_value())
        rep = str(formula.constant_value())
        return self.mkInteger(rep)
    
    def walk_complex_constant(self, formula, **kwargs):
        real, image = formula.constant_value()
        rep = ComplexExpr(self.walk_real_constant(real), self.walk_real_constant(image))
        return rep
    
    def walk_bool_constant(self, formula, **kwargs):
        return self.mkBoolean(formula.constant_value())

    def walk_function(self, formula, args, **kwargs):
        """ Create a CVC5 Function Application for the given function. 
            If the function is recursive, then create a CVC5 Recursive Function Application. """
        name = formula.function_name() # this is FNode
        if name in self.declared_vars:
            decl = self.declared_vars[name]
        elif str(name) in self._rec_funcs:
            variables, rtype, expr = self._rec_funcs[str(name)]
            cvc5func = self._cvc5_rec_func_decl(name)
            body = self.body_walk(expr) # body_walk introduce bound variables
            body, var_list = self._rename_bound_variables(body, variables)
            bound_vars_list = self.mkTerm(self.Kind.VARIABLE_LIST, *var_list)
            cvc5func = self.defineFunRec(cvc5func, bound_vars_list, body)
            self.declared_vars[name] = cvc5func
            decl = self.declared_vars[name]
        else:
            self.declare_variable(name)
            decl = self.declared_vars[name]
        return self.mkTerm(self.Kind.APPLY_UF, decl, *args)
    
    def _cvc5_rec_func_decl(self, func_name):
        """Create a CVC5 Function Declaration for the given function."""
        self.declare_variable(func_name)
        decl = self.declared_vars[func_name]
        return decl        
    
    """_summary_
        The following are logic relation
    """
    def walk_and(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.AND, *args)

    def walk_or(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.OR, *args)

    def walk_not(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.NOT, args[0])

    def walk_iff(self, formula, args, **kwargs):
        # left_to_right = self.mkTerm(self.Kind.IMPLIES, args[0], args[1])
        # right_to_left = self.mkTerm(self.Kind.IMPLIES, args[1], args[0])
        # return self.mkTerm(self.Kind.AND, left_to_right, right_to_left)
        return self.mkTerm(self.Kind.EQUAL, args[0], args[1])

    def walk_implies(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.IMPLIES, args[0], args[1])

    def walk_le(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.LEQ, args[0], args[1])

    def walk_lt(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.LT, args[0], args[1])

    def walk_ite(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.ITE, args[0], args[1], args[2])
    
    def walk_numer_ite(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.ITE, args[0], args[1], args[2])

    """_summary_
        The following are logic quantifier
    """
    def walk_exists(self, formula, args, **kwargs):
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        bound_vars_list = self.mkTerm(self.Kind.VARIABLE_LIST, var_list)
        return self.mkTerm(self.Kind.EXISTS,
                           bound_vars_list,
                           bound_formula)

    def walk_forall(self, formula, args, **kwargs):
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        bound_vars_list = self.mkTerm(self.Kind.VARIABLE_LIST, *var_list)
        return self.mkTerm(self.Kind.FORALL,
                           bound_vars_list,
                           bound_formula)

    """_summary_
        The following are linear arithmetic operations
    """
    def walk_equals(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.EQUAL, args[0], args[1])

    def walk_plus(self, formula, args, **kwargs):
        res = self.mkTerm(self.Kind.ADD, *args)
        return res

    def walk_minus(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.SUB, args[0], args[1])
    
    def walk_times(self, formula, args, **kwargs):
        # if sum(1 for x in formula.args() if x.get_free_variables()) > 1:
            # raise NonLinearError(formula)
        res = args[0]
        for x in args[1:]:
            res = self.mkTerm(self.Kind.MULT, res, x)
        return res
    
    def walk_intdiv(self, formula, args, **kwargs):
        res = args[0]
        for x in args[1:]:
            res = self.mkTerm(self.Kind.INTS_DIVISION, res, x)
        return res
    
    def walk_div(self, formula, args, **kwargs):
        if self._get_type(formula.args()[0]).is_int_type() and self._get_type(formula.args()[1]).is_int_type():
            return self.mkTerm(self.Kind.INTS_DIVISION, args[0], args[1])
        else:
            return self.mkTerm(self.Kind.DIVISION, args[0], args[1])

    """_summary_
        The following are non-linear arithmetic operations
    """
    def walk_mod(self, formula, args, **kwargs):
        res = self.mkTerm(self.Kind.INTS_MODULUS, args[0], args[1])
        return res
    
    def walk_even(self, formula, args, **kwargs):
        self.Kindzero = self.mkInteger("0")
        self.Kindtwo = self.mkInteger("2")
        self.Kindterm = args[0]
        self.Kindmod2 = self.mkTerm(self.Kind.INTS_MODULUS, self.Kindterm, self.Kindtwo)
        self.Kindterm = self.mkTerm(self.Kind.EQUAL, self.Kindmod2, self.Kindzero)
        return self.Kindterm
    
    def walk_prime(self, formula, args, **kwargs):
        self.Kindone = self.mkInteger("1")
        self.Kindtwo = self.mkInteger("2")
        self.Kindterm = args[0]
        self.Kindmod2 = self.mkTerm(self.Kind.INTS_MODULUS, self.Kindterm, self.Kindtwo)
        self.Kindterm = self.mkTerm(self.Kind.EQUAL, self.Kindmod2, self.Kindone)
        return self.Kindterm
    
    def walk_pow(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.POW, args[0], args[1])
    
    def walk_sqrt(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.SQRT, args[0])

    def walk_exp(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.EXPONENTIAL, args[0])
    
    def walk_log(self, formula, args, **kwargs):
        # aux_name = "log_aux_" + str(self.aux_id)
        # log_term = self.mkConst(self.realType, aux_name)
        # exp_term = self.walk_exp(formula, args=(log_term,))
        # self.mkTerm(self.Kind.EQUAL, args[0], exp_term)
        # return log_term
        raise InternalSolverError("cvc5 does not support logarithmic function")

    def walk_sin(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.SINE, args[0])
    
    def walk_toreal(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.TO_REAL, args[0])
    
    def walk_pi(self, formula, args, **kwargs):
        return self.mkPi()
    
    def walk_e(self, formula, args, **kwargs):
        cvc5one = self.mkReal("1")
        return self.mkTerm(self.Kind.EXPONENTIAL, cvc5one)
    
    """_summary_
    The following are complex arithmetic operations
    """
    def walk_complex_equals(self, formula, args, **kwargs):
        """ complex_equals of (a+bi) = (c+di) """
        a, b = args[0]
        c, d = args[1]
        real_eq = self.walk_equals(formula, (a, c))
        image_eq = self.walk_equals(formula, (b, d))
        return self.walk_and(formula, (real_eq, image_eq))

    def walk_complex_plus(self, formula, args, **kwargs):
        """ complex_plus of (a+bi) + (c+di)"""
        a, b = args[0]
        c, d = args[1]
        real_cvc5term = self.walk_plus(formula, (a, c))
        image_cvc5term = self.walk_plus(formula, (b, d))
        cvc5term = ComplexExpr(real_cvc5term, image_cvc5term)
        return cvc5term
    
    def walk_complex_minus(self, formula, args, **kwargs):
        """ complex_minus of (a+bi) - (c+di) """
        a, b = args[0]
        c, d = args[1]
        real_cvc5term = self.walk_minus(formula, (a, c))
        image_cvc5term = self.walk_minus(formula, (b, d))
        cvc5term = ComplexExpr(real_cvc5term, image_cvc5term)
        return cvc5term
    
    def walk_complex_times(self, formula, args, **kwargs):
        """ complex_times of (a+bi) * (c+di) """
        a, b = args[0]
        c, d = args[1]
        ac = self.walk_times(formula, (a, c))
        bd = self.walk_times(formula, (b, d))
        real_cvc5term = self.walk_minus(formula, (ac, bd))
        ad = self.walk_times(formula, (a, d))
        bc = self.walk_times(formula, (b, c))
        image_cvc5term = self.walk_plus(formula, (ad, bc))
        cvc5term = ComplexExpr(real_cvc5term, image_cvc5term)
        return cvc5term
    
    def walk_complex_div(self, formula, args, **kwargs):
        """ complex_div of (a+bi) / (c+di) """
        a, b = args[0]
        c, d = args[1]
        c_square = self.walk_times(formula, (c, c))
        d_square = self.walk_times(formula, (d, d))
        denominator = self.walk_plus(formula, (c_square, d_square)) 
        ac = self.walk_times(formula, (a, c))
        bd = self.walk_times(formula, (b, d))
        numerator_real = self.walk_plus(formula, (ac, bd))
        ad = self.walk_times(formula, (a, d))
        bc = self.walk_times(formula, (b, c))
        numerator_image = self.walk_minus(formula, (bc, ad))
        real_cvc5term = self.walk_div(formula, (numerator_real, denominator))
        image_cvc5term = self.walk_div(formula, (numerator_image, denominator))
        cvc5term = ComplexExpr(real_cvc5term, image_cvc5term)
        return cvc5term

    """_summary_
    MISC. operations
    """
    def walk_array_store(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.STORE, args[0], args[1], args[2])

    def walk_array_select(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.SELECT, args[0], args[1])
    
    def walk_bv_constant(self, formula, **kwargs):
        vrepr = str(formula.constant_value())
        width = formula.bv_width()
        return self.mkBitVector(width, self.mkInteger(vrepr))

    def walk_bv_ult(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_ULT, args[0], args[1])

    def walk_bv_ule(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_ULE, args[0], args[1])

    def walk_bv_concat(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_CONCAT, args[0], args[1])

    def walk_bv_extract(self, formula, args, **kwargs):
        # ext = self.mkConst(self.Kind.BitVectorExtract(formula.bv_extract_end(),
                                                #  formula.bv_extract_start()))
        # return self.mkTerm(self.Kind.BITVECTOR_EXTRACT, ext, args[0])
        raise InternalSolverError("CVC5 bv_extract is not implemented")

    def walk_bv_or(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_OR, args[0], args[1])

    def walk_bv_not(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_NOT, args[0])

    def walk_bv_and(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_AND, args[0], args[1])

    def walk_bv_xor(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_XOR, args[0], args[1])

    def walk_bv_add(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_PLUS, args[0], args[1])

    def walk_bv_sub(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_SUB, args[0], args[1])

    def walk_bv_neg(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_NEG, args[0])

    def walk_bv_mul(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_MULT, args[0], args[1])

    def walk_bv_tonatural(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_TO_NAT, args[0])

    def walk_bv_udiv(self, formula, args, **kwargs):
        # Force deterministic semantics of division by 0
        # If the denominator is bv0, then the result is ~0
        n,d = args
        if d.isConst():
            bv = d.getConstBitVector()
            v = bv.getValue().toString()
            if v == "0":
                return self.mkTerm(self.Kind.BITVECTOR_NOT, d)
            else:
                return self.mkTerm(self.Kind.BITVECTOR_UDIV, n, d)
        else:
            # (d == 0) ? ~0 : n bvudiv d
            base = self.mkTerm(self.Kind.BITVECTOR_UDIV, n, d)
            zero = self.mkBitVector(formula.bv_width(),
                                               self.mkInteger("0"))
            notzero = self.mkTerm(self.Kind.BITVECTOR_NOT, zero)
            test = self.mkTerm(self.Kind.EQUAL, d, zero)
            return self.mkTerm(self.Kind.ITE, test, notzero, base)

    def walk_bv_urem(self, formula, args, **kwargs):
        # Force deterministic semantics of reminder by 0
        # If the denominator is bv0, then the result is the numerator
        n,d = args
        if d.isConst():
            bv = d.getConstBitVector()
            v = bv.getValue().toString()
            if v == "0":
                return n
            else:
                return self.mkTerm(self.Kind.BITVECTOR_UREM, n, d)
        else:
            # (d == 0) ? n : n bvurem d
            base = self.mkTerm(self.Kind.BITVECTOR_UREM, n, d)
            zero = self.mkConst(self.Kind.BitVector(formula.bv_width(),
                                               self.Kind.Integer("0")))
            test = self.mkTerm(self.Kind.EQUAL, d, zero)
            return self.mkTerm(self.Kind.ITE, test, n, base)

    def walk_bv_lshl(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_SHL, args[0], args[1])

    def walk_bv_lshr(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_LSHR, args[0], args[1])

    def walk_bv_rol(self, formula, args, **kwargs):
        ext = self.mkConst(self.Kind.BitVectorRotateLeft(formula.bv_rotation_step()))
        return self.mkTerm(self.Kind.BITVECTOR_ROTATE_LEFT, ext, args[0])

    def walk_bv_ror(self, formula, args, **kwargs):
        ext = self.mkConst(self.Kind.BitVectorRotateRight(formula.bv_rotation_step()))
        return self.mkTerm(self.Kind.BITVECTOR_ROTATE_RIGHT, ext, args[0])

    def walk_bv_zext(self, formula, args, **kwargs):
        ext = self.mkConst(self.Kind.BitVectorZeroExtend(formula.bv_extend_step()))
        return self.mkTerm(self.Kind.BITVECTOR_ZERO_EXTEND, ext, args[0])

    def walk_bv_sext (self, formula, args, **kwargs):
        ext = self.mkConst(self.Kind.BitVectorSignExtend(formula.bv_extend_step()))
        return self.mkTerm(self.Kind.BITVECTOR_SIGN_EXTEND, ext, args[0])

    def walk_bv_slt(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_SLT, args[0], args[1])

    def walk_bv_sle(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_SLE, args[0], args[1])

    def walk_bv_comp(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_COMP, args[0], args[1])

    def walk_bv_sdiv(self, formula, args, **kwargs):
        # Force deterministic semantics of division by 0
        # If the denominator is bv0, then the result is:
        #   * ~0 (if the numerator is signed >= 0)
        #   * 1 (if the numerator is signed < 0)
        n,d = args
        # sign_expr : ( 0 s<= n ) ? ~0 : 1 )
        zero = self.mkConst(self.Kind.BitVector(formula.bv_width(),
                                           self.Kind.Integer("0")))
        notzero = self.mkTerm(self.Kind.BITVECTOR_NOT, zero)
        one = self.mkConst(self.Kind.BitVector(formula.bv_width(),
                                          self.Kind.Integer("1")))
        is_gt_zero = self.mkTerm(self.Kind.BITVECTOR_SLE, zero, n)
        sign_expr = self.mkTerm(self.Kind.ITE, is_gt_zero, notzero, one)
        base = self.mkTerm(self.Kind.BITVECTOR_SDIV, n, d)
        if d.isConst():
            v = d.getConstBitVector().getValue().toString()
            if v == "0":
                return sign_expr
            else:
                return base
        else:
            # (d == 0) ? sign_expr : base
            is_zero = self.mkTerm(self.Kind.EQUAL, d, zero)
            return self.mkTerm(self.Kind.ITE, is_zero, sign_expr, base)

    def walk_bv_srem(self, formula, args, **kwargs):
        # Force deterministic semantics of reminder by 0
        # If the denominator is bv0, then the result is the numerator
        n,d = args
        if d.isConst():
            v = d.getConstBitVector().getValue().toString()
            if v == "0":
                return n
            else:
                return self.mkTerm(self.Kind.BITVECTOR_SREM, n, d)
        else:
            # (d == 0) ? n : n bvurem d
            base = self.mkTerm(self.Kind.BITVECTOR_SREM, n, d)
            zero = self.mkConst(self.Kind.BitVector(formula.bv_width(),
                                               self.Kind.Integer("0")))
            test = self.mkTerm(self.Kind.EQUAL, d, zero)
            return self.mkTerm(self.Kind.ITE, test, n, base)

    def walk_bv_ashr(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.BITVECTOR_ASHR, args[0], args[1])

    def walk_str_constant(self, formula, args, **kwargs):
        return self.mkConst(self.Kind.self.KindString(formula.constant_value()))

    def walk_str_length (self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.STRING_LENGTH , args[0])

    def walk_str_concat(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.STRING_CONCAT, args)

    def walk_str_contains(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.STRING_STRCTN, args[0], args[1])

    def walk_str_indexof(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.STRING_STRIDOF, args[0], args[1], args[2])

    def walk_str_replace(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.STRING_STRREPL, args[0], args[1], args[2])

    def walk_str_substr(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.STRING_SUBSTR, args[0], args[1], args[2])

    def walk_str_prefixof(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.STRING_PREFIX, args[0], args[1])

    def walk_str_suffixof(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.STRING_SUFFIX, args[0], args[1])

    def walk_str_to_int(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.STRING_STOI, args[0])

    def walk_int_to_str(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.STRING_ITOS, args[0])

    def walk_str_charat(self, formula, args, **kwargs):
        return self.mkTerm(self.Kind.STRING_CHARAT, args[0], args[1])

    def _type_to_cvc5(self, tp):
        if tp.is_bool_type():
            return self.boolType
        elif tp.is_real_type():
            return self.realType
        elif tp.is_int_type():
            return self.intType
        elif tp.is_function_type():
            stps = [self._type_to_cvc5(x) for x in tp.param_types]
            rtp = self._type_to_cvc5(tp.return_type)
            return self.mkFunctionSort(stps, rtp)
        elif tp.is_array_type():
            # Recursively convert the types of index and elem
            idx_cvc_type = self._type_to_cvc5(tp.index_type)
            elem_cvc_type = self._type_to_cvc5(tp.elem_type)
            return self.mkArrayType(idx_cvc_type, elem_cvc_type)
        elif tp.is_bv_type():
            return self.mkBitVectorType(tp.width)
        elif tp.is_string_type():
            return self.stringType
        elif tp.is_custom_type():
            return self.mkSort(str(tp))
        else:
            raise NotImplementedError("Unsupported type: %s" %tp)

    def _cvc5_type_to_type(self, type_):
        if type_.isBoolean():
            return types.BOOL
        elif type_.isInteger():
            return types.INT
        elif type_.isReal():
            return types.REAL
        elif type_.isArray():
            # Casting Type into ArrayType
            type_ = self.Kind.ArrayType(type_)
            # Recursively convert the types of index and elem
            idx_type = self._self.Kind_type_to_type(type_.getIndexType())
            elem_type = self._self.Kind_type_to_type(type_.getConstituentType())
            return types.ArrayType(idx_type, elem_type)
        elif type_.isBitVector():
            # Casting Type into BitVectorType
            type_ = self.Kind.BitVectorType(type_)
            return types.BVType(type_.getSize())
        elif type_.isFunction():
            # Casting Type into FunctionType
            type_ = self.Kind.FunctionType(type_)
            return_type = type_.getRangeType()
            param_types = tuple(self._self.Kind_type_to_type(ty) for ty in type_.getArgTypes())
            return types.FunctionType(return_type, param_types)
        else:
            raise NotImplementedError("Unsupported type: %s" % type_)

    def _rename_bound_variables(self, formula, variables):
        """Bounds the variables in formula.

        Returns a tuple (new_formula, new_var_list) in which the old
        variables have been replaced by the new variables in the list.
        """
        new_var_list = [self.mkVar(self._type_to_cvc5(x.symbol_type()), x.symbol_name()) \
                        for x in variables]
        old_var_list = [self.walk_symbol(x, []) for x in variables]
        new_formula = formula.substitute(old_var_list, new_var_list)
        return (new_formula, new_var_list)
