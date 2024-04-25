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
from io import StringIO

import pysmt.operators as op
from pysmt.walkers import TreeWalker
from pysmt.walkers.generic import handles
from pysmt.utils import quote
from pysmt.constants import is_pysmt_fraction, is_pysmt_integer


class HRPrinter(TreeWalker):
    """Performs serialization of a formula in a human-readable way.

    E.g., Implies(And(Symbol(x), Symbol(y)), Symbol(z))  ~>   '(x * y) -> z'
    """

    def __init__(self, stream, env=None):
        TreeWalker.__init__(self, env=env)
        self.stream = stream
        self.write = self.stream.write

    def printer(self, f, threshold=None):
        """Performs the serialization of 'f'.

        Thresholding can be used to define how deep in the formula to
        go. After reaching the thresholded value, "..." will be
        printed instead. This is mainly used for debugging.
        """
        self.walk(f, threshold=threshold)

    def walk_threshold(self, formula):
        self.write("...")

    def walk_nary(self, formula, ops):
        self.write("(")
        args = formula.args()
        for s in args[:-1]:
            yield s
            self.write(ops)
        yield args[-1]
        self.write(")")
    
    def walk_term(self, formula, ops):
        """ Note: add bracket for fraction to differentiate (a/b)^k & a/b^k """
        self.write("(")
        args = formula.args()
        for s in args[:-1]:
            if s.is_constant() and is_pysmt_fraction(s.constant_value()):
                self.write("(")
                yield s
                self.write(")")
            else:
                yield s
            self.write(ops)
        s = args[-1]
        if s.is_constant() and is_pysmt_fraction(s.constant_value()):
            self.write("(")
            yield s
            self.write(")")
        else:
            yield s
        self.write(")")

    def walk_quantifier(self, op_symbol, var_sep, sep, formula):
        if len(formula.quantifier_vars()) > 0:
            self.write("(")
            self.write(op_symbol)
            for s in formula.quantifier_vars()[:-1]:
                yield s
                self.write(var_sep)
            yield formula.quantifier_vars()[-1]
            self.write(sep)
            yield formula.arg(0)
            self.write(")")
        else:
            yield formula.arg(0)
            
    def walk_symbol(self, formula):
        self.write(quote(formula.symbol_name(), style="'"))
        
    def walk_single_input_operator(self, formula, op_name):
        """ walk single input operator with single argument """
        self.write(op_name)
        self.write("(")
        yield formula.arg(0)
        self.write(")")
    
    def walk_multi_input_operator(self, formula, op_name):
        """ walk multi input operator with multiple arguments """
        self.write(op_name)
        self.write("(")
        for p in formula.args()[:-1]:
            yield p
            self.write(", ")
        yield formula.args()[-1]
        self.write(")")

    def walk_function(self, formula):
        """ walk function with multiple arguments """
        yield formula.function_name()
        self.write("(")
        for p in formula.args()[:-1]:
            yield p
            self.write(", ")
        yield formula.args()[-1]
        self.write(")")

    def real_to_str(self, number):
        n, d = number.numerator, number.denominator
        if d == 1:
            return "%s.0" % n
        else:
            return "%s/%s" % (n, d)

    def walk_real_constant(self, formula):
        assert is_pysmt_fraction(formula.constant_value()), \
            "The type was " + str(type(formula.constant_value()))
        # TODO: Remove this once issue 113 in gmpy2 is solved
        v = formula.constant_value()
        self.write(self.real_to_str(v))

    def walk_int_constant(self, formula):
        assert is_pysmt_integer(formula.constant_value()), \
            "The type was " + str(type(formula.constant_value()))
        self.write(str(formula.constant_value()))
        
    def walk_complex_constant(self, formula):
        real, image = formula.constant_value()
        real = real.constant_value()
        real_str = self.real_to_str(real)
        image = image.constant_value()
        if image == 0:
            self.write(real_str)
        elif image < 0:        
            image = -image
            image_str = self.real_to_str(image)
            self.write("(%s - %s*i)" %(real_str, image_str))
        else:
            image_str = self.real_to_str(image)
            self.write("(%s + %s*i)" %(real_str, image_str))

    def walk_complex_variable(self, formula):
        self.write("(")
        yield formula.arg(0)
        self.write(" + ")
        yield formula.arg(1)
        self.write("*i)")

    def walk_bool_constant(self, formula):
        if formula.constant_value():
            self.write("True")
        else:
            self.write("False")

    def walk_bv_constant(self, formula):
        # This is the simplest SMT-LIB way of printing the value of a BV
        # self.write("(_ bv%d %d)" % (formula.bv_width(),
        #                             formula.constant_value()))
        self.write("%d_%d" % (formula.constant_value(),
                              formula.bv_width()))

    def walk_algebraic_constant(self, formula):
        self.write(str(formula.constant_value()))

    def walk_bv_extract(self, formula):
        yield formula.arg(0)
        self.write("[%d:%d]" % (formula.bv_extract_start(),
                                       formula.bv_extract_end()))

    def walk_bv_neg(self, formula):
        self.write("(- ")
        yield formula.arg(0)
        self.write(")")

    def walk_bv_ror(self, formula):
        self.write("(")
        yield formula.arg(0)
        self.write(" ROR ")
        self.write("%d)" % formula.bv_rotation_step())

    def walk_bv_rol(self, formula):
        self.write("(")
        yield formula.arg(0)
        self.write(" ROL ")
        self.write("%d)" % formula.bv_rotation_step())

    def walk_bv_zext(self, formula):
        self.write("(")
        yield formula.arg(0)
        self.write(" ZEXT ")
        self.write("%d)" % formula.bv_extend_step())

    def walk_bv_sext(self, formula):
        self.write("(")
        yield formula.arg(0)
        self.write(" SEXT ")
        self.write("%d)" % formula.bv_extend_step())

    def walk_ite(self, formula):
        self.write("ITE(")
        yield formula.arg(0)
        self.write(", ")
        yield formula.arg(1)
        self.write(", ")
        yield formula.arg(2)
        self.write(")")
    
    def walk_numer_ite(self, formula):
        arg = formula.arg(0)
        cond = formula.arg(0).serialize()
        self.write("Piecewise(")
        self.write("(")
        yield formula.arg(1)
        self.write(", ")
        self.write(cond)
        self.write("), (")
        yield formula.arg(2)
        self.write(", ")
        self.write(f"Not({cond})")
        self.write(")")
        self.write(")")
            
    def walk_forall(self, formula):
        return self.walk_quantifier("forall ", ", ", " . ", formula)

    def walk_exists(self, formula):
        return self.walk_quantifier("exists ", ", ", " . ", formula)

    def walk_toreal(self, formula):
        # self.write("ToReal(")
        yield formula.arg(0)
        # self.write(")")

    def walk_realtoint(self, formula):
        # self.write("RealToInt(")
        yield formula.arg(0)
        # self.write(")")

    def walk_str_constant(self, formula):
        assert (type(formula.constant_value()) == str ), \
            "The type was " + str(type(formula.constant_value()))
        self.write('"%s"' % formula.constant_value().replace('"', '""'))

    def walk_str_length(self,formula):
        self.write("str.len(" )
        self.walk(formula.arg(0))
        self.write(")")

    def walk_str_charat(self,formula, **kwargs):
        self.write("str.at(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_concat(self,formula, **kwargs):
        self.write("str.++(" )
        for arg in formula.args()[:-1]:
            self.walk(arg)
            self.write(", ")
        self.walk(formula.args()[-1])
        self.write(")")

    def walk_str_contains(self,formula, **kwargs):
        self.write("str.contains(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_indexof(self,formula, **kwargs):
        self.write("str.indexof(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(", ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_replace(self,formula, **kwargs):
        self.write("str.replace(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(", ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_substr(self,formula, **kwargs):
        self.write("str.substr(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(", ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_str_prefixof(self,formula, **kwargs):
        self.write("str.prefixof(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_suffixof(self,formula, **kwargs):
        self.write("str.suffixof(" )
        self.walk(formula.arg(0))
        self.write(", ")
        self.walk(formula.arg(1))
        self.write(")")

    def walk_str_to_int(self,formula, **kwargs):
        self.write("str.to.int(" )
        self.walk(formula.arg(0))
        self.write(")")

    def walk_int_to_str(self,formula, **kwargs):
        self.write("int.to.str(" )
        self.walk(formula.arg(0))
        self.write(")")

    def walk_array_select(self, formula):
        yield formula.arg(0)
        self.write("[")
        yield formula.arg(1)
        self.write("]")

    def walk_array_store(self, formula):
        yield formula.arg(0)
        self.write("[")
        yield formula.arg(1)
        self.write(" := ")
        yield formula.arg(2)
        self.write("]")

    def walk_array_value(self, formula):
        self.write(str(self.env.stc.get_type(formula)))
        self.write("(")
        yield formula.array_value_default()
        self.write(")")
        assign = formula.array_value_assigned_values_map()
        # We sort the array value assigments in lexicographic order
        # for deterministic printing
        for k in sorted(assign, key=str):
            self.write("[")
            yield k
            self.write(" := ")
            yield assign[k]
            self.write("]")

    def walk_bv_tonatural(self, formula):
        self.write("bv2nat(")
        yield formula.arg(0)
        self.write(")")

    def walk_and(self, formula): return self.walk_nary(formula, " & ")
    def walk_or(self, formula): return self.walk_nary(formula, " | ")
    def walk_equals(self, formula): return self.walk_nary(formula, " == ")
    def walk_plus(self, formula): return self.walk_nary(formula, " + ")
    def walk_times(self, formula): return self.walk_nary(formula, " * ")
    def walk_div(self, formula): return self.walk_nary(formula, " / ")
    def walk_intdiv(self, formula): return self.walk_nary(formula, " // ")
    def walk_complex_plus(self, formula): return self.walk_nary(formula, " + ")
    def walk_complex_minus(self, formula): return self.walk_nary(formula, " - ")
    def walk_complex_times(self, formula): return self.walk_nary(formula, " * ")
    def walk_complex_div(self, formula): return self.walk_nary(formula, " / ")
    def walk_pow(self, formula): return self.walk_term(formula, " ^ ")
    def walk_mod(self, formula): return self.walk_nary(formula, " % ")
    def walk_iff(self, formula): return self.walk_nary(formula, " <-> ")
    def walk_implies(self, formula): return self.walk_nary(formula, " -> ")
    def walk_minus(self, formula): return self.walk_nary(formula, " - ")
    def walk_complex_equals(self, formula): return self.walk_nary(formula, " = ")
    def walk_le(self, formula): return self.walk_nary(formula, " <= ")
    def walk_lt(self, formula): return self.walk_nary(formula, " < ")
    def walk_bv_xor(self, formula): return self.walk_nary(formula, " xor ")
    def walk_bv_concat(self, formula): return self.walk_nary(formula, "::")
    def walk_bv_udiv(self, formula): return self.walk_nary(formula, " u/ ")
    def walk_bv_urem(self, formula): return self.walk_nary(formula, " u% ")
    def walk_bv_sdiv(self, formula): return self.walk_nary(formula, " s/ ")
    def walk_bv_srem(self, formula): return self.walk_nary(formula, " s% ")
    def walk_bv_sle(self, formula): return self.walk_nary(formula, " s<= ")
    def walk_bv_slt(self, formula): return self.walk_nary(formula, " s< ")
    def walk_bv_ule(self, formula): return self.walk_nary(formula, " u<= ")
    def walk_bv_ult(self, formula): return self.walk_nary(formula, " u< ")
    def walk_bv_lshl(self, formula): return self.walk_nary(formula, " << ")
    def walk_bv_lshr(self, formula): return self.walk_nary(formula, " >> ")
    def walk_bv_ashr(self, formula): return self.walk_nary(formula, " a>> ")
    def walk_bv_comp(self, formula): return self.walk_nary(formula, " bvcomp ")
    def walk_round(self, formula): return self.walk_single_input_operator(formula, 'round')
    def walk_abs(self, formula): return self.walk_single_input_operator(formula, 'abs')
    def walk_complex_abs(self, formula): return self.walk_single_input_operator(formula, 'abs')
    def walk_sqrt(self, formula): return self.walk_single_input_operator(formula, 'sqrt')
    def walk_prime(self, formula): return self.walk_single_input_operator(formula, "prime")
    def walk_even(self, formula): return self.walk_single_input_operator(formula, "even")
    def walk_exp(self, formula): return self.walk_single_input_operator(formula, "exp")
    def walk_sin(self, formula): return self.walk_single_input_operator(formula, "sin")
    def walk_cos(self, formula): return self.walk_single_input_operator(formula, "cos")
    def walk_tan(self, formula): return self.walk_single_input_operator(formula, "tan")
    def walk_asin(self, formula): return self.walk_single_input_operator(formula, "asin")
    def walk_acos(self, formula): return self.walk_single_input_operator(formula, "acos")
    def walk_atan(self, formula): return self.walk_single_input_operator(formula, "atan")
    def walk_acsc(self, formula): return self.walk_single_input_operator(formula, "acsc")
    def walk_asec(self, formula): return self.walk_single_input_operator(formula, "asec")
    def walk_acot(self, formula): return self.walk_single_input_operator(formula, "acot")
    def walk_factorial(self, formula): return self.walk_single_input_operator(formula, "factorial")
    def walk_log(self, formula): return self.walk_single_input_operator(formula, "log")
    def walk_gcd(self, formula): return self.walk_multi_input_operator(formula, "gcd")
    def walk_lcm(self, formula): return self.walk_multi_input_operator(formula, "lcm")
    def walk_binomial(self, formula): return self.walk_multi_input_operator(formula, "binomial")
    def walk_not(self, formula): return self.walk_single_input_operator(formula, "Not")
    def walk_pi(self, formula): self.write("pi")
    def walk_e(self, formula): self.write("e")
    walk_bv_and = walk_and
    walk_bv_or = walk_or
    walk_bv_not = walk_not
    walk_bv_add = walk_plus
    walk_bv_mul = walk_times
    walk_bv_sub = walk_minus

#EOC HRPrinter



class BottemaPrinter(TreeWalker):
    """Performs serialization of a formula in a human-readable way.

    E.g., Implies(And(Symbol(x), Symbol(y)), Symbol(z))  ~>   '(x * y) -> z'
    """

    def __init__(self, stream, env=None):
        TreeWalker.__init__(self, env=env)
        self.stream = stream
        self.write = self.stream.write

    def printer(self, f, threshold=None):
        """Performs the serialization of 'f'.

        Thresholding can be used to define how deep in the formula to
        go. After reaching the thresholded value, "..." will be
        printed instead. This is mainly used for debugging.
        """
        self.walk(f, threshold=threshold)

    def walk_threshold(self, formula):
        self.write("...")

    def walk_nary(self, formula, ops):
        self.write("(")
        args = formula.args()
        for s in args[:-1]:
            yield s
            self.write(ops)
        s = args[-1]
        yield s
        self.write(")")
    
    def walk_term(self, formula, ops):
        """ Note: add bracket for fraction """
        self.write("(")
        args = formula.args()
        for s in args[:-1]:
            if s.is_constant() and is_pysmt_fraction(s.constant_value()):
                self.write("(")
                yield s
                self.write(")")
            else:
                yield s
            self.write(ops)
        s = args[-1]
        if s.is_constant() and is_pysmt_fraction(s.constant_value()):
            self.write("(")
            yield s
            self.write(")")
        else:
            yield s
        self.write(")")
            
    def walk_not(self, formula):
        self.write("(! ")
        yield formula.arg(0)
        self.write(")")

    def walk_symbol(self, formula):
        self.write(quote(formula.symbol_name(), style="'"))
        
    def walk_single_input_operator(self, formula, op_name):
        """ walk single input operator with single argument """
        self.write(op_name)
        self.write("(")
        yield formula.arg(0)
        self.write(")")
    
    def walk_multi_input_operator(self, formula, op_name):
        """ walk multi input operator with multiple arguments """
        self.write(op_name)
        self.write("(")
        for p in formula.args()[:-1]:
            yield p
            self.write(", ")
        yield formula.args()[-1]
        self.write(")")

    def walk_function(self, formula):
        """ walk function with multiple arguments """
        yield formula.function_name()
        self.write("(")
        for p in formula.args()[:-1]:
            yield p
            self.write(", ")
        yield formula.args()[-1]
        self.write(")")

    def real_to_str(self, number):
        n, d = number.numerator, number.denominator
        if d == 1:
            return "%s" % n
        else:
            return "%s/%s" % (n, d)

    def walk_real_constant(self, formula):
        assert is_pysmt_fraction(formula.constant_value()), \
            "The type was " + str(type(formula.constant_value()))
        # TODO: Remove this once issue 113 in gmpy2 is solved            
        v = formula.constant_value()
        if v < 0: # add this for -1 => (-1)
            self.write(f"({self.real_to_str(v)})")
        else:
            self.write(self.real_to_str(v))

    def walk_int_constant(self, formula):
        assert is_pysmt_integer(formula.constant_value()), \
            "The type was " + str(type(formula.constant_value()))
        self.write(str(formula.constant_value()))
        
    def walk_complex_constant(self, formula):
        real, image = formula.constant_value()
        real = real.constant_value()
        real_str = self.real_to_str(real)
        image = image.constant_value()
        if image == 0:
            self.write(real_str)
        elif image < 0:        
            image = -image
            image_str = self.real_to_str(image)
            self.write("(%s - %s*i)" %(real_str, image_str))
        else:
            image_str = self.real_to_str(image)
            self.write("(%s + %s*i)" %(real_str, image_str))

    def walk_complex_variable(self, formula):
        self.write("(")
        yield formula.arg(0)
        self.write(" + ")
        yield formula.arg(1)
        self.write("*i)")

    def walk_bool_constant(self, formula):
        if formula.constant_value():
            self.write("True")
        else:
            self.write("False")

    def walk_algebraic_constant(self, formula):
        self.write(str(formula.constant_value()))

    def walk_toreal(self, formula):
        # self.write("ToReal(")
        yield formula.arg(0)
        # self.write(")")

    def walk_realtoint(self, formula):
        # self.write("RealToInt(")
        yield formula.arg(0)
        # self.write(")")

    def walk_and(self, formula): return self.walk_nary(formula, " , ")
    def walk_plus(self, formula): return self.walk_nary(formula, " + ")
    def walk_minus(self, formula): return self.walk_nary(formula, " - ")
    def walk_times(self, formula): return self.walk_nary(formula, " * ")
    def walk_div(self, formula): return self.walk_nary(formula, " / ")
    def walk_complex_plus(self, formula): return self.walk_nary(formula, " + ")
    def walk_complex_minus(self, formula): return self.walk_nary(formula, " - ")
    def walk_complex_times(self, formula): return self.walk_nary(formula, " * ")
    def walk_complex_div(self, formula): return self.walk_nary(formula, " / ")
    def walk_pow(self, formula): return self.walk_term(formula, " ^ ")
    def walk_equals(self, formula): return self.walk_nary(formula, " = ")
    def walk_complex_equals(self, formula): return self.walk_nary(formula, " = ")
    def walk_le(self, formula): return self.walk_nary(formula, " <= ")
    def walk_lt(self, formula): return self.walk_nary(formula, " < ")
    def walk_sqrt(self, formula): return self.walk_single_input_operator(formula, 'sqrt')
    def walk_pi(self, formula): self.write("pi")
    def walk_e(self, formula): self.write("e")

#EOC BottemaPrinter

class HRSerializer(object):
    """Return the serialized version of the formula as a string."""

    PrinterClass = HRPrinter

    def __init__(self, environment=None):
        self.environment = environment

    def serialize(self, formula, printer=None, threshold=None):
        """Returns a string with the human-readable version of the formula.

        'printer' is the printer to call to perform the serialization.
        'threshold' is the thresholding value for the printing function.
        """
        buf = StringIO()
        if printer is None:
            p = self.PrinterClass(buf)
        else:
            p = printer(buf)
        
        p.printer(formula, threshold)
        res = buf.getvalue()
        buf.close()
        return res


class SmartPrinter(HRPrinter):
    """Better serialization allowing special printing of subformula.

    The formula is serialized according to the format defined in the
    HRPrinter. However, every time a formula that is present in
    'subs' is found, this is replaced.

    E.g., subs  = {And(a,b): "ab"}

    Every time that the subformula And(a,b) is found, "ab" will be
    printed instead of "a & b". This makes it possible to rename big
    subformulae, and provide better human-readable representation.
    """

    def __init__(self, stream, subs=None):
        HRPrinter.__init__(self, stream)
        if subs is None:
            self.subs = {}
        else:
            self.subs = subs

    def printer(self, f, threshold=None):
        self.walk(f, threshold=threshold)

    @handles(op.ALL_TYPES)
    def smart_walk(self, formula):
        if formula in self.subs:
            # Smarties contains a string.
            # In the future, we could allow for arbitrary function calls
            self.write(self.subs[formula])
        else:
            return HRPrinter.super(self, formula)

# EOC SmartPrinter

def smart_serialize(formula, subs=None, threshold=None):
    """Creates and calls a SmartPrinter to perform smart serialization."""
    buf = StringIO()
    p = SmartPrinter(buf, subs=subs)
    p.printer(formula, threshold=threshold)
    res = buf.getvalue()
    buf.close()
    return res
