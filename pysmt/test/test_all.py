import sys
sys.path.insert(0, '/home/argustest/pysmt')
from pysmt.smtlib.parser import SmtLibParser, SmtLibScript
from io import StringIO
from pysmt.shortcuts import Solver, Optimizer, REAL, INT, get_env
import json

def pysmt_solver(statement, solver_name):
    smt_parser = SmtLibParser()
    smt_parser.env.enable_div_by_0 = False
    try:
        script = smt_parser.get_script(StringIO(statement))  
    except ZeroDivisionError as e:
        return False, "zero division error"
    Opt = Optimizer if any(cmd.name in ["maximize", "minimize"] for cmd in script) else Solver
    with Opt(name=solver_name) as opt:
        logs = script.evaluate(opt)
    return logs

def test_solver(statement, solver_name):
    """尝试使用指定的求解器解决问题并返回结果。"""
    try:
        pysmt_solver(statement, solver_name=solver_name)
        return True
    except Exception as e:
        print(f"\n{solver_name} failed with error: {e}")
        return False

with open("test_cases.json", "r") as file:
    test_cases = json.load(file)

for idx, case in test_cases.items():
    print(f"Testing case {idx} with topic '{case['topic']}'...", end=' ')

    solvers = ['z3', 'cvc4', 'msat']
    all_passed = True

    for solver in solvers:
        if not test_solver(case['statement'], solver):
            all_passed = False
            break  

    # 输出测试结果
    if all_passed:
        print("all passed")