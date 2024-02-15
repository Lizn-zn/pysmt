statement = """
(declare-fun factorial (Int) Int)

; Declare a function to compute the GCD (non-executable placeholder)
(declare-fun gcd (Int Int) Int)

; Define the sequence a_n = n! + n
(define-fun a_n ((n Int)) Int (+ (factorial n) n))

; We want to find the maximum possible value of the GCD of two consecutive terms a_n and a_(n+1)
(declare-fun n () Int)
(declare-fun max_gcd () Int)

; The constraints that n must be a non-negative integer
(assert (>= n 0))

; The GCD of two consecutive terms
(assert (= max_gcd (gcd (a_n n) (a_n (+ n 1)))))

; We want to maximize the GCD value
(maximize max_gcd)

(check-sat)
(get-value (max_gcd))
"""

topic = "FACTORIAL-MAXIMUM-GCD"

import json
### read json file
try:
    with open("test_cases.json", "r") as f:
        cases = json.load(f)
except (FileNotFoundError, json.JSONDecodeError):
    cases = {}
idx = len(cases)
cases[f"test_idx_{idx}"] = {'topic': topic, 'statement': statement}
with open("test_cases.json", "w") as f:
    json.dump(cases, f, indent=2)
     
    

