statement = """
(declare-fun n () Int)
(declare-fun sum1 () Int)
(declare-fun sum2 () Int)
(declare-fun perfect_square () Int)

; Constraints
(assert (<= n 2008))
(assert (>= n 1))

; Define the sums of squares
(define-fun-rec sum_squares ((i Int) (j Int)) Int
  (ite (<= i j)
    (+ (* i i) (sum_squares (+ i 1) j))
    1))
    
(assert (= sum1 (sum_squares 1 10)))
(assert (> sum1 10))
    
(check-sat)
(get-model)
"""

topic = "DEFINE-FUN-REC"

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
     
    

