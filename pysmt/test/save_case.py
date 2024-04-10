statement = """
(declare-const lower_bound Real)
(declare-const upper_bound Real)
(declare-const int_count Int)

; Define the lower and upper bounds
(assert (= lower_bound (sqrt 5)))
(assert (= upper_bound (sqrt 50)))

; The number of integers between two real numbers is the difference between the floor of the upper bound and the ceiling of the lower bound, plus one
(assert (= int_count (+ (- (to_int upper_bound) (to_int (ceil lower_bound))) 1)))

(check-sat)
(get-value (int_count))
"""

topic = "TOINT"

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
     
    

