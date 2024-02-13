statement = """
; Declare the variables for the numbers and the letter
(declare-fun num1 () Int)
(assert (>= num1 0))
(assert (= 1 (mod num1 2)))
(check-sat)
(get-value (num1))
"""

topic = "mod_func"

import json
### read json file
with open("test_cases.json", "w") as f:
    cases = json.load(f)
idx = len(cases)
cases[f"test_idx_{idx}"] = {'topic': topic, 'statement': statement}
with open("test_cases.json", "w") as f:
    json.dump(cases, f, indent=2)
     
    

