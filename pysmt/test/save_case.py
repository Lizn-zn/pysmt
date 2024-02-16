statement = """
(declare-fun A () Int)

(assert (< A 0))
(assert (= (abs A) 100))

(check-sat)
(get-value (A))
"""

topic = "ABS"

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
     
    

