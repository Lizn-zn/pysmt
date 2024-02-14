statement = """
; Declare the variables for the height, radius, and the angle of the staircase
(declare-fun height () Real)
(declare-fun radius () Real)
(declare-fun angle () Real)

; Declare the variable for the length of the handrail
(declare-fun length () Real)

; Assign the given values
(assert (= height 10.0))
(assert (= radius 3.0))

; The angle is given in degrees, convert it to radians as trigonometric functions in SMT-LIB use radians
; 270 degrees = 270 * pi / 180 radians
(assert (= angle (* (/ 270.0 180.0) PI)))

; Use the formula for the length of a spiral (helix): sqrt((2*pi*r)^2 + h^2)
(assert (= length (sqrt (+ (pow (* 2 PI radius) 2) (pow height 2)))))

(check-sat)
(get-value (length))
"""

topic = "PI"

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
     
    

