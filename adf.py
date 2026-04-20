# Source - https://stackoverflow.com/a/76044320
# Posted by Pedro Piter
# Retrieved 2026-04-09, License - CC BY-SA 4.0

import json

with open("pracav3.ipynb") as pynb:
    try:
        report = json.load(pynb)
    except Exception as e:
        print(str(e))
