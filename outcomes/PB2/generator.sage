# Data built by scripts/pibase.py from the pi-Base bundle.
import json

def must(literal):
    return ("be " if literal["value"] else "not be ") + literal["name"]

class Generator(BaseGenerator):
    def data(self):
        with open("outcomes/PB2/data.json") as f:
            pool = json.load(f)["pool"]
        item = choice(pool)
        givens = list(item["givens"])
        shuffle(givens)
        return {
            "space": item["space"],
            "givens": givens,
            "target": item["target"],
            "target_must": must(item["target"]),
            "steps": item["steps"],
            "theorem_count": len(item["theorems"]),
            "proof_url": item["proof_url"],
        }
