# Data built by scripts/pibase.py from the pi-Base bundle.
import json

def must(literal):
    return ("be " if literal["value"] else "not be ") + literal["name"]

def negation(literal):
    return literal["name"] if not literal["value"] else "not " + literal["name"]

class Generator(BaseGenerator):
    def data(self):
        with open("outcomes/PB3/data.json") as f:
            pool = json.load(f)["pool"]
        item = choice(pool)
        hypotheses = list(item["hypotheses"])
        shuffle(hypotheses)
        return {
            "hypotheses": hypotheses,
            "conclusion": item["conclusion"],
            "conclusion_must": must(item["conclusion"]),
            "negated_conclusion": negation(item["conclusion"]),
            "search_query": item["search_query"],
            "derived_steps": item["steps"][:-1],
            "final_step": item["steps"][-1],
            "theorem_count": len(item["theorems"]),
        }
