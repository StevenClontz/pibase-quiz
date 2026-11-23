# Data built by scripts/pibase.py from the pi-Base bundle.
import json

class Generator(BaseGenerator):
    def data(self):
        with open("outcomes/PB1/data.json") as f:
            pool = json.load(f)["pool"]
        item = choice(pool)
        properties = list(item["properties"])
        shuffle(properties)
        properties[-1]["last"] = True
        return {
            "properties": properties,
            "search_query": item["search_query"],
            "examples": item["examples"],
        }
