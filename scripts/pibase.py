"""
Build question pools for the pi-Base outcomes (PB1, PB2, PB3).

Usage:
    python3 scripts/pibase.py [path/to/bundle.json]

Without an argument the current pi-Base bundle is downloaded. The script
writes outcomes/PB1/data.json, outcomes/PB2/data.json and
outcomes/PB3/data.json, which the outcome generators sample from.

The Prover below is a faithful port of pi-Base's own deduction engine
(github.com/pi-base/web, packages/core/src/Logic/{Prover,Queue,Derivations}.ts)
so that the theorems and "given" properties in each proof match what
students see on https://topology.pi-base.org.
"""

import itertools
import json
import os
import random
import re
import sys
import urllib.request
from html import escape

BUNDLE_URL = "https://pi-base-bundles.s3.us-east-2.amazonaws.com/refs/heads/main.json"
SITE = "https://topology.pi-base.org"
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Properties a typical first course in topology covers. Edit freely.
PROPERTY_ALLOWLIST = [
    "P000001",  # T0
    "P000002",  # T1
    "P000003",  # T2
    "P000004",  # T2.5
    "P000005",  # T3
    "P000006",  # T3.5
    "P000007",  # T4
    "P000008",  # T5
    "P000011",  # Regular
    "P000012",  # Completely regular
    "P000013",  # Normal
    "P000016",  # Compact
    "P000017",  # sigma-compact
    "P000018",  # Lindelof
    "P000019",  # Countably compact
    "P000020",  # Sequentially compact
    "P000021",  # Limit point compact
    "P000026",  # Separable
    "P000027",  # Second countable
    "P000028",  # First countable
    "P000030",  # Paracompact
    "P000036",  # Connected
    "P000037",  # Path connected
    "P000041",  # Locally connected
    "P000042",  # Locally path connected
    "P000047",  # Totally disconnected
    "P000050",  # Zero dimensional
    "P000052",  # Discrete
    "P000053",  # Metrizable
    "P000055",  # Completely metrizable
    "P000057",  # Countable
    "P000078",  # Finite
    "P000095",  # Arc connected
    "P000129",  # Indiscrete
    "P000130",  # Locally compact
]

# Further standard properties that may appear inside a proof (in an
# intermediate step) but are not used in question statements. Every theorem
# cited in a PB2/PB3 proof must only mention properties from these two lists.
PROOF_ALLOWLIST = PROPERTY_ALLOWLIST + [
    "P000009",  # Functionally Hausdorff
    "P000014",  # Completely normal
    "P000015",  # Perfectly normal
    "P000023",  # Weakly locally compact
    "P000024",  # Locally relatively compact
    "P000025",  # Exhaustible by compacts
    "P000032",  # Countably paracompact
    "P000046",  # Totally path disconnected
    "P000048",  # Totally separated
    "P000051",  # Scattered
    "P000067",  # T6
    "P000079",  # Sequential
    "P000080",  # Frechet Urysohn
    "P000084",  # Locally Hausdorff
    "P000094",  # Locally finite
    "P000125",  # Has multiple points
    "P000131",  # Hereditarily Lindelof
    "P000134",  # R1
    "P000135",  # R0
    "P000139",  # Has an isolated point
]


# ---------------------------------------------------------------- formulas

def props_of(f):
    if f["kind"] == "atom":
        return [f["property"]]
    out = []
    for s in f["subs"]:
        for p in props_of(s):
            if p not in out:
                out.append(p)
    return out


def evaluate(f, traits):
    if f["kind"] == "atom":
        if f["property"] not in traits:
            return None
        return traits[f["property"]] == f["value"]
    vals = [evaluate(s, traits) for s in f["subs"]]
    if f["kind"] == "and":
        if any(v is False for v in vals):
            return False
        if all(v is True for v in vals):
            return True
        return None
    # or
    if any(v is True for v in vals):
        return True
    if all(v is False for v in vals):
        return False
    return None


def negate(f):
    if f["kind"] == "atom":
        return {"kind": "atom", "property": f["property"], "value": not f["value"]}
    kind = "or" if f["kind"] == "and" else "and"
    return {"kind": kind, "subs": [negate(s) for s in f["subs"]]}


# ------------------------------------------------------------------ prover

class Prover:
    """Port of pi-Base's Prover/Queue/Derivations."""

    def __init__(self, index, traits):
        self.index = index
        self.traits = dict(traits)
        self.given = set(traits)
        self.evidence = {}
        # JS Set semantics: insertion ordered, re-adding is a no-op
        self.queue = dict.fromkeys(range(len(index.all)))
        for p in traits:
            self.mark(p)

    def mark(self, p):
        for i in index_with(self.index, p):
            self.queue.setdefault(i)

    def run(self):
        while self.queue:
            i = next(iter(self.queue))
            del self.queue[i]
            c = self.apply(self.index.all[i])
            if c is not None:
                return c
        return None

    def apply(self, t):
        a, c = t["when"], t["then"]
        av, cv = evaluate(a, self.traits), evaluate(c, self.traits)
        if av is True and cv is False:
            return self.expand(t["uid"], props_of(a) + props_of(c))
        if av is True:
            return self.force(t["uid"], c, props_of(a))
        if cv is False:
            return self.force(t["uid"], negate(a), props_of(c))
        return None

    def force(self, tid, f, support):
        if f["kind"] == "atom":
            p = f["property"]
            if p in self.traits:
                if self.traits[p] != f["value"]:
                    return self.expand(tid, support + [p])
                return None
            self.traits[p] = f["value"]
            self.evidence[p] = (tid, list(support))
            self.mark(p)
            return None
        if f["kind"] == "and":
            for s in f["subs"]:
                c = self.force(tid, s, support)
                if c is not None:
                    return c
            return None
        # or
        falses, unknown = [], None
        for s in f["subs"]:
            v = evaluate(s, self.traits)
            if v is True:
                return None
            if v is False:
                falses.append(s)
            elif unknown is not None:
                return None
            else:
                unknown = s
        false_props = [p for s in falses for p in props_of(s)]
        if len(falses) == len(f["subs"]):
            return self.expand(tid, support + false_props)
        if unknown is not None:
            return self.force(tid, unknown, support + false_props)
        return None

    def expand(self, tid, properties):
        by_prop = {}  # insertion ordered like JS Map
        assumptions = {}
        expanded = set()
        queue = list(properties)
        while queue:
            p = queue.pop(0)
            if p in expanded:
                continue
            if p in self.given:
                assumptions[p] = True
                expanded.add(p)
            elif p in self.evidence:
                ev = self.evidence[p]
                by_prop[p] = ev[0]
                queue += ev[1]
                expanded.add(p)
        theorems = list(reversed([tid] + list(by_prop.values())))
        # Not part of pi-Base: the derived properties in an order where each
        # step only depends on givens and earlier steps (for answer keys).
        steps, done = [], set(self.given)

        def visit(p):
            if p in done:
                return
            done.add(p)
            for q in self.evidence[p][1]:
                visit(q)
            steps.append((p, self.traits[p], self.evidence[p][0]))

        for p in properties:
            if p in self.evidence:
                visit(p)
        return {"theorems": theorems, "properties": list(assumptions), "steps": steps}

    def proof(self, p):
        if p in self.given:
            return "given"
        if p not in self.evidence:
            return None
        return self.expand(*self.evidence[p])


class Index:
    def __init__(self, theorems):
        self.all = theorems
        self.by_prop = {}
        for i, t in enumerate(theorems):
            for p in props_of(t["when"]) + props_of(t["then"]):
                self.by_prop.setdefault(p, {})[i] = True


def index_with(index, p):
    return index.by_prop.get(p, {})


def prove(index, traits):
    """Returns ('contradiction', proof) or ('ok', prover)."""
    pr = Prover(index, traits)
    c = pr.run()
    if c is not None:
        return "contradiction", c
    return "ok", pr


# -------------------------------------------------------------- rendering

def math_to_spatext(s):
    """Escape for XML and turn $...$ into <m>...</m>."""
    parts = re.split(r"(\$[^$]*\$)", s)
    out = ""
    for part in parts:
        if part.startswith("$") and part.endswith("$") and len(part) > 1:
            out += "<m>" + escape(part[1:-1], quote=False) + "</m>"
        else:
            out += escape(part, quote=False)
    return out


class Data:
    def __init__(self, bundle):
        self.bundle = bundle
        self.P = {p["uid"]: p for p in bundle["properties"]}
        self.S = {s["uid"]: s for s in bundle["spaces"]}
        self.T = {t["uid"]: t for t in bundle["theorems"]}
        self.index = Index(bundle["theorems"])
        self.asserted = {}
        for tr in bundle["traits"]:
            self.asserted.setdefault(tr["space"], {})[tr["property"]] = tr["value"]

    def name(self, p):
        return math_to_spatext(self.P[p]["name"])

    def search_term(self, p):
        prop = self.P[p]
        if "$" not in prop["name"]:
            return prop["name"]
        aliases = [a for a in prop.get("aliases", []) if "$" not in a]
        for a in aliases:
            if re.fullmatch(r"T\d(\.\d)?", a):
                return a
        if aliases:
            return aliases[0]
        return re.sub(r"[$\\{}]", "", prop["name"])

    def predicate(self, p, v):
        """'is X' / 'is not X', or 'has X' / 'does not have X' for 'Has X' properties."""
        raw = self.P[p]["name"]
        if raw.startswith("Has "):
            rest = math_to_spatext(raw[4:])
            return ("has " if v else "does not have ") + rest
        return ("is " if v else "is not ") + self.name(p)

    def literal(self, p, v):
        """Spatext rendering of a property literal."""
        return {
            "uid": p,
            "value": v,
            "name": self.name(p),
            "phrase": self.name(p) if v else "not " + self.name(p),
            "url": f"{SITE}/properties/{p}",
        }

    def formula_text(self, f):
        if f["kind"] == "atom":
            n = self.name(f["property"])
            return n if f["value"] else "not " + n
        joiner = " and " if f["kind"] == "and" else " or "
        return joiner.join(self.formula_text(s) for s in f["subs"])

    def theorem(self, tid):
        t = self.T[tid]
        return {
            "uid": tid,
            "statement": f"{self.formula_text(t['when'])} <m>\\Rightarrow</m> {self.formula_text(t['then'])}",
            "url": f"{SITE}/theorems/{tid}",
        }

    def proof_ok(self, thms):
        allowed = set(PROOF_ALLOWLIST)
        for tid in thms:
            t = self.T[tid]
            if not set(props_of(t["when"]) + props_of(t["then"])) <= allowed:
                return False
        return True

    def steps(self, proof, final=None):
        """Ordered answer-key steps. final: text for a closing contradiction step."""
        out = []
        for p, v, tid in proof["steps"]:
            out.append({"theorem": self.theorem(tid), "conclusion": self.predicate(p, v)})
        if final is not None:
            out.append({"theorem": self.theorem(proof["theorems"][-1]), "conclusion": final})
        return out

    def search_query(self, lits):
        """A query to paste into pi-Base's space search (XML-escaped)."""
        q = " + ".join(("" if v else "not ") + self.search_term(p) for p, v in lits)
        return escape(q, quote=False)

    def space(self, s):
        return {
            "uid": s,
            "name": math_to_spatext(self.S[s]["name"]),
            "url": f"{SITE}/spaces/{s}",
        }

    def is_single_theorem(self, hyps, concl):
        """Is there a theorem whose hypotheses are a subset of hyps and that concludes concl
        (directly or by contrapositive with an atomic hypothesis)?"""
        hyp_set = set(hyps)
        for t in self.bundle["theorems"]:
            w, c = t["when"], t["then"]
            wl = [(a["property"], a["value"]) for a in (w["subs"] if w["kind"] == "and" else [w])]
            cl = [(a["property"], a["value"]) for a in (c["subs"] if c["kind"] == "and" else [c])]
            if concl in cl and set(wl) <= hyp_set:
                return True
            # contrapositive of A => B (atomic A): ~B => ~A
            if len(wl) == 1 and concl == (wl[0][0], not wl[0][1]):
                if any((p, not v) in hyp_set for p, v in cl):
                    return True
        return False


# ----------------------------------------------------------------- pools

def deduce_all_spaces(D):
    full, provers = {}, {}
    for s in D.S:
        kind, res = prove(D.index, D.asserted.get(s, {}))
        if kind == "contradiction":
            raise RuntimeError(f"pi-Base data is contradictory for {s}: {res}")
        full[s] = res.traits
        provers[s] = res
    return full, provers


def forced(D, lits):
    """Return dict of traits forced by lits, or None if contradictory."""
    kind, res = prove(D.index, dict(lits))
    return None if kind == "contradiction" else res.traits


def pb1_pool(D, full, rng, size=300):
    allowed = PROPERTY_ALLOWLIST
    literals = [(p, v) for p in allowed for v in (True, False)]
    pool, seen = [], set()
    for combo in itertools.combinations(literals, 3):
        props = [p for p, _ in combo]
        if len(set(props)) < 3 or all(v for _, v in combo):
            continue
        matches = [s for s in D.S if all(full[s].get(p) == v for p, v in combo)]
        if not 1 <= len(matches) <= 8:
            continue
        # no literal follows from the other two
        redundant = False
        for i in range(3):
            others = [combo[j] for j in range(3) if j != i]
            f = forced(D, others)
            if f is None or combo[i][0] in f:
                redundant = True
                break
        if redundant:
            continue
        key = frozenset(combo)
        if key in seen:
            continue
        seen.add(key)
        pool.append({
            "properties": [D.literal(p, v) for p, v in combo],
            "search_query": D.search_query(combo),
            "examples": [D.space(s) for s in matches],
        })
    rng.shuffle(pool)
    return pool[:size]


def pb2_pool(D, full, provers, rng, min_thms=5, max_thms=8, per_target=20):
    allowed = set(PROPERTY_ALLOWLIST)
    pool = []
    for s in D.S:
        pr = provers[s]
        for p, v in pr.traits.items():
            if p not in allowed:
                continue
            proof = pr.proof(p)
            if proof in (None, "given"):
                continue
            thms = proof["theorems"]
            givens = proof["properties"]
            if not (min_thms <= len(set(thms)) <= max_thms):
                continue
            if not 2 <= len(givens) <= 4:
                continue
            if not set(givens) <= allowed or not D.proof_ok(thms):
                continue
            pool.append({
                "space": D.space(s),
                "givens": [D.literal(g, pr.traits[g]) for g in givens],
                "target": D.literal(p, v),
                "theorems": [D.theorem(t) for t in thms],
                "steps": D.steps(proof, final=D.predicate(p, v)),
                "proof_url": f"{SITE}/spaces/{s}/properties/{p}",
            })
    rng.shuffle(pool)
    by_target = {}
    for item in pool:
        by_target.setdefault(item["target"]["uid"], []).append(item)
    return [item for items in by_target.values() for item in items[:per_target]]


def pb3_pool(D, full, rng, size=300, tries=400_000, max_thms=8):
    allowed = PROPERTY_ALLOWLIST
    literals = [(p, v) for p in allowed for v in (True, False)]
    pool, seen = [], set()
    for _ in range(tries):
        if len(pool) >= size:
            break
        hyps = rng.sample(literals, 3)
        if len({p for p, _ in hyps}) < 3:
            continue
        if not any(all(full[s].get(p) == v for p, v in hyps) for s in D.S):
            continue  # want a non-vacuous theorem
        f3 = forced(D, hyps)
        if f3 is None:
            continue
        # every hypothesis independent of the other two
        pair_forced = []
        ok = True
        for i in range(3):
            others = [hyps[j] for j in range(3) if j != i]
            f2 = forced(D, others)
            if f2 is None or hyps[i][0] in f2:
                ok = False
                break
            pair_forced.append(f2)
        if not ok:
            continue
        hyp_props = {p for p, _ in hyps}
        candidates = [
            (p, v) for p, v in f3.items()
            if p in allowed and p not in hyp_props
            and all(p not in f2 for f2 in pair_forced)
            and not D.is_single_theorem(hyps, (p, v))
        ]
        rng.shuffle(candidates)
        for concl in candidates:
            key = (frozenset(hyps), concl)
            if key in seen:
                continue
            kind, contra = prove(D.index, dict(hyps + [(concl[0], not concl[1])]))
            if kind != "contradiction":
                continue
            if not 2 <= len(set(contra["theorems"])) <= max_thms:
                continue
            if not D.proof_ok(contra["theorems"]):
                continue
            seen.add(key)
            pool.append({
                "hypotheses": [D.literal(p, v) for p, v in hyps],
                "conclusion": D.literal(*concl),
                "search_query": D.search_query(hyps + [(concl[0], not concl[1])]),
                "theorems": [D.theorem(t) for t in contra["theorems"]],
                "steps": D.steps(contra, final="a contradiction"),
            })
            break
    return pool


def write(slug, sha, pool):
    path = os.path.join(ROOT, "outcomes", slug, "data.json")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        json.dump({"pi_base_sha": sha, "pool": pool}, f, indent=1, ensure_ascii=False)
    print(f"{slug}: {len(pool)} items -> {os.path.relpath(path, ROOT)}")


def main():
    if len(sys.argv) > 1:
        with open(sys.argv[1]) as f:
            bundle = json.load(f)
    else:
        with urllib.request.urlopen(BUNDLE_URL) as r:
            bundle = json.load(r)
    sha = bundle["version"]["sha"]
    D = Data(bundle)
    missing = [p for p in PROPERTY_ALLOWLIST if p not in D.P]
    if missing:
        raise RuntimeError(f"allowlisted properties missing from bundle: {missing}")
    full, provers = deduce_all_spaces(D)
    rng = random.Random(20261123)
    write("PB1", sha, pb1_pool(D, full, rng))
    write("PB2", sha, pb2_pool(D, full, provers, rng))
    write("PB3", sha, pb3_pool(D, full, rng))


if __name__ == "__main__":
    main()
