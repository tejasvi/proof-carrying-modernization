"""Surface IR of ACCTINT2.cob: ACCTINT with
   COMPUTE WS-DAILY-RATE ROUNDED = ACCT-RATE / 365
replaced by
   DIVIDE ACCT-RATE BY 365 GIVING WS-DAILY-RATE ROUNDED
(the extractor's `divide` node, as in Cobol/Frontend/Surface.lean)."""
import json, sys
src, dst = sys.argv[1], sys.argv[2]
d = json.load(open(src))
para = d["paras"][1]
assert para["name"] == "1000-CALC"
sent = para["sentences"][2]
assert list(sent[0].keys()) == ["compute"]
c = sent[0]["compute"]
div = c["e"]["div"]
para["sentences"][2] = [{"divide": {"dividend": div["a"], "divisor": div["b"], "rcv": c["rcv"],
                                     "giving": True, "remainder": None, "onSize": None,
                                     "notOnSize": []}}]
d["name"] = "ACCTINT2"
json.dump(d, open(dst, "w"), indent=1)
print(dst)
