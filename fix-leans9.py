p = "minimal/lean_worker_caller_combined.lean"
s = open(p).read()

lines = s.split("\n")
# Remove the find_unknown_callers theorem
out = []
skip = False
for i, ln in enumerate(lines):
    if "theorem find_unknown_callers :" in ln:
        skip = True
        # skip until the next "end LeanWorkerCaller" or "theorem" or blank
        continue
    if skip:
        if ln.strip().startswith("end LeanWorkerCaller"):
            skip = False
        continue
    out.append(ln)
s = "\n".join(out)

# Remove the trailing combined entry point (we don't need it to prove theorems)
# Keep it but it's fine to include. Actually, just remove the `def leanWorker_allVerified` block.
lines = s.split("\n")
out = []
skip = False
for i, ln in enumerate(lines):
    if ln.strip().startswith("/-- The full verified lean-worker caller model"):
        skip = True
        continue
    if skip:
        if ln.strip() == "":
            # keep one blank line then stop
            skip = False
            continue
        continue
    out.append(ln)
s = "\n".join(out)

open(p, "w").write(s)
print("done")
