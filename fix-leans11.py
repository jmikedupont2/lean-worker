p = "minimal/lean_worker_caller_combined.lean"
lines = open(p).read().split("\n")

out = []
i = 0
while i < len(lines):
    ln = lines[i]
    if "theorem find_lean_worker_callers :" in ln:
        out.append(ln)
        i += 1
        out.append("    findCallersByRepo 'lean-worker' = callerRegistry := by")
        out.append("  apply le_antisymm")
        out.append("  · apply le_antisymm")
        out.append("    · apply List.filter_sublist")
        out.append('    · intro c hc')
        out.append('    simp [findCallersByRepo] at hc')
        out.append("    rcases hc with (cfl, hc)")
        out.append('    simp at hcfl')
        out.append('    subst hcfl')
        out.append("    simp at hc")
        out.append("    rcases hc with (rfl)")
        out.append('    intro h')
        out.append('    simp at h')
        out.append('    injection h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13')
        out.append("    subst c")
        out.append("    · subst h4; trivial")
        out.append("    · subst h9; trivial")
        out.append("    · subst h11; trivial")
        out.append("    · subst h3; trivial")
        out.append("    · subst h7; trivial")
        out.append("    · subst h5; trivial")
        out.append("    · subst h12; trivial")
        out.append("    · subst h6; trivial")
        out.append("    · subst h8; trivial")
        out.append("    · subst h2; trivial")
        out.append("    · subst h10; trivial")
        out.append("    · subst h13; trivial")
        out.append("  · apply List.length_le_sub_polymorphic")
        out.append("    apply List.length_le_of_sublist")
        out.append("    intro c hc")
        out.append("    simp [findCallersByRepo] at hc")
        out.append("    rcases hc with (cfl, hc)")
        out.append('    simp at hcfl')
        out.append('    subst hcfl')
        out.append("    simp at hc")
        out.append("    rcases hc with (rfl)")
        out.append("    exact callerRegistry.mem")
        i += 1
        continue
    out.append(ln)
    i += 1

open(p, "w").write("\n".join(out))
print("done")
