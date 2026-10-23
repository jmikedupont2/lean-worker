import RequestProject.Dasein15VM.Walk

/-!
# Cryptids, part 4: Conway's PRIMEGAME visits the Dasein15 VM

PRIMEGAME is Conway's 14-fraction FRACTRAN program which, started at `2`, passes through
`2^p` exactly for the primes `p`, in order. Every prime it uses (2, 3, 5, 7, 11, 13, 17, 19, 23,
29) is one of the 15 supersingular primes, so it runs inside the Dasein15 shape space.

* `primegame_pow2_iff`: for `k ≤ 710`, `k` steps from `2` reach a power of two `2^e` exactly for
  `(k, e) ∈ {(0,1), (19,2), (69,3), (281,5), (710,7)}` — the first four primes 2, 3, 5, 7 appear,
  in order, and nothing else is a power of two. The kernel replays the 710-step orbit
  (`primegame_orbit_pow2`); `pgPow2_sound` / `pgPow2_complete` connect the orbit list to
  `fractranRun`.
* `primegame_changes_mass`: PRIMEGAME's first step is `2 ↦ 15`, which takes total exponent mass
  1 to 2.
* `vm_step_conserves_mass`, `primegame_rejected`: any shape-dispatched VM (`VMSpec`) over the
  supersingular basis conserves mass along every step, so no VM step goes from `2` to `15`.
  PRIMEGAME is a FRACTRAN program that the Dasein15 VM's invariant gate cannot host.
-/

namespace Dasein15VM.Cryptids

open Dasein15 Dasein15VM

/-- Conway's PRIMEGAME. -/
def primegame : List ℚ :=
  [17/91, 78/85, 19/51, 23/38, 29/33, 77/29, 95/23, 77/19, 1/17, 11/13, 13/11, 15/2, 1/7, 55/1]

/-- The orbit of `c` under a FRACTRAN program, up to `k` steps (stops early on halting). -/
def orbit (prog : List ℚ) : ℕ → ℕ → List ℕ
  | 0, c => [c]
  | k + 1, c => c :: match fractranStep prog c with
    | some c' => orbit prog k c'
    | none => []

theorem orbit_spec (prog : List ℚ) :
    ∀ (k c i : ℕ) (h : i < (orbit prog k c).length),
      fractranRun prog i c = some ((orbit prog k c)[i])
  | 0, c, i, h => by
    simp only [orbit, List.length_singleton, Nat.lt_one_iff] at h; subst h; rfl
  | k + 1, c, 0, _ => rfl
  | k + 1, c, i + 1, h => by
    cases hc : fractranStep prog c with
    | none => simp [orbit, hc] at h
    | some c' =>
      simp only [orbit, hc, List.length_cons, Nat.add_lt_add_iff_right] at h
      simp only [orbit, hc, List.getElem_cons_succ]
      simp only [fractranRun, hc, Option.bind_some]
      exact orbit_spec prog k c' i h

/-- Exponent of `c` if `c` is a power of two (fuel-bounded, kernel-friendly). -/
def log2Exact : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | f + 1, c => if c = 1 then some 0 else if c % 2 = 0 then (log2Exact f (c / 2)).map (· + 1)
    else none

theorem log2Exact_spec : ∀ (f c e : ℕ), log2Exact f c = some e → c = 2 ^ e
  | 0, _, _, h => by simp [log2Exact] at h
  | f + 1, c, e, h => by
    unfold log2Exact at h
    split_ifs at h with h1 h2
    · cases h; simp [h1]
    · obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.1 h
      have := log2Exact_spec f (c / 2) e' he'
      rw [pow_succ, ← this]; omega

theorem log2Exact_pow : ∀ (e f : ℕ), e < f → log2Exact f (2 ^ e) = some e
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, f + 1, _ => by simp [log2Exact]
  | e + 1, f + 1, h => by
    have h1 : 2 ^ (e + 1) ≠ 1 := by
      have := Nat.one_lt_two_pow (n := e + 1) (by omega); omega
    have h2 : 2 ^ (e + 1) % 2 = 0 := by rw [pow_succ]; simp
    rw [log2Exact, if_neg h1, if_pos h2, show 2 ^ (e + 1) / 2 = 2 ^ e by rw [pow_succ]; simp,
      log2Exact_pow e f (by omega)]
    rfl

/-- The 711 states of the first 710 steps of PRIMEGAME from `2`. -/
def pgOrbit : List ℕ := orbit primegame 710 2

/-- Steps and exponents of the powers of two among the first 711 states. -/
def pgPow2 : List (ℕ × ℕ) :=
  pgOrbit.zipIdx.filterMap fun p => (log2Exact (p.1 + 1) p.1).map fun e => (p.2, e)

set_option maxRecDepth 10000 in
/-- **Kernel run of PRIMEGAME**: among its first 711 states the powers of two are exactly
`2^1, 2^2, 2^3, 2^5, 2^7`, at steps 0, 19, 69, 281, 710. -/
theorem primegame_orbit_pow2 :
    pgOrbit.length = 711 ∧ pgPow2 = [(0, 1), (19, 2), (69, 3), (281, 5), (710, 7)] := by
  decide +kernel

theorem primegame_19 : fractranRun primegame 19 2 = some (2 ^ 2) := by decide +kernel
theorem primegame_69 : fractranRun primegame 69 2 = some (2 ^ 3) := by decide +kernel
theorem primegame_281 : fractranRun primegame 281 2 = some (2 ^ 5) := by decide +kernel
theorem primegame_710 : fractranRun primegame 710 2 = some (2 ^ 7) := by decide +kernel

/-- PRIMEGAME's first step. -/
theorem primegame_first_step : fractranStep primegame 2 = some 15 := by decide +kernel

theorem shapeOf_two : shapeOf sspBasis 2 = vec [1] := by
  rw [show shapeOf sspBasis 2 = shapeOf sspBasis (godel sspBasis (vec [1])) from
    congrArg _ (by decide +kernel), shapeOf_godel]

theorem shapeOf_fifteen : shapeOf sspBasis 15 = vec [0, 1, 1] := by
  rw [show shapeOf sspBasis 15 = shapeOf sspBasis (godel sspBasis (vec [0, 1, 1])) from
    congrArg _ (by decide +kernel), shapeOf_godel]

/-- **PRIMEGAME changes mass**: its first step takes total exponent mass 1 to 2. -/
theorem primegame_changes_mass :
    fractranStep primegame 2 = some 15 ∧ mass (shapeOf sspBasis 2) = 1 ∧
      mass (shapeOf sspBasis 15) = 2 := by
  refine ⟨primegame_first_step, ?_, ?_⟩
  · rw [shapeOf_two]; decide
  · rw [shapeOf_fifteen]; decide

/-- Every VM step conserves the mass of the configuration's exponent vector. -/
theorem vm_step_conserves_mass {n : ℕ} (S : VMSpec n) {s s' : VMState n} (hs : VMInvariant S s)
    (h : step S s = some s') :
    mass (shapeOf S.basis s'.config) = mass (shapeOf S.basis s.config) := by
  rw [(step_preserves_invariant S h).shapeOf_config, hs.shapeOf_config,
    (step_preserves_invariant S h).2.2, hs.2.2]

/-- **The VM gate rejects PRIMEGAME**: no step of any shape-dispatched VM over the supersingular
basis goes from configuration `2` to configuration `15`, while PRIMEGAME's first step does. -/
theorem primegame_rejected (S : VMSpec 15) (hB : S.basis = sspBasis) {s s' : VMState 15}
    (hs : VMInvariant S s) (h2 : s.config = 2) (h : step S s = some s') : s'.config ≠ 15 := by
  intro h15
  have := vm_step_conserves_mass S hs h
  rw [hB, h2, h15, primegame_changes_mass.2.1, primegame_changes_mass.2.2] at this
  omega

end Dasein15VM.Cryptids

namespace Dasein15VM.Cryptids

/-- Each entry `(k, e)` of `pgPow2` is a genuine run: `k` PRIMEGAME steps from `2` give `2 ^ e`. -/
theorem pgPow2_sound : ∀ p ∈ pgPow2, fractranRun primegame p.1 2 = some (2 ^ p.2) := by
  intro p hp
  obtain ⟨⟨c, k⟩, hq, he⟩ := List.mem_filterMap.1 hp
  obtain ⟨e, he', rfl⟩ := Option.map_eq_some_iff.1 he
  rw [List.mem_zipIdx_iff_getElem?] at hq
  obtain ⟨hk, hc⟩ := List.getElem?_eq_some_iff.1 hq
  rw [orbit_spec primegame 710 2 k hk]
  simp only at hc ⊢
  unfold pgOrbit at hc
  rw [hc, ← log2Exact_spec _ c e he']

end Dasein15VM.Cryptids

namespace Dasein15VM.Cryptids

/-- **Completeness**: every power of two reached within 710 steps is listed in `pgPow2`. -/
theorem pgPow2_complete (k e : ℕ) (hk : k ≤ 710) (h : fractranRun primegame k 2 = some (2 ^ e)) :
    (k, e) ∈ pgPow2 := by
  have hlen : k < pgOrbit.length := by rw [primegame_orbit_pow2.1]; omega
  have hrun := orbit_spec primegame 710 2 k hlen
  rw [h, Option.some_inj] at hrun
  refine List.mem_filterMap.2 ⟨(2 ^ e, k), ?_, ?_⟩
  · rw [List.mem_zipIdx_iff_getElem?]
    exact List.getElem?_eq_some_iff.2 ⟨hlen, hrun.symm⟩
  · simp only
    rw [log2Exact_pow e _ (by have := Nat.lt_two_pow_self (n := e); omega)]
    rfl

/-- **PRIMEGAME's first five prime outputs**: for `k ≤ 710`, `k` steps from `2` land on a power
of two `2 ^ e` exactly for `(k, e) ∈ {(0,1), (19,2), (69,3), (281,5), (710,7)}`. -/
theorem primegame_pow2_iff (k e : ℕ) (hk : k ≤ 710) :
    fractranRun primegame k 2 = some (2 ^ e) ↔
      (k, e) ∈ [(0, 1), (19, 2), (69, 3), (281, 5), (710, 7)] := by
  rw [← primegame_orbit_pow2.2]
  exact ⟨pgPow2_complete k e hk, pgPow2_sound (k, e)⟩

end Dasein15VM.Cryptids
