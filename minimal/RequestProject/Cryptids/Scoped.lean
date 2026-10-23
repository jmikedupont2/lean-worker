import RequestProject.Cryptids.Primegame

/-!
# Cryptids, part 5: mass-scoped runs (PRIMEGAME with a mass range)

The Dasein15 VM gate demands *exact* mass conservation, so it rejects PRIMEGAME
(`primegame_rejected`). Here the gate is relaxed to a **scope**: a run is told

* `massMin`, `massMax` — the band of total SSP exponent mass every state must stay in;
* `variance` — the largest allowed change of mass in one step;
* `gas` — the largest number of steps.

`scopedRun sc prog c` runs the FRACTRAN program `prog` from `c`. Before admitting a state it
computes the exponent vector over the 15 supersingular primes and *checks* that the state is the
Gödel number of that vector (so the state has no other prime factor, and the vector is
`shapeOf sspBasis c`); then it checks the band and the step change. It stops with

* `halted` — the program halted (no fraction applies);
* `gasExhausted` — `gas` steps were taken, all in scope;
* `outOfScope` — the next state would leave the band, jump by more than `variance`, or not be
  a pure SSP number (or the start itself is out of scope).

**Soundness** (`scopedRun_sound`): the returned trace starts at `c`; consecutive states are
FRACTRAN steps of `prog`; every state is a pure SSP number whose mass lies in
`[massMin, massMax]`; consecutive masses differ by at most `variance`; there are at most `gas`
steps; `halted` really means halted and `gasExhausted` means exactly `gas` steps were taken.
`exact_scope_conserves`: with `variance = 0` the scope is the Dasein15
VM's conservation law.

**PRIMEGAME scoped** (`pgScope = ⟨1, 14, 2, 710⟩`):

* `primegame_scoped`: from `2`, PRIMEGAME runs all 710 steps inside the scope, and its trace is
  exactly the orbit `pgOrbit`, so it passes `2^2, 2^3, 2^5, 2^7` (`primegame_scoped_primes`).
* The scope is tight in every parameter (`primegame_scope_tight`): with `massMax = 13` it stops
  out of scope after 413 steps; with `massMin = 2` the start `2` (mass 1) is already rejected; with
  `variance = 1` it stops after 1 step (`2 ↦ 15 ↦ 825`, mass 2 → 4); and with `gas = 709` it stops
  one step short of `2^7`.
* Observed statistics of the 711 masses (`primegame_mass_stats`): minimum 1, maximum 14, largest
  step change 2, mean `709/79`, variance `373160/56169` (population variance).
-/

namespace Dasein15VM.Cryptids

open Dasein15 Dasein15VM

/-! ## Measuring mass, with a checked factorisation -/

/-- How many times `p` divides `c` (fuel-bounded; only a *guess*, checked below). -/
def countDiv (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, c => if c ≠ 0 ∧ c % p = 0 then countDiv p f (c / p) + 1 else 0

/-- Guessed exponent vector over the 15 supersingular primes. -/
def shapeGuess (c : ℕ) : PrimeShape 15 := fun i => countDiv (SSP i) 128 c

/-- The mass of `c`, if `c` is certified to be the Gödel number of the guessed vector. -/
def sspMass? (c : ℕ) : Option ℕ :=
  if godel sspBasis (shapeGuess c) = c then some (mass (shapeGuess c)) else none

/-- A state is pure SSP with mass `m`. -/
def PureMass (c m : ℕ) : Prop :=
  c = godel sspBasis (shapeOf sspBasis c) ∧ mass (shapeOf sspBasis c) = m

theorem sspMass?_sound {c m : ℕ} (h : sspMass? c = some m) : PureMass c m := by
  unfold sspMass? at h
  split_ifs at h with hg
  cases h
  have hs : shapeOf sspBasis c = shapeGuess c := by
    conv_lhs => rw [← hg]
    exact shapeOf_godel _ _
  exact ⟨by rw [hs, hg], by rw [hs]⟩

/-! ## Scopes and scoped runs -/

/-- A mass scope: band, largest step change, step budget. -/
structure MassScope where
  massMin : ℕ
  massMax : ℕ
  variance : ℕ
  gas : ℕ
  deriving DecidableEq, Repr

inductive ScopeStatus
  | halted
  | gasExhausted
  | outOfScope
  deriving DecidableEq, Repr

/-- The band test. -/
def MassScope.inBand (sc : MassScope) (m : ℕ) : Bool := sc.massMin ≤ m && m ≤ sc.massMax

/-- The step-change test. -/
def MassScope.near (sc : MassScope) (m m' : ℕ) : Bool := m' ≤ m + sc.variance && m ≤ m' + sc.variance

/-- The scoped loop from state `c` of mass `m`, with `g` steps of gas left. -/
def scopedLoop (sc : MassScope) (prog : List ℚ) : ℕ → ℕ → ℕ → List ℕ × ScopeStatus
  | 0, c, _ => ([c], .gasExhausted)
  | g + 1, c, m =>
    match fractranStep prog c with
    | none => ([c], .halted)
    | some c' =>
      match sspMass? c' with
      | none => ([c], .outOfScope)
      | some m' =>
        if sc.inBand m' && sc.near m m' then
          let r := scopedLoop sc prog g c' m'
          (c :: r.1, r.2)
        else ([c], .outOfScope)

/-- **Scoped run** of `prog` from `c`. -/
def scopedRun (sc : MassScope) (prog : List ℚ) (c : ℕ) : List ℕ × ScopeStatus :=
  match sspMass? c with
  | none => ([], .outOfScope)
  | some m => if sc.inBand m then scopedLoop sc prog sc.gas c m else ([], .outOfScope)

/-- What a scoped run guarantees about its trace `tr` and status `st`. -/
def ScopedCorrect (sc : MassScope) (prog : List ℚ) (c : ℕ) (tr : List ℕ) (st : ScopeStatus) :
    Prop :=
  (tr ≠ [] → tr.head? = some c) ∧
  (∀ i (h : i + 1 < tr.length), fractranStep prog tr[i] = some tr[i + 1]) ∧
  (∀ x ∈ tr, ∃ m, PureMass x m ∧ sc.massMin ≤ m ∧ m ≤ sc.massMax) ∧
  (∀ i (h : i + 1 < tr.length), ∀ m m', PureMass tr[i] m → PureMass tr[i + 1] m' →
    m' ≤ m + sc.variance ∧ m ≤ m' + sc.variance) ∧
  tr.length ≤ sc.gas + 1 ∧
  (st = .halted → ∃ z, tr.getLast? = some z ∧ fractranStep prog z = none) ∧
  (st = .gasExhausted → tr.length = sc.gas + 1)

theorem PureMass.unique {c m m' : ℕ} (h : PureMass c m) (h' : PureMass c m') : m = m' :=
  h.2.symm.trans h'.2

/-- One FRACTRAN step relation. -/
def StepRel (prog : List ℚ) (a b : ℕ) : Prop := fractranStep prog a = some b

/-- The step-change relation of a scope. -/
def NearRel (sc : MassScope) (a b : ℕ) : Prop :=
  ∀ m m', PureMass a m → PureMass b m' → m' ≤ m + sc.variance ∧ m ≤ m' + sc.variance

/-- Invariant of the loop. -/
structure LoopOK (sc : MassScope) (prog : List ℚ) (g c : ℕ) (r : List ℕ × ScopeStatus) :
    Prop where
  head : r.1.head? = some c
  chain : r.1.IsChain (StepRel prog)
  near : r.1.IsChain (NearRel sc)
  band : ∀ x ∈ r.1, ∃ m, PureMass x m ∧ sc.massMin ≤ m ∧ m ≤ sc.massMax
  len : r.1.length ≤ g + 1
  halted : r.2 = .halted → ∃ z, r.1.getLast? = some z ∧ fractranStep prog z = none
  gas : r.2 = .gasExhausted → r.1.length = g + 1

theorem LoopOK.single {sc : MassScope} {prog : List ℚ} {g c m : ℕ} (st : ScopeStatus)
    (hc : PureMass c m) (h1 : sc.massMin ≤ m) (h2 : m ≤ sc.massMax)
    (hh : st = .halted → fractranStep prog c = none) (hg : st = .gasExhausted → g = 0) :
    LoopOK sc prog g c ([c], st) where
  head := rfl
  chain := List.isChain_singleton _
  near := List.isChain_singleton _
  band := fun x hx => by simp at hx; subst hx; exact ⟨m, hc, h1, h2⟩
  len := by simp
  halted := fun h => ⟨c, rfl, hh h⟩
  gas := fun h => by simp [hg h]

theorem scopedLoop_sound (sc : MassScope) (prog : List ℚ) :
    ∀ (g c m : ℕ), PureMass c m → sc.massMin ≤ m → m ≤ sc.massMax →
      LoopOK sc prog g c (scopedLoop sc prog g c m)
  | 0, c, m, hc, h1, h2 => LoopOK.single _ hc h1 h2 (fun h => by simp at h) (fun _ => rfl)
  | g + 1, c, m, hc, h1, h2 => by
    rw [scopedLoop]
    split
    · next hs => exact LoopOK.single _ hc h1 h2 (fun _ => hs) (fun h => by simp at h)
    · next c' hs =>
      split
      · exact LoopOK.single _ hc h1 h2 (fun h => by simp at h) (fun h => by simp at h)
      · next m' hm =>
        split_ifs with hb
        · simp only [MassScope.inBand, MassScope.near, Bool.and_eq_true, decide_eq_true_eq] at hb
          obtain ⟨⟨hb1, hb2⟩, hn1, hn2⟩ := hb
          have hc' := sspMass?_sound hm
          have ih := scopedLoop_sound sc prog g c' m' hc' hb1 hb2
          generalize scopedLoop sc prog g c' m' = r at ih ⊢
          obtain ⟨l, st⟩ := r
          obtain ⟨ih0, ih1, ih2, ih3, ih4, ih5, ih6⟩ := ih
          simp only at ih0 ih1 ih2 ih3 ih4 ih5 ih6 ⊢
          obtain ⟨ys, rfl⟩ : ∃ ys, l = c' :: ys := by
            cases l with
            | nil => simp at ih0
            | cons y ys => simp at ih0; exact ⟨ys, by rw [ih0]⟩
          refine ⟨rfl, ih1.cons_cons hs, ih2.cons_cons ?_, ?_, ?_, ?_, ?_⟩
          · intro a b ha hb'
            have e1 := ha.unique hc
            have e2 := hb'.unique hc'
            subst e1; subst e2; exact ⟨hn1, hn2⟩
          · intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact ⟨m, hc, h1, h2⟩
            · exact ih3 x hx
          · simp only [List.length_cons] at ih4 ⊢; omega
          · intro h
            obtain ⟨z, hz, hz'⟩ := ih5 h
            exact ⟨z, by rw [List.getLast?_cons, hz]; rfl, hz'⟩
          · intro h; simp only [List.length_cons] at ih6 ⊢; rw [ih6 h]
        · exact LoopOK.single _ hc h1 h2 (fun h => by simp at h) (fun h => by simp at h)

/-- **Soundness of scoped runs.** -/
theorem scopedRun_sound (sc : MassScope) (prog : List ℚ) (c : ℕ) :
    ScopedCorrect sc prog c (scopedRun sc prog c).1 (scopedRun sc prog c).2 := by
  unfold scopedRun
  cases hm : sspMass? c with
  | none => exact ⟨fun h => absurd rfl h, fun i h => by simp at h, fun x hx => by simp at hx,
      fun i h => by simp at h, by simp, fun h => by simp at h, fun h => by simp at h⟩
  | some m =>
    simp only
    split_ifs with hb
    · simp only [MassScope.inBand, Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ :=
        scopedLoop_sound sc prog sc.gas c m (sspMass?_sound hm) hb.1 hb.2
      exact ⟨fun _ => h0, h1.getElem, h3, h2.getElem, h4, h5, h6⟩
    · exact ⟨fun h => absurd rfl h, fun i h => by simp at h, fun x hx => by simp at hx,
        fun i h => by simp at h, by simp, fun h => by simp at h, fun h => by simp at h⟩

/-- An exact scope (`variance = 0`) is the Dasein15 VM's conservation law: along a scoped trace,
all states have the same mass. -/
theorem exact_scope_conserves (sc : MassScope) (hv : sc.variance = 0) (prog : List ℚ) (c : ℕ)
    (i : ℕ) (h : i + 1 < (scopedRun sc prog c).1.length) :
    mass (shapeOf sspBasis (scopedRun sc prog c).1[i + 1]) =
      mass (shapeOf sspBasis (scopedRun sc prog c).1[i]) := by
  have hs := scopedRun_sound sc prog c
  have := hs.2.2.2.1 i h _ _ ⟨(hs.2.2.1 _ (List.getElem_mem _)).choose_spec.1.1, rfl⟩
    ⟨(hs.2.2.1 _ (List.getElem_mem _)).choose_spec.1.1, rfl⟩
  rw [hv] at this; omega

/-! ## PRIMEGAME, scoped -/

/-- The scope of PRIMEGAME's first 710 steps from `2`. -/
def pgScope : MassScope := ⟨1, 14, 2, 710⟩

set_option maxRecDepth 10000 in
/-- **PRIMEGAME runs inside the scope** `⟨1, 14, 2, 710⟩`: all 710 steps are admitted and the
trace is exactly the orbit `pgOrbit`. -/
theorem primegame_scoped : scopedRun pgScope primegame 2 = (pgOrbit, .gasExhausted) := by
  decide +kernel

/-- Inside the scope PRIMEGAME still produces its prime powers of two. -/
theorem primegame_scoped_primes :
    (scopedRun pgScope primegame 2).2 = .gasExhausted ∧
      ∀ e ∈ [2, 3, 5, 7], 2 ^ e ∈ (scopedRun pgScope primegame 2).1 := by
  rw [primegame_scoped]
  refine ⟨rfl, ?_⟩
  intro e he
  have h := pgPow2_sound
  rw [primegame_orbit_pow2.2] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  have key : ∀ k, k ≤ 710 → ∀ c, fractranRun primegame k 2 = some c → c ∈ pgOrbit := by
    intro k hk c hc
    have hlen : k < pgOrbit.length := by rw [primegame_orbit_pow2.1]; omega
    have := orbit_spec primegame 710 2 k hlen
    rw [hc, Option.some_inj] at this
    rw [this]; exact List.getElem_mem _
  rcases he with rfl | rfl | rfl | rfl
  · exact key 19 (by norm_num) _ (h (19, 2) (by simp))
  · exact key 69 (by norm_num) _ (h (69, 3) (by simp))
  · exact key 281 (by norm_num) _ (h (281, 5) (by simp))
  · exact key 710 le_rfl _ (h (710, 7) (by simp))

set_option maxRecDepth 10000 in
/-- **The scope is tight in every parameter.** -/
theorem primegame_scope_tight :
    ((scopedRun ⟨1, 13, 2, 710⟩ primegame 2).2 = .outOfScope ∧
      (scopedRun ⟨1, 13, 2, 710⟩ primegame 2).1.length = 414) ∧
    scopedRun ⟨2, 14, 2, 710⟩ primegame 2 = ([], .outOfScope) ∧
    scopedRun ⟨1, 14, 1, 710⟩ primegame 2 = ([2, 15], .outOfScope) ∧
    ((scopedRun ⟨1, 14, 2, 709⟩ primegame 2).2 = .gasExhausted ∧
      2 ^ 7 ∉ (scopedRun ⟨1, 14, 2, 709⟩ primegame 2).1) := by
  decide +kernel

/-- The masses along a trace. -/
def traceMasses (tr : List ℕ) : List ℕ := tr.map fun c => (sspMass? c).getD 0

set_option maxRecDepth 10000 in
/-- Raw statistics of PRIMEGAME's 711 masses: count, min, max, largest step change, `Σ m`,
`Σ m²`. -/
theorem primegame_mass_raw :
    (traceMasses pgOrbit).length = 711 ∧ (traceMasses pgOrbit).min? = some 1 ∧
      (traceMasses pgOrbit).max? = some 14 ∧
      (List.zipWith (fun a b => max a b - min a b) (traceMasses pgOrbit)
        (traceMasses pgOrbit).tail).max? = some 2 ∧
      (traceMasses pgOrbit).sum = 6381 ∧ ((traceMasses pgOrbit).map (· ^ 2)).sum = 61991 := by
  decide +kernel

/-- **Observed mass statistics of PRIMEGAME's run** (mean and population variance). -/
theorem primegame_mass_stats :
    let l := traceMasses pgOrbit
    ((l.sum : ℚ) / l.length = 709 / 79) ∧
      ((((l.map (fun x => x ^ 2)).sum : ℕ) : ℚ) / l.length - ((l.sum : ℚ) / l.length) ^ 2 = 373160 / 56169) := by
  obtain ⟨h1, -, -, -, h5, h6⟩ := primegame_mass_raw
  simp only [h1, h5, h6]
  norm_num

end Dasein15VM.Cryptids
