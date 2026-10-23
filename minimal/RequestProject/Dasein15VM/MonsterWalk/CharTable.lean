import Mathlib

/-!
# Character table and Clebsch–Gordan composition for a finite group (REQ-0001 item 3)

`MonsterWalkZKP` names three representation-theoretic ingredients of "the Monster IS the VM" —
conjugacy classes as opcodes, the character table as instruction semantics, and Clebsch–Gordan
coefficients as composition rules — but formalizes none of them. The Monster group itself is not
available in Mathlib, and its 194 × 194 character table is not supplied, so they are formalized
here **for an arbitrary finite group `G` over `ℂ`**; the Monster is the intended instance.

* `Opcode G := ConjClasses G`; `classChar V : Opcode G → ℂ` is the character of a representation
  read on conjugacy classes (well defined because characters are class functions).
* `charTable ρ` — for a family `ρ : ι → FDRep ℂ G` of representations, the table
  `ι → Opcode G → ℂ`. `charTable_orthonormal` gives the first orthogonality relation for
  irreducible rows; `classChar_one` says the entry at the identity class is the dimension
  ("register width").
* `cg V W U := finrank (U ⟶ V ⊗ W)`: the Clebsch–Gordan multiplicity of `U` in `V ⊗ W`.
  - `cg_eq_char`: the character formula
    `cg V W U = |G|⁻¹ Σ_g χ_V(g) χ_W(g) χ_U(g⁻¹)`;
  - `cg_comm`: composition is commutative, `cg V W U = cg W V U`;
  - `unit_ρ`, `unit_character`: the monoidal unit `𝟙` is the trivial representation;
  - `cg_unit_left`, `cg_unit_right`: **the trivial representation is the identity (NOP) of
    composition**: `cg 𝟙 W U = finrank (U ⟶ W)`;
  - `cg_unit_simple`: for irreducible `U`, `W`: `cg 𝟙 W U = 1` if `U ≅ W` and `0` otherwise.
-/

namespace MonsterWalkZKP.RepVM

open CategoryTheory MonoidalCategory FDRep

variable {G : Type} [Group G]

/-- Opcodes of the group VM: conjugacy classes. -/
abbrev Opcode (G : Type) [Group G] := ConjClasses G

/-- The character of `V` on a conjugacy class. -/
noncomputable def classChar (V : FDRep ℂ G) : Opcode G → ℂ :=
  Quotient.lift V.character fun a b (h : IsConj a b) => by
    obtain ⟨c, rfl⟩ := isConj_iff.1 h
    exact (char_conj V a c).symm

@[simp] theorem classChar_mk (V : FDRep ℂ G) (g : G) :
    classChar V (ConjClasses.mk g) = V.character g := rfl

/-- The entry of a character at the identity class is the dimension ("register width"). -/
theorem classChar_one (V : FDRep ℂ G) :
    classChar V (ConjClasses.mk 1) = Module.finrank ℂ V := by
  simp

/-- The character table of a family of representations. -/
noncomputable def charTable {ι : Type} (ρ : ι → FDRep ℂ G) : ι → Opcode G → ℂ :=
  fun i => classChar (ρ i)

/-- The monoidal unit of `FDRep ℂ G` is the trivial representation: every group element acts as the
identity. -/
theorem unit_ρ (g : G) : (𝟙_ (FDRep ℂ G)).ρ g = LinearMap.id := rfl

/-- Its character is constantly `1` (in particular it is one-dimensional). -/
theorem unit_character (g : G) : (𝟙_ (FDRep ℂ G)).character g = 1 := by
  rw [FDRep.character, unit_ρ, LinearMap.trace_id]
  exact_mod_cast Module.finrank_self ℂ

/-- **Clebsch–Gordan multiplicity** of `U` in `V ⊗ W`. -/
noncomputable def cg (V W U : FDRep ℂ G) : ℕ := Module.finrank ℂ (U ⟶ V ⊗ W)

/-- **The trivial representation is the NOP of composition** (left). -/
theorem cg_unit_left (W U : FDRep ℂ G) : cg (𝟙_ (FDRep ℂ G)) W U = Module.finrank ℂ (U ⟶ W) :=
  LinearEquiv.finrank_eq (Linear.homCongr ℂ (Iso.refl U) (λ_ W))

/-- **The trivial representation is the NOP of composition** (right). -/
theorem cg_unit_right (W U : FDRep ℂ G) : cg W (𝟙_ (FDRep ℂ G)) U = Module.finrank ℂ (U ⟶ W) :=
  LinearEquiv.finrank_eq (Linear.homCongr ℂ (Iso.refl U) (ρ_ W))

open scoped Classical in
/-- For irreducible `U`, `W`: `𝟙 ⊗ W` contains `U` once if `U ≅ W` and not at all otherwise. -/
theorem cg_unit_simple (W U : FDRep ℂ G) [Simple W] [Simple U] :
    cg (𝟙_ (FDRep ℂ G)) W U = if Nonempty (U ≅ W) then 1 else 0 := by
  rw [cg_unit_left]
  convert finrank_hom_simple_simple ℂ U W

variable [Fintype G]

noncomputable instance : Invertible (Fintype.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

open scoped Classical in
/-- **First orthogonality relation** for irreducible rows of the character table. -/
theorem charTable_orthonormal {ι : Type} (ρ : ι → FDRep ℂ G) (i j : ι) [Simple (ρ i)]
    [Simple (ρ j)] :
    ⅟(Fintype.card G : ℂ) •
        ∑ g : G, charTable ρ i (ConjClasses.mk g) * charTable ρ j (ConjClasses.mk g⁻¹) =
      if Nonempty (ρ i ≅ ρ j) then 1 else 0 := by
  simpa [charTable] using char_orthonormal (ρ i) (ρ j)

/-- The character formula for Clebsch–Gordan multiplicities. -/
theorem cg_eq_char (V W U : FDRep ℂ G) :
    (cg V W U : ℂ) =
      ⅟(Fintype.card G : ℂ) • ∑ g : G, V.character g * W.character g * U.character g⁻¹ := by
  rw [cg, ← scalar_product_char_eq_finrank_equivariant]
  simp

/-- Composition is commutative. -/
theorem cg_comm (V W U : FDRep ℂ G) : cg V W U = cg W V U := by
  have h := cg_eq_char V W U
  rw [show (∑ g : G, V.character g * W.character g * U.character g⁻¹) =
      ∑ g : G, W.character g * V.character g * U.character g⁻¹ by
    simp only [mul_comm (V.character _)], ← cg_eq_char] at h
  exact_mod_cast h

end MonsterWalkZKP.RepVM
