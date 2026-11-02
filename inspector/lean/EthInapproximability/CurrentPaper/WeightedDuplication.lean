import EthInapproximability.ParameterizedNP.DenseStageFourOpening

/-!
# Rational multiplicities for the current replacement paper

Source: `papers/interlacing-np-eth/versions/2026-09-22-complete-replacement-v8/`
`source/sections/A-stage4-details.tex`, `lem:paper-weighted-blowup` and the
following input-group construction (lines 143--236).

This module constructs actual finite labelled inputs.  The current column
construction has TWO supports, with weights 182 and 2, followed by a uniform
duplication.  It does not reuse the frozen three-support matrix.

Only the generic protocol transport theorem `DenseStageFourOpening.D_forget_eq`
is reused from that module.  Its proof was inspected: it pulls protocol trees
back along input maps and applies the right inverses in the other direction.
The literal transpose uses the inspected `NPCC.comp_transpose`, whose proof is
the protocol-swap theorem `Workspace.UpperBound.D_swap`.
No protected-hardness closure or promise-side certificate is imported as a
hypothesis.  The conclusions here concern duplication, not Stage--4 hardness.
-/

namespace EthInapproximability.CurrentPaper.WeightedDuplication

open scoped BigOperators
open EthInapproximability.ParameterizedNP.DenseStageFourOpening
open Workspace.Types.CommComplexity

universe u v w

section Generic

variable {I : Type u} [Fintype I] [DecidableEq I]
variable (S : I → Type v) [∀ i, Fintype (S i)] (c : I → ℕ)

/-- Number of labelled copies of each original input in a group. -/
def copies (i : I) : ℕ := c i * ∏ h ∈ Finset.univ.erase i, Fintype.card (S h)

/-- An actual copy consists of its original element and its copy index. -/
abbrev Group (i : I) := S i × Fin (copies S c i)

/-- The group label remains part of the input even for overlapping supports. -/
abbrev Carrier := (i : I) × Group S c i

theorem card_group (i : I) :
    Fintype.card (Group S c i) = c i * ∏ h, Fintype.card (S h) := by
  change Fintype.card (S i × Fin (copies S c i)) = _
  rw [Fintype.card_prod, Fintype.card_fin]
  unfold copies
  rw [show Fintype.card (S i) * (c i * ∏ h ∈ Finset.univ.erase i,
      Fintype.card (S h)) = c i * (Fintype.card (S i) *
      ∏ h ∈ Finset.univ.erase i, Fintype.card (S h)) by ring]
  rw [Finset.mul_prod_erase Finset.univ (fun h => Fintype.card (S h))
    (Finset.mem_univ i)]

theorem card_carrier :
    Fintype.card (Carrier S c) = (∑ i, c i) * ∏ h, Fintype.card (S h) := by
  simp only [Carrier, Fintype.card_sigma, card_group]
  rw [Finset.sum_mul]

theorem copies_pos (hc : ∀ i, 0 < c i) (hS : ∀ i, 0 < Fintype.card (S i))
    (i : I) : 0 < copies S c i := by
  exact Nat.mul_pos (hc i) (Finset.prod_pos fun h _ => hS h)

theorem group_mass (hS : ∀ i, 0 < Fintype.card (S i))
    (i : I) :
    (Fintype.card (Group S c i) : ℚ) / Fintype.card (Carrier S c) =
      (c i : ℚ) / ∑ h, (c h : ℚ) := by
  have hp : (∏ h, (Fintype.card (S h) : ℚ)) ≠ 0 := by
    exact ne_of_gt (Finset.prod_pos fun h _ => by exact_mod_cast hS h)
  rw [card_group, card_carrier]
  push_cast
  exact mul_div_mul_right _ _ hp

/-- Each group projection has precisely the prescribed number of copies. -/
def fibreEquiv (i : I) (x : S i) :
    {a : Group S c i // a.1 = x} ≃ Fin (copies S c i) where
  toFun a := a.1.2
  invFun k := ⟨(x, k), rfl⟩
  left_inv a := by rcases a with ⟨⟨a, k⟩, h⟩; cases h; rfl
  right_inv _ := rfl

theorem card_fibre [∀ i, DecidableEq (S i)] (i : I) (x : S i) :
    Fintype.card {a : Group S c i // a.1 = x} = copies S c i := by
  classical
  exact (Fintype.card_congr (fibreEquiv S c i x)).trans (Fintype.card_fin _)

/-- Forgetting labels evaluates the actual original input. -/
def forget {X : Type w} (incl : ∀ i, S i → X) (a : Carrier S c) : X :=
  incl a.1 a.2.1

/-- A full support supplies a representative for every original input. -/
def representative {X : Type w} (i : I) (sec : X → S i)
    (hcopy : 0 < copies S c i) (x : X) : Carrier S c :=
  ⟨i, sec x, ⟨0, hcopy⟩⟩

@[simp] theorem forget_representative {X : Type w} (incl : ∀ i, S i → X)
    (i : I) (sec : X → S i) (hcopy : 0 < copies S c i)
    (hsec : ∀ x, incl i (sec x) = x) (x : X) :
    forget S c incl (representative S c i sec hcopy x) = x := hsec x

theorem forget_surjective {X : Type w} (incl : ∀ i, S i → X)
    (i : I) (sec : X → S i) (hcopy : 0 < copies S c i)
    (hsec : ∀ x, incl i (sec x) = x) :
    Function.Surjective (forget S c incl) := by
  intro x
  exact ⟨representative S c i sec hcopy x,
    forget_representative S c incl i sec hcopy hsec x⟩

theorem representative_injective {X : Type w} (incl : ∀ i, S i → X)
    (i : I) (sec : X → S i) (hcopy : 0 < copies S c i)
    (hsec : ∀ x, incl i (sec x) = x) :
    Function.Injective (representative S c i sec hcopy) :=
  Function.LeftInverse.injective (forget_representative S c incl i sec hcopy hsec)

end Generic

section Density

variable {S : Type u} [Fintype S] [DecidableEq S] {d : ℕ}

omit [Fintype S] in
/-- A retained set cannot have more than `d` copies of each projected input. -/
theorem retained_card_le (E : Finset (S × Fin d)) :
    E.card ≤ (E.image Prod.fst).card * d := by
  have hsub : E ⊆ (E.image Prod.fst) ×ˢ (Finset.univ : Finset (Fin d)) := by
    intro a ha
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      Finset.mem_univ _⟩
  simpa using Finset.card_le_card hsub

/-- Projecting a positive uniform duplication never lowers retained density. -/
theorem retained_density_le (E : Finset (S × Fin d))
    (hS : 0 < Fintype.card S) (hd : 0 < d) :
    (E.card : ℚ) / Fintype.card (S × Fin d) ≤
      ((E.image Prod.fst).card : ℚ) / Fintype.card S := by
  have hS' : (0 : ℚ) < Fintype.card S := by exact_mod_cast hS
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  apply (div_le_div_iff₀ (mul_pos hS' hd') hS').2
  have h := retained_card_le E
  have h' : (E.card : ℚ) ≤ (E.image Prod.fst).card * (d : ℚ) := by exact_mod_cast h
  nlinarith

/-- The additional uniform column copies preserve exact groupwise fibres. -/
def uniformFibreEquiv (t : ℕ) (x : S) :
    {a : (S × Fin d) × Fin t // a.1.1 = x} ≃ Fin d × Fin t where
  toFun a := (a.1.1.2, a.1.2)
  invFun k := ⟨((x, k.1), k.2), rfl⟩
  left_inv a := by rcases a with ⟨⟨⟨a, k⟩, l⟩, h⟩; cases h; rfl
  right_inv _ := rfl

theorem card_uniform_fibre (t : ℕ) (x : S) :
    Fintype.card {a : (S × Fin d) × Fin t // a.1.1 = x} = d * t := by
  exact (Fintype.card_congr (uniformFibreEquiv t x)).trans
    (by simp only [Fintype.card_prod, Fintype.card_fin])

omit [Fintype S] in
/-- Cardinality bound on the final two-index column groups. -/
theorem retained_uniform_card_le {t : ℕ} (E : Finset ((S × Fin d) × Fin t)) :
    E.card ≤ (E.image (fun a => a.1.1)).card * d * t := by
  have hsub : E ⊆ ((E.image (fun a => a.1.1)) ×ˢ
      (Finset.univ : Finset (Fin d))) ×ˢ (Finset.univ : Finset (Fin t)) := by
    intro a ha
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩, Finset.mem_univ _⟩, Finset.mem_univ _⟩
  simpa using Finset.card_le_card hsub

/-- Retained density does not decrease when both final copy indices are forgotten. -/
theorem retained_uniform_density_le {t : ℕ}
    (E : Finset ((S × Fin d) × Fin t))
    (hS : 0 < Fintype.card S) (hd : 0 < d) (ht : 0 < t) :
    (E.card : ℚ) / Fintype.card ((S × Fin d) × Fin t) ≤
      ((E.image (fun a => a.1.1)).card : ℚ) / Fintype.card S := by
  have hS' : (0 : ℚ) < Fintype.card S := by exact_mod_cast hS
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have ht' : (0 : ℚ) < t := by exact_mod_cast ht
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  apply (div_le_div_iff₀ (mul_pos (mul_pos hS' hd') ht') hS').2
  have h := retained_uniform_card_le E
  have h' : (E.card : ℚ) ≤ (E.image (fun a => a.1.1)).card * (d : ℚ) * t := by
    exact_mod_cast h
  nlinarith

end Density

section Matrix

variable {I J X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype X] [Fintype Y]
variable (R : I → Type*) (C : J → Type*) [∀ i, Fintype (R i)]
  [∀ j, Fintype (C j)] (r : I → ℕ) (c : J → ℕ)

/-- The duplicated matrix simply evaluates the underlying matrix. -/
def blowup (H : X → Y → Bool) (ri : ∀ i, R i → X) (ci : ∀ j, C j → Y) :
    Carrier R r → Carrier C c → Bool :=
  fun x y => H (forget R r ri x) (forget C c ci y)

/-- Full supports on both sides give equality of communication complexity. -/
theorem D_blowup_eq (H : X → Y → Bool) (ri : ∀ i, R i → X)
    (ci : ∀ j, C j → Y) (i : I) (j : J) (rs : X → R i) (cs : Y → C j)
    (hr : 0 < copies R r i) (hc : 0 < copies C c j)
    (hrs : ∀ x, ri i (rs x) = x) (hcs : ∀ y, ci j (cs y) = y) :
    D (blowup R C r c H ri ci) = D H := by
  exact D_forget_eq H (forget R r ri) (forget C c ci)
    (representative R r i rs hr) (representative C c j cs hc)
    (forget_representative R r ri i rs hr hrs)
    (forget_representative C c ci j cs hc hcs)

end Matrix

/-! ## The current paper's two column groups and four row groups -/

/-- There is no third (selector-only) column support in the current paper. -/
def columnSupport (Ω Δ : Type u) : Fin 2 → Type u := ![Ω, Δ]

def columnWeight : Fin 2 → ℕ := ![182, 2]

def rowSupport (X T V B : Type u) : Fin 4 → Type u := ![X, T, V, B]

def rowWeight : Fin 4 → ℕ := ![2 ^ 22 - 4, 2, 1, 1]

instance columnSupportFintype (Ω Δ : Type u) [Fintype Ω] [Fintype Δ] :
    ∀ i, Fintype (columnSupport Ω Δ i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))
  · exact inferInstanceAs (Fintype Ω)
  · exact inferInstanceAs (Fintype Δ)

instance rowSupportFintype (X T V B : Type u)
    [Fintype X] [Fintype T] [Fintype V] [Fintype B] :
    ∀ i, Fintype (rowSupport X T V B i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (fun i => Fin.elim0 i))))
  · exact inferInstanceAs (Fintype X)
  · exact inferInstanceAs (Fintype T)
  · exact inferInstanceAs (Fintype V)
  · exact inferInstanceAs (Fintype B)

instance columnSupportNonempty (Ω Δ : Type u) [Nonempty Ω] [Nonempty Δ] :
    ∀ i, Nonempty (columnSupport Ω Δ i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))
  · exact inferInstanceAs (Nonempty Ω)
  · exact inferInstanceAs (Nonempty Δ)

instance rowSupportNonempty (X T V B : Type u)
    [Nonempty X] [Nonempty T] [Nonempty V] [Nonempty B] :
    ∀ i, Nonempty (rowSupport X T V B i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (fun i => Fin.elim0 i))))
  · exact inferInstanceAs (Nonempty X)
  · exact inferInstanceAs (Nonempty T)
  · exact inferInstanceAs (Nonempty V)
  · exact inferInstanceAs (Nonempty B)

/-- The uniform `Sdup` copies follow the two-group rational blow-up. -/
abbrev Columns (Ω Δ : Type u) [Fintype Ω] [Fintype Δ] (Sdup : ℕ) :=
  Carrier (columnSupport Ω Δ) columnWeight × Fin Sdup

abbrev Rows (X T V B : Type u)
    [Fintype X] [Fintype T] [Fintype V] [Fintype B] :=
  Carrier (rowSupport X T V B) rowWeight

@[simp] theorem card_columnSupport (Ω Δ : Type u) [Fintype Ω] [Fintype Δ]
    (i : Fin 2) : Fintype.card (columnSupport Ω Δ i) =
      ![Fintype.card Ω, Fintype.card Δ] i := by
  fin_cases i <;> rfl

@[simp] theorem card_rowSupport (X T V B : Type u)
    [Fintype X] [Fintype T] [Fintype V] [Fintype B] (i : Fin 4) :
    Fintype.card (rowSupport X T V B i) =
      ![Fintype.card X, Fintype.card T, Fintype.card V, Fintype.card B] i := by
  fin_cases i <;> rfl

theorem card_columns (Ω Δ : Type u) [Fintype Ω] [Fintype Δ] (Sdup : ℕ) :
    Fintype.card (Columns Ω Δ Sdup) =
      184 * Fintype.card Ω * Fintype.card Δ * Sdup := by
  rw [Fintype.card_prod, Fintype.card_fin, card_carrier]
  norm_num [card_columnSupport, columnWeight,
    Fin.sum_univ_succ, Fin.prod_univ_succ]
  left
  ring

theorem card_rows (X T V B : Type u)
    [Fintype X] [Fintype T] [Fintype V] [Fintype B] :
    Fintype.card (Rows X T V B) =
      2 ^ 22 * Fintype.card X * Fintype.card T * Fintype.card V * Fintype.card B := by
  rw [card_carrier]
  norm_num [card_rowSupport, rowWeight,
    Fin.sum_univ_succ, Fin.prod_univ_succ]
  ring

theorem columnSupport_card_pos (Ω Δ : Type u) [Fintype Ω] [Fintype Δ]
    [Nonempty Ω] [Nonempty Δ] (i : Fin 2) :
    0 < Fintype.card (columnSupport Ω Δ i) := by
  exact Fintype.card_pos

theorem rowSupport_card_pos (X T V B : Type u)
    [Fintype X] [Fintype T] [Fintype V] [Fintype B]
    [Nonempty X] [Nonempty T] [Nonempty V] [Nonempty B] (i : Fin 4) :
    0 < Fintype.card (rowSupport X T V B i) := Fintype.card_pos

theorem columnWeight_pos (i : Fin 2) : 0 < columnWeight i := by
  fin_cases i <;> norm_num [columnWeight]

theorem rowWeight_pos (i : Fin 4) : 0 < rowWeight i := by
  fin_cases i <;> norm_num [rowWeight]

/-- The two column masses include the subsequent uniform duplication. -/
theorem column_group_mass (Ω Δ : Type u) [Fintype Ω] [Fintype Δ]
    [Nonempty Ω] [Nonempty Δ] (Sdup : ℕ) (hSdup : 0 < Sdup) (i : Fin 2) :
    (Fintype.card (Group (columnSupport Ω Δ) columnWeight i × Fin Sdup) : ℚ) /
      Fintype.card (Columns Ω Δ Sdup) =
      ![(91 / 92 : ℚ), 1 / 92] i := by
  change (Fintype.card (Group (columnSupport Ω Δ) columnWeight i × Fin Sdup) : ℚ) /
    Fintype.card (Carrier (columnSupport Ω Δ) columnWeight × Fin Sdup) = _
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  have hS' : (Sdup : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hSdup)
  rw [mul_div_mul_right _ _ hS']
  have hm := group_mass (columnSupport Ω Δ) columnWeight
    (columnSupport_card_pos Ω Δ) i
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at hm
  rw [hm]
  fin_cases i <;> norm_num [columnWeight, Fin.sum_univ_succ]

/-- The four row masses of the actual current construction. -/
theorem row_group_mass (X T V B : Type u)
    [Fintype X] [Fintype T] [Fintype V] [Fintype B]
    [Nonempty X] [Nonempty T] [Nonempty V] [Nonempty B] (i : Fin 4) :
    (Fintype.card (Group (rowSupport X T V B) rowWeight i) : ℚ) /
      Fintype.card (Rows X T V B) =
      ![(1 - 1 / 2 ^ 20 : ℚ), 1 / 2 ^ 21, 1 / 2 ^ 22, 1 / 2 ^ 22] i := by
  rw [group_mass (rowSupport X T V B) rowWeight (rowSupport_card_pos X T V B)]
  fin_cases i <;> norm_num [rowWeight, Fin.sum_univ_succ]

section CurrentMatrix

variable {X T V B Ω Δ : Type u}
  [Fintype X] [Fintype T] [Fintype V] [Fintype B] [Fintype Ω] [Fintype Δ]

/-- Supports can overlap: the group tags, not the inclusion maps, distinguish copies. -/
def rowIncl (iT : T → X) (iV : V → X) (iB : B → X) :
    (i : Fin 4) → rowSupport X T V B i → X :=
  Fin.cases id (Fin.cases iT (Fin.cases iV (Fin.cases iB (fun i => Fin.elim0 i))))

def columnIncl (iD : Δ → Ω) : (i : Fin 2) → columnSupport Ω Δ i → Ω :=
  Fin.cases id (Fin.cases iD (fun i => Fin.elim0 i))

def rowForget (iT : T → X) (iV : V → X) (iB : B → X) : Rows X T V B → X :=
  forget (rowSupport X T V B) rowWeight (rowIncl iT iV iB)

def columnForget (iD : Δ → Ω) {Sdup : ℕ} : Columns Ω Δ Sdup → Ω :=
  fun a => forget (columnSupport Ω Δ) columnWeight (columnIncl iD) a.1

/-- The same explicit copy evaluator works in both promise cases. -/
def matrix (H : X → Ω → Bool) (iT : T → X) (iV : V → X) (iB : B → X)
    (iD : Δ → Ω) (Sdup : ℕ) : Rows X T V B → Columns Ω Δ Sdup → Bool :=
  fun r c => H (rowForget iT iV iB r) (columnForget iD c)

@[simp] theorem matrix_apply (H : X → Ω → Bool) (iT : T → X) (iV : V → X)
    (iB : B → X) (iD : Δ → Ω) (Sdup : ℕ)
    (r : Rows X T V B) (c : Columns Ω Δ Sdup) :
    matrix H iT iV iB iD Sdup r c =
      H (rowForget iT iV iB r) (columnForget iD c) := rfl

/-- The paper uses `N`, the literal transpose of the labelled blow-up. -/
def transposedMatrix (H : X → Ω → Bool) (iT : T → X) (iV : V → X) (iB : B → X)
    (iD : Δ → Ω) (Sdup : ℕ) : Columns Ω Δ Sdup → Rows X T V B → Bool :=
  fun c r => matrix H iT iV iB iD Sdup r c

@[simp] theorem transposedMatrix_apply (H : X → Ω → Bool) (iT : T → X)
    (iV : V → X) (iB : B → X) (iD : Δ → Ω) (Sdup : ℕ)
    (c : Columns Ω Δ Sdup) (r : Rows X T V B) :
    transposedMatrix H iT iV iB iD Sdup c r =
      H (rowForget iT iV iB r) (columnForget iD c) := rfl

variable [Nonempty X] [Nonempty T] [Nonempty V] [Nonempty B]
  [Nonempty Ω] [Nonempty Δ]

def rowRepresentative (x : X) : Rows X T V B :=
  representative (rowSupport X T V B) rowWeight 0 id
    (copies_pos _ _ rowWeight_pos (rowSupport_card_pos X T V B) 0) x

def columnRepresentative (Sdup : ℕ) (hSdup : 0 < Sdup) (y : Ω) : Columns Ω Δ Sdup :=
  (representative (columnSupport Ω Δ) columnWeight 0 id
    (copies_pos _ _ columnWeight_pos (columnSupport_card_pos Ω Δ) 0) y, ⟨0, hSdup⟩)

@[simp] theorem rowForget_representative (iT : T → X) (iV : V → X) (iB : B → X)
    (x : X) :
    rowForget iT iV iB (rowRepresentative (T := T) (V := V) (B := B) x) = x := rfl

@[simp] theorem columnForget_representative (iD : Δ → Ω) (Sdup : ℕ)
    (hSdup : 0 < Sdup) (y : Ω) :
    columnForget iD (columnRepresentative (Δ := Δ) Sdup hSdup y) = y := rfl

theorem rowForget_surjective (iT : T → X) (iV : V → X) (iB : B → X) :
    Function.Surjective (rowForget iT iV iB) := by
  intro x
  exact ⟨rowRepresentative x, rfl⟩

theorem columnForget_surjective (iD : Δ → Ω) (Sdup : ℕ) (hSdup : 0 < Sdup) :
    Function.Surjective (columnForget (Sdup := Sdup) iD) := by
  intro y
  exact ⟨columnRepresentative Sdup hSdup y, rfl⟩

/-- Exact communication preservation for the TWO-column-support matrix. -/
theorem D_matrix (H : X → Ω → Bool) (iT : T → X) (iV : V → X) (iB : B → X)
    (iD : Δ → Ω) (Sdup : ℕ) (hSdup : 0 < Sdup) :
    D (matrix H iT iV iB iD Sdup) = D H := by
  exact D_forget_eq H (rowForget iT iV iB) (columnForget iD)
    rowRepresentative (columnRepresentative Sdup hSdup)
    (rowForget_representative iT iV iB)
    (columnForget_representative iD Sdup hSdup)

/-- Transposition changes orientation but not the communication cost. -/
theorem D_transposedMatrix (H : X → Ω → Bool) (iT : T → X) (iV : V → X)
    (iB : B → X) (iD : Δ → Ω) (Sdup : ℕ) (hSdup : 0 < Sdup) :
    D (transposedMatrix H iT iV iB iD Sdup) = D H := by
  exact (NPCC.comp_transpose (matrix H iT iV iB iD Sdup)).trans
    (D_matrix H iT iV iB iD Sdup hSdup)

end CurrentMatrix

end EthInapproximability.CurrentPaper.WeightedDuplication
