import EthInapproximability.CurrentPaper.Construction
import NPCC.Upper

/-!
# The literal matrix of the current exact-NP reduction

Source: v8 `03-exact-hardness.tex`, `lem:exact-source`,
`eq:exact-P`, `eq:exact-duplicate-labels`, `eq:exact-QT`,
`eq:exact-H-carriers`, `eq:exact-H-template`, `eq:exact-H-vectors`,
and `eq:exact-canonical-columns`; `E-exact-details.tex` and
`G-exact-control.tex` retain the separate balancedness and protocol-control
obligations. Families here are indexed accessors, not sets of distinct tuples.

This module does not replace either sampler by an existence axiom, nor claim
the protocol lower bound or a polynomial-time NP reduction. It constructs the
actual matrix, with exactly three auxiliary bits and four bins.
-/

namespace EthInapproximability.CurrentPaper.ExactConstruction

open Workspace.Types.CommComplexity
open scoped BigOperators

abbrev width (a : ℕ) := 2 ^ a
abbrev prefixLength (a : ℕ) := Construction.qOne a

theorem two_le_prefix (a : ℕ) (ha : 2 ≤ a) : 2 ≤ prefixLength a := by
  have h : 4 ≤ 2 ^ a := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) ha
  unfold prefixLength Construction.qOne
  omega

/-- The two additional labels name the first and second original rows. -/
def duplicateLabel (a : ℕ) (ha : 2 ≤ a) (i : Fin (width a)) : Fin (prefixLength a) :=
  if hi : i.val < prefixLength a then ⟨i.val, hi⟩
  else if i.val = prefixLength a then ⟨0, by have := two_le_prefix a ha; omega⟩
  else ⟨1, by have := two_le_prefix a ha; omega⟩

def originalLabel (a : ℕ) (ha : 2 ≤ a) (i : Fin (prefixLength a)) : Fin (width a) :=
  ⟨i.val, by
    have h : prefixLength a + 2 = width a := Construction.qOne_add_two a (by omega)
    omega⟩

@[simp] theorem duplicateLabel_original (a : ℕ) (ha : 2 ≤ a) (i : Fin (prefixLength a)) :
    duplicateLabel a ha (originalLabel a ha i) = i := by
  simp [duplicateLabel, originalLabel, i.isLt]

theorem duplicateLabel_surjective (a : ℕ) (ha : 2 ≤ a) :
    Function.Surjective (duplicateLabel a ha) :=
  fun i => ⟨originalLabel a ha i, duplicateLabel_original a ha i⟩

theorem duplicateLabel_first_extra (a : ℕ) (ha : 2 ≤ a) :
    duplicateLabel a ha
      ⟨prefixLength a, by
        have h : prefixLength a + 2 = width a := Construction.qOne_add_two a (by omega)
        omega⟩ =
      ⟨0, by have := two_le_prefix a ha; omega⟩ := by
  simp [duplicateLabel]

theorem duplicateLabel_second_extra (a : ℕ) (ha : 2 ≤ a) :
    duplicateLabel a ha
      ⟨prefixLength a + 1, by
        have h : prefixLength a + 2 = width a := Construction.qOne_add_two a (by omega)
        omega⟩ =
      ⟨1, by have := two_le_prefix a ha; omega⟩ := by
  simp [duplicateLabel]

abbrev FirstFamily (a N₁ : ℕ) := Fin N₁ → Fin (prefixLength a + 3) → Bool
abbrev SecondFamily (a d N₂ : ℕ) := Fin N₂ → Fin d → Fin (width a)
abbrev Selectors (d N₁ : ℕ) := Fin 4 → Fin d × Fin N₁
abbrev Rows (N₂ n : ℕ) := (Fin 4 × Fin N₂) ⊕ Fin n
abbrev Columns (d N₁ : ℕ) := (Fin 3 → Bool) × Selectors d N₁

def prefixCoordinate (a : ℕ) (i : Fin (prefixLength a)) : Fin (prefixLength a + 3) :=
  Fin.castAdd 3 i

def tailCoordinate (a : ℕ) (i : Fin 3) : Fin (prefixLength a + 3) :=
  Fin.natAdd (prefixLength a) i

def firstMatrix {a N₁ : ℕ} (C₁ : FirstFamily a N₁) :
    Fin (prefixLength a) → Fin N₁ → Bool :=
  fun i ℓ => C₁ ℓ (prefixCoordinate a i)

def duplicatedFirstMatrix {a N₁ : ℕ} (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) :
    Fin (width a) → Fin N₁ → Bool :=
  fun i ℓ => firstMatrix C₁ (duplicateLabel a ha i) ℓ

def secondMatrix {a d N₁ N₂ : ℕ} (ha : 2 ≤ a) (C₁ : FirstFamily a N₁)
    (C₂ : SecondFamily a d N₂) : (Fin d × Fin N₁) → Fin N₂ → Bool :=
  fun r z => duplicatedFirstMatrix ha C₁ (C₂ z r.1) r.2

def thirdMatrix {a d N₁ N₂ : ℕ} (ha : 2 ≤ a) (C₁ : FirstFamily a N₁)
    (C₂ : SecondFamily a d N₂) : (Fin 4 × Fin N₂) → Selectors d N₁ → Bool :=
  fun r c => secondMatrix ha C₁ C₂ (c r.1) r.2

def aligned {d N₁ : ℕ} (c : Columns d N₁) : Prop :=
  ∀ p, (c.2 p).1 = (c.2 0).1

instance alignedDecidable {d N₁ : ℕ} (c : Columns d N₁) : Decidable (aligned c) := by
  unfold aligned
  infer_instance

/-- Endpoint indices are their ranks in the public vector order. -/
abbrev activeSlot {n d : ℕ} (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (α : Fin d) (i : {i : Fin n // v i α = true}) : Fin 2 :=
  Construction.activeSlot v cap α i

def vectorEntry {n d N₁ : ℕ} (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (i : Fin n) (c : Columns d N₁) : Bool :=
  if aligned c then
    if hi : v i (c.2 0).1 = true then
      c.1 (Fin.castAdd 1 (activeSlot v cap (c.2 0).1 ⟨i, hi⟩))
    else c.1 2
  else c.1 2

def matrix {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a) (C₁ : FirstFamily a N₁)
    (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    Rows N₂ n → Columns d N₁ → Bool
  | .inl r, c => thirdMatrix ha C₁ C₂ r c.2
  | .inr i, c => vectorEntry v cap i c

/-- All four selectors and the three tail bits come from one labelled string. -/
def diagonal {a d N₁ : ℕ} (C₁ : FirstFamily a N₁)
    (α : Fin d) (ℓ : Fin N₁) : Columns d N₁ :=
  (fun j => C₁ ℓ (tailCoordinate a j), fun _ => (α, ℓ))

theorem diagonal_injective {a d N₁ : ℕ} (C₁ : FirstFamily a N₁) :
    Function.Injective (fun r : Fin d × Fin N₁ => diagonal C₁ r.1 r.2) := by
  intro r s h
  exact congrArg (fun c : Columns d N₁ => c.2 0) h

@[simp] theorem diagonal_aligned {a d N₁ : ℕ} (C₁ : FirstFamily a N₁)
    (α : Fin d) (ℓ : Fin N₁) : aligned (diagonal C₁ α ℓ) := fun _ => rfl

@[simp] theorem matrix_template_diagonal {a d N₁ N₂ n : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (p : Fin 4) (z : Fin N₂) (α : Fin d) (ℓ : Fin N₁) :
    matrix ha C₁ C₂ v cap (.inl (p, z)) (diagonal C₁ α ℓ) =
      C₁ ℓ (prefixCoordinate a (duplicateLabel a ha (C₂ z α))) := rfl

theorem matrix_active_diagonal {a d N₁ N₂ n : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (i : Fin n) (α : Fin d) (ℓ : Fin N₁) (hi : v i α = true) :
    matrix ha C₁ C₂ v cap (.inr i) (diagonal C₁ α ℓ) =
      C₁ ℓ (tailCoordinate a (Fin.castAdd 1 (activeSlot v cap α ⟨i, hi⟩))) := by
  simp [matrix, vectorEntry, diagonal, aligned, hi]

theorem matrix_inactive_diagonal {a d N₁ N₂ n : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (i : Fin n) (α : Fin d) (ℓ : Fin N₁) (hi : v i α = false) :
    matrix ha C₁ C₂ v cap (.inr i) (diagonal C₁ α ℓ) =
      C₁ ℓ (tailCoordinate a 2) := by
  simp [matrix, vectorEntry, diagonal, aligned, hi]

theorem matrix_nonaligned {a d N₁ N₂ n : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (i : Fin n) (c : Columns d N₁) (h : ¬ aligned c) :
    matrix ha C₁ C₂ v cap (.inr i) c = c.1 2 := by
  simp [matrix, vectorEntry, h]

@[simp] theorem card_rows (N₂ n : ℕ) : Fintype.card (Rows N₂ n) = 4 * N₂ + n := by
  simp [Rows]

@[simp] theorem card_columns (d N₁ : ℕ) :
    Fintype.card (Columns d N₁) = 8 * (d * N₁) ^ 4 := by
  simp [Columns, Selectors]

theorem table_size (d N₁ N₂ n : ℕ) :
    Fintype.card (Rows N₂ n) * Fintype.card (Columns d N₁) =
      (4 * N₂ + n) * 8 * (d * N₁) ^ 4 := by
  rw [card_rows, card_columns]
  ring

/-- The manuscript's conservative table-size bound, conditional on the two
sampler-size estimates, which remain separate Lean obligations. -/
theorem table_size_polynomial (d N₁ N₂ n : ℕ)
    (hN₁ : N₁ ≤ d ^ 300) (hN₂ : N₂ ≤ d ^ 100) :
    Fintype.card (Rows N₂ n) * Fintype.card (Columns d N₁) ≤
      8 * (4 * d ^ 100 + n) * d ^ 1204 := by
  rw [table_size]
  calc
    (4 * N₂ + n) * 8 * (d * N₁) ^ 4 ≤
        (4 * d ^ 100 + n) * 8 * (d * d ^ 300) ^ 4 := by gcongr
    _ = 8 * (4 * d ^ 100 + n) * d ^ 1204 := by
      rw [mul_pow, ← pow_mul, ← pow_add]
      ring

theorem D_duplicatedFirstMatrix {a N₁ : ℕ} (ha : 2 ≤ a)
    (C₁ : FirstFamily a N₁) : D (duplicatedFirstMatrix ha C₁) = D (firstMatrix C₁) := by
  apply ParameterizedNP.DenseStageFourOpening.D_forget_eq
    (firstMatrix C₁) (duplicateLabel a ha) id (originalLabel a ha) id
  · exact duplicateLabel_original a ha
  · intro x; rfl

theorem D_firstMatrix_le {a N₁ : ℕ} (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) :
    D (firstMatrix C₁) ≤ a + 1 := by
  apply NPCC.comp_le_of_row_types_succ _ a (originalLabel a ha)
  intro i j h
  have hv := congrArg Fin.val h
  have hij : i = j := Fin.ext hv
  rw [hij]

theorem D_duplicatedFirstMatrix_le {a N₁ : ℕ} (ha : 2 ≤ a)
    (C₁ : FirstFamily a N₁) : D (duplicatedFirstMatrix ha C₁) ≤ a + 1 := by
  rw [D_duplicatedFirstMatrix ha C₁]
  exact D_firstMatrix_le ha C₁

theorem D_thirdMatrix_le_matrix {a d N₁ N₂ n : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    D (thirdMatrix ha C₁ C₂) ≤ D (matrix ha C₁ C₂ v cap) :=
  ParameterizedNP.DenseStageFourOpening.D_precomp_le (matrix ha C₁ C₂ v cap)
    Sum.inl (fun c => (fun _ => false, c))

def bin {N₂ n : ℕ} (σ : Fin n → Fin 4) : Rows N₂ n → Fin 4
  | .inl r => r.1
  | .inr i => σ i

/-- A feasible packing has at most one active vector in each bin and coordinate. -/
def Feasible {n d : ℕ} (v : Fin n → Fin d → Bool) (σ : Fin n → Fin 4) : Prop :=
  ∀ p α, (Finset.univ.filter (fun i => σ i = p ∧ v i α = true)).card ≤ 1

theorem Feasible.active_unique {n d : ℕ} {v : Fin n → Fin d → Bool}
    {σ : Fin n → Fin 4} (h : Feasible v σ) (p : Fin 4) (α : Fin d)
    (i j : Fin n) (hi : σ i = p) (hj : σ j = p)
    (hvi : v i α = true) (hvj : v j α = true) : i = j := by
  apply Finset.card_le_one.mp (h p α)
  · simp [hi, hvi]
  · simp [hj, hvj]

theorem vectorEntry_pinned_inactive {n d N₁ : ℕ} (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (i : Fin n) (p : Fin 4) (α : Fin d) (c : Columns d N₁)
    (hc : (c.2 p).1 = α) (hi : v i α = false) : vectorEntry v cap i c = c.1 2 := by
  by_cases hal : aligned c
  · have heq : (c.2 0).1 = α := (hal p).symm.trans hc
    simp [vectorEntry, hal, heq, hi]
  · simp [vectorEntry, hal]

def yesClass {a d N₂ n : ℕ} (ha : 2 ≤ a) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (α : Fin d) : Rows N₂ n → Fin (width a)
  | .inl r => originalLabel a ha (duplicateLabel a ha (C₂ r.2 α))
  | .inr i => ⟨prefixLength a + (if v i α = true then 1 else 0), by
      have h : prefixLength a + 2 = width a := Construction.qOne_add_two a (by omega)
      split <;> omega⟩

theorem yes_local_upper {a d N₁ N₂ n : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (σ : Fin n → Fin 4) (hf : Feasible v σ) (p : Fin 4) (α : Fin d) :
    D (fun (r : {r : Rows N₂ n // bin σ r = p})
      (c : {c : Columns d N₁ // (c.2 p).1 = α}) => matrix ha C₁ C₂ v cap r.val c.val)
      ≤ a + 1 := by
  classical
  apply NPCC.comp_le_of_row_types_succ _ a (fun r => yesClass ha C₂ v α r.val)
  intro r s h
  have hb₁ := r.property
  have hb₂ := s.property
  have hv := congrArg Fin.val h
  funext c
  have hc := c.property
  rcases hr : r.val with r₀ | i <;> rcases hs : s.val with s₀ | j
  · rw [hr] at hb₁ hv
    rw [hs] at hb₂ hv
    change r₀.1 = p at hb₁
    change s₀.1 = p at hb₂
    change (duplicateLabel a ha (C₂ r₀.2 α)).val =
      (duplicateLabel a ha (C₂ s₀.2 α)).val at hv
    have ht := Fin.ext hv
    simp only [matrix, thirdMatrix, secondMatrix, duplicatedFirstMatrix, firstMatrix]
    rw [hb₁, hb₂, hc, ht]
  · rw [hr, hs] at hv
    change (duplicateLabel a ha (C₂ r₀.2 α)).val =
      prefixLength a + (if v j α = true then 1 else 0) at hv
    have ht := (duplicateLabel a ha (C₂ r₀.2 α)).isLt
    split at hv <;> omega
  · rw [hr, hs] at hv
    change prefixLength a + (if v i α = true then 1 else 0) =
      (duplicateLabel a ha (C₂ s₀.2 α)).val at hv
    have ht := (duplicateLabel a ha (C₂ s₀.2 α)).isLt
    split at hv <;> omega
  · rw [hr] at hb₁ hv
    rw [hs] at hb₂ hv
    change σ i = p at hb₁
    change σ j = p at hb₂
    change prefixLength a + (if v i α = true then 1 else 0) =
      prefixLength a + (if v j α = true then 1 else 0) at hv
    by_cases hi : v i α = true <;> by_cases hj : v j α = true
    · rw [hf.active_unique p α i j hb₁ hb₂ hi hj]
    · simp [hi, hj] at hv
    · simp [hi, hj] at hv
    · exact (vectorEntry_pinned_inactive v cap i p α c.val hc
        (Bool.eq_false_iff.mpr hi)).trans
        (vectorEntry_pinned_inactive v cap j p α c.val hc
          (Bool.eq_false_iff.mpr hj)).symm

/-- The paper's three-phase YES protocol, with all answer bits charged. -/
theorem D_matrix_le_of_feasible {a r N₁ N₂ n : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a (2 ^ r) N₂)
    (v : Fin n → Fin (2 ^ r) → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (σ : Fin n → Fin 4) (hf : Feasible v σ) :
    D (matrix ha C₁ C₂ v cap) ≤ 2 + r + (a + 1) := by
  have hbound : D (matrix ha C₁ C₂ v cap) ≤ 2 + (r + (a + 1)) := by
    apply NPCC.comp_le_partition _ 2 (r + (a + 1)) (bin σ)
    intro p
    apply NPCC.comp_le_partition_cols _ r (a + 1) (fun c => (c.2 p).1)
    intro α
    exact yes_local_upper ha C₁ C₂ v cap σ hf p α
  omega

def anyClass {a d N₂ n : ℕ} (ha : 2 ≤ a) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (α : Fin d) : Rows N₂ n → Fin (2 ^ (a + 1))
  | .inl r => ⟨(duplicateLabel a ha (C₂ r.2 α)).val, by
      have hi := (duplicateLabel a ha (C₂ r.2 α)).isLt
      have h : prefixLength a + 2 = 2 ^ a := Construction.qOne_add_two a (by omega)
      rw [pow_succ]
      omega⟩
  | .inr i => ⟨prefixLength a +
      (if hi : v i α = true then (activeSlot v cap α ⟨i, hi⟩).val else 2), by
      have h : prefixLength a + 2 = 2 ^ a := Construction.qOne_add_two a (by omega)
      have hp : 0 < 2 ^ a := pow_pos (by omega) _
      rw [pow_succ]
      split
      · have hi := (activeSlot v cap α ⟨i, ‹v i α = true›⟩).isLt
        omega
      · omega⟩

theorem arbitrary_local_upper {a d N₁ N₂ n : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (σ : Fin n → Fin 4) (p : Fin 4) (α : Fin d) :
    D (fun (r : {r : Rows N₂ n // bin σ r = p})
      (c : {c : Columns d N₁ // (c.2 p).1 = α}) => matrix ha C₁ C₂ v cap r.val c.val)
      ≤ a + 2 := by
  classical
  have hbound : D (fun (r : {r : Rows N₂ n // bin σ r = p})
      (c : {c : Columns d N₁ // (c.2 p).1 = α}) => matrix ha C₁ C₂ v cap r.val c.val)
      ≤ (a + 1) + 1 := by
    apply NPCC.comp_le_of_row_types_succ _ (a + 1) (fun r => anyClass ha C₂ v cap α r.val)
    intro r s h
    have hb₁ := r.property
    have hb₂ := s.property
    have hv := congrArg Fin.val h
    funext c
    have hc := c.property
    rcases hr : r.val with r₀ | i <;> rcases hs : s.val with s₀ | j
    · rw [hr] at hb₁ hv
      rw [hs] at hb₂ hv
      change r₀.1 = p at hb₁
      change s₀.1 = p at hb₂
      change (duplicateLabel a ha (C₂ r₀.2 α)).val =
        (duplicateLabel a ha (C₂ s₀.2 α)).val at hv
      have ht := Fin.ext hv
      simp only [matrix, thirdMatrix, secondMatrix, duplicatedFirstMatrix, firstMatrix]
      rw [hb₁, hb₂, hc, ht]
    · rw [hr, hs] at hv
      change (duplicateLabel a ha (C₂ r₀.2 α)).val = prefixLength a +
        (if hj : v j α = true then (activeSlot v cap α ⟨j, hj⟩).val else 2) at hv
      have ht := (duplicateLabel a ha (C₂ r₀.2 α)).isLt
      split at hv <;> omega
    · rw [hr, hs] at hv
      change prefixLength a +
        (if hi : v i α = true then (activeSlot v cap α ⟨i, hi⟩).val else 2) =
        (duplicateLabel a ha (C₂ s₀.2 α)).val at hv
      have ht := (duplicateLabel a ha (C₂ s₀.2 α)).isLt
      split at hv <;> omega
    · rw [hr, hs] at hv
      change prefixLength a +
        (if hi : v i α = true then (activeSlot v cap α ⟨i, hi⟩).val else 2) =
        prefixLength a +
        (if hj : v j α = true then (activeSlot v cap α ⟨j, hj⟩).val else 2) at hv
      by_cases hi : v i α = true <;> by_cases hj : v j α = true
      · rw [dif_pos hi, dif_pos hj] at hv
        have hslt : activeSlot v cap α ⟨i, hi⟩ = activeSlot v cap α ⟨j, hj⟩ :=
          Fin.ext (by omega)
        have hij : i = j := congrArg Subtype.val
          (Construction.activeSlot_injective v cap α hslt)
        rw [hij]
      · rw [dif_pos hi, dif_neg hj] at hv
        have ht := (activeSlot v cap α ⟨i, hi⟩).isLt
        omega
      · rw [dif_neg hi, dif_pos hj] at hv
        have ht := (activeSlot v cap α ⟨j, hj⟩).isLt
        omega
      · exact (vectorEntry_pinned_inactive v cap i p α c.val hc
          (Bool.eq_false_iff.mpr hi)).trans
          (vectorEntry_pinned_inactive v cap j p α c.val hc
            (Bool.eq_false_iff.mpr hj)).symm
  omega

/-- Every source, not just a feasible source, admits the paper's `K+1` protocol. -/
theorem D_matrix_le_unconditional {a r N₁ N₂ n : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a (2 ^ r) N₂)
    (v : Fin n → Fin (2 ^ r) → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    D (matrix ha C₁ C₂ v cap) ≤ 2 + r + (a + 2) := by
  have hbound : D (matrix ha C₁ C₂ v cap) ≤ 2 + (r + (a + 2)) := by
    apply NPCC.comp_le_partition _ 2 (r + (a + 2)) (bin (fun _ => 0))
    intro p
    apply NPCC.comp_le_partition_cols _ r (a + 2) (fun c => (c.2 p).1)
    intro α
    exact arbitrary_local_upper ha C₁ C₂ v cap (fun _ => 0) p α
  omega

/-- The first sampled interlace is indexing, restricted to its original rows. -/
theorem firstMatrix_relaxed {a N₁ : ℕ} (C₁ : FirstFamily a N₁) :
    firstMatrix C₁ = fun i ℓ =>
      NPCC.relaxedInterlace (fun (_ : Unit) (b : Bool) => b) C₁
        (prefixCoordinate a i, ()) ℓ := rfl

theorem secondMatrix_relaxed {a d N₁ N₂ : ℕ} (ha : 2 ≤ a)
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂) :
    secondMatrix ha C₁ C₂ =
      NPCC.relaxedInterlace (fun ℓ i => duplicatedFirstMatrix ha C₁ i ℓ) C₂ := rfl

theorem thirdMatrix_interlace {a d N₁ N₂ : ℕ} (ha : 2 ≤ a)
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂) :
    thirdMatrix ha C₁ C₂ =
      Workspace.Types.Interlace.interlaceFun (fun z r => secondMatrix ha C₁ C₂ r z) 4 := rfl

section FiveCopies

/-- A graph is supplied by its public edge list, with two distinct endpoints.
The five copies have disjoint coordinate sets; equal vectors retain labels. -/
def fiveCopyVectors {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (row : Fin 5 × Fin n) (coord : Fin 5 × Fin d) : Bool :=
  decide (row.1 = coord.1 ∧ ∃ j : Fin 2, row.2 = e coord.2 j)

theorem fiveCopy_atMostTwo {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (coord : Fin 5 × Fin d) :
    (Finset.univ.filter (fun row => fiveCopyVectors e row coord = true)).card ≤ 2 := by
  have hsub : Finset.univ.filter (fun row => fiveCopyVectors e row coord = true) ⊆
      Finset.univ.image (fun j : Fin 2 => (coord.1, e coord.2 j)) := by
    intro row hrow
    have h := (Finset.mem_filter.mp hrow).2
    simp only [fiveCopyVectors, decide_eq_true_eq] at h
    rcases h with ⟨hcopy, j, hj⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, Prod.ext hcopy.symm hj.symm⟩
  calc
    _ ≤ (Finset.univ.image (fun j : Fin 2 => (coord.1, e coord.2 j))).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 2)).card := Finset.card_image_le
    _ = 2 := by simp

theorem fiveCopy_badTriplet {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hinj : ∀ α, Function.Injective (e α))
    (hbad : ∀ colour : Fin n → Fin 4,
      ∃ α : Fin d, colour (e α 0) = colour (e α 1))
    (σ : (Fin 5 × Fin n) → Fin 4) :
    ∃ (i j k : Fin 5 × Fin n) (coord : Fin 5 × Fin d),
      i ≠ j ∧ σ i = σ j ∧ σ i = σ k ∧
      fiveCopyVectors e i coord = true ∧ fiveCopyVectors e j coord = true ∧
      fiveCopyVectors e k coord = false := by
  classical
  have eachCopy : ∀ c : Fin 5, ∃ α : Fin d,
      σ (c, e α 0) = σ (c, e α 1) := fun c => hbad (fun v => σ (c, v))
  choose edge hedge using eachCopy
  obtain ⟨c₁, c₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun c : Fin 5 => σ (c, e (edge c) 0)) (by simp)
  refine ⟨(c₁, e (edge c₁) 0), (c₁, e (edge c₁) 1),
    (c₂, e (edge c₂) 0), (c₁, edge c₁), ?_, hedge c₁, heq, ?_, ?_, ?_⟩
  · intro h
    have h01 : (0 : Fin 2) = 1 := hinj _ (congrArg Prod.snd h)
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  · simp only [fiveCopyVectors, decide_eq_true_eq]
    exact ⟨True.intro, 0, rfl⟩
  · simp only [fiveCopyVectors, decide_eq_true_eq]
    exact ⟨True.intro, 1, rfl⟩
  · simp [fiveCopyVectors, Ne.symm hne]

theorem fiveCopy_yesPartition {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (colour : Fin n → Fin 4)
    (hproper : ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1)) :
    ∀ (p : Fin 4) (coord : Fin 5 × Fin d),
      (Finset.univ.filter (fun row =>
        colour row.2 = p ∧ fiveCopyVectors e row coord = true)).card ≤ 1 := by
  intro p coord
  apply Finset.card_le_one.mpr
  intro row hrow row' hrow'
  obtain ⟨hcolour, hactive⟩ := (Finset.mem_filter.mp hrow).2
  obtain ⟨hcolour', hactive'⟩ := (Finset.mem_filter.mp hrow').2
  simp only [fiveCopyVectors, decide_eq_true_eq] at hactive hactive'
  obtain ⟨hc, j, hj⟩ := hactive
  obtain ⟨hc', j', hj'⟩ := hactive'
  have hsameColour : colour (e coord.2 j) = colour (e coord.2 j') := by
    rw [← hj, ← hj', hcolour, hcolour']
  have hsameJ : j = j' := by
    fin_cases j <;> fin_cases j'
    · rfl
    · exact False.elim (hproper _ hsameColour)
    · exact False.elim (hproper _ hsameColour.symm)
    · rfl
  exact Prod.ext (hc.trans hc'.symm) (by rw [hj, hj', hsameJ])

/-- Copy-major labels give one fixed public order for the active-slot ranks. -/
def encodedFiveCopyVectors {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (i : Fin (5 * n)) (α : Fin (5 * d)) : Bool :=
  fiveCopyVectors e (finProdFinEquiv.symm i) (finProdFinEquiv.symm α)

theorem encodedFiveCopy_atMostTwo {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (α : Fin (5 * d)) :
    (Construction.activeItems (encodedFiveCopyVectors e) α).card ≤ 2 := by
  let coord : Fin 5 × Fin d := finProdFinEquiv.symm α
  have hsub : Construction.activeItems (encodedFiveCopyVectors e) α ⊆
      Finset.univ.image (fun j : Fin 2 => finProdFinEquiv (coord.1, e coord.2 j)) := by
    intro row hrow
    have h := (Finset.mem_filter.mp hrow).2
    change fiveCopyVectors e (finProdFinEquiv.symm row) coord = true at h
    simp only [fiveCopyVectors, decide_eq_true_eq] at h
    rcases h with ⟨hcopy, j, hj⟩
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    apply finProdFinEquiv.symm.injective
    simp only [Equiv.symm_apply_apply]
    exact Prod.ext hcopy.symm hj.symm
  calc
    _ ≤ (Finset.univ.image (fun j : Fin 2 => finProdFinEquiv (coord.1, e coord.2 j))).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 2)).card := Finset.card_image_le
    _ = 2 := by simp

theorem encodedFiveCopy_badTriplet {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hinj : ∀ α, Function.Injective (e α))
    (hbad : ∀ colour : Fin n → Fin 4,
      ∃ α : Fin d, colour (e α 0) = colour (e α 1))
    (σ : Fin (5 * n) → Fin 4) :
    ∃ (i j k : Fin (5 * n)) (α : Fin (5 * d)),
      i ≠ j ∧ σ i = σ j ∧ σ i = σ k ∧
      encodedFiveCopyVectors e i α = true ∧ encodedFiveCopyVectors e j α = true ∧
      encodedFiveCopyVectors e k α = false := by
  obtain ⟨i, j, k, α, hij, hσij, hσik, hi, hj, hk⟩ :=
    fiveCopy_badTriplet e hinj hbad (fun i => σ (finProdFinEquiv i))
  refine ⟨finProdFinEquiv i, finProdFinEquiv j, finProdFinEquiv k,
    finProdFinEquiv α, ?_, hσij, hσik, ?_, ?_, ?_⟩
  · exact fun h => hij (finProdFinEquiv.injective h)
  · simpa [encodedFiveCopyVectors] using hi
  · simpa [encodedFiveCopyVectors] using hj
  · simpa [encodedFiveCopyVectors] using hk

theorem encodedFiveCopy_feasible {n d : ℕ} (e : Fin d → Fin 2 → Fin n)
    (colour : Fin n → Fin 4)
    (hproper : ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1)) :
    Feasible (encodedFiveCopyVectors e) (fun i => colour (finProdFinEquiv.symm i).2) := by
  intro p α
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply finProdFinEquiv.symm.injective
  apply Finset.card_le_one.mp (fiveCopy_yesPartition e colour hproper p
    (finProdFinEquiv.symm α))
  · simpa [encodedFiveCopyVectors] using hi
  · simpa [encodedFiveCopyVectors] using hj

/-- Zero-coordinate extension retains row labels and order. If `D < d` this
also defines truncation; preservation of NO witnesses requires `d ≤ D`. -/
def padVectors {n d D : ℕ} (v : Fin n → Fin d → Bool)
    (i : Fin n) (α : Fin D) : Bool :=
  if h : α.val < d then v i ⟨α.val, h⟩ else false

@[simp] theorem padVectors_original {n d D : ℕ} (v : Fin n → Fin d → Bool)
    (hd : d ≤ D) (i : Fin n) (α : Fin d) :
    padVectors (D := D) v i (Fin.castLE hd α) = v i α := by
  simp [padVectors, α.isLt]

theorem padVectors_cap {n d D : ℕ} (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    ∀ α, (Construction.activeItems (padVectors (D := D) v) α).card ≤ 2 := by
  intro α
  by_cases hα : α.val < d
  · simpa [Construction.activeItems, padVectors, hα] using cap ⟨α.val, hα⟩
  · simp [Construction.activeItems, padVectors, hα]

theorem padVectors_feasible {n d D : ℕ} (v : Fin n → Fin d → Bool)
    (σ : Fin n → Fin 4) (hf : Feasible v σ) :
    Feasible (padVectors (D := D) v) σ := by
  intro p α
  by_cases hα : α.val < d
  · simpa [padVectors, hα] using hf p ⟨α.val, hα⟩
  · simp [padVectors, hα]

/-- The literal five-copy source. The intended padding instantiation requires
`5*d ≤ D`, explicitly carried by `sourceVectors_badTriplet`. -/
def sourceVectors {n d : ℕ} (D : ℕ) (e : Fin d → Fin 2 → Fin n) :
    Fin (5 * n) → Fin D → Bool := padVectors (encodedFiveCopyVectors e)

theorem sourceVectors_cap {n d : ℕ} (D : ℕ) (e : Fin d → Fin 2 → Fin n) :
    ∀ α, (Construction.activeItems (sourceVectors D e) α).card ≤ 2 :=
  padVectors_cap (encodedFiveCopyVectors e) (encodedFiveCopy_atMostTwo e)

theorem sourceVectors_feasible {n d : ℕ} (D : ℕ) (e : Fin d → Fin 2 → Fin n)
    (colour : Fin n → Fin 4)
    (hproper : ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1)) :
    Feasible (sourceVectors D e) (fun i => colour (finProdFinEquiv.symm i).2) :=
  padVectors_feasible _ _ (encodedFiveCopy_feasible e colour hproper)

theorem sourceVectors_badTriplet {n d D : ℕ} (e : Fin d → Fin 2 → Fin n)
    (hD : 5 * d ≤ D) (hinj : ∀ α, Function.Injective (e α))
    (hbad : ∀ colour : Fin n → Fin 4,
      ∃ α : Fin d, colour (e α 0) = colour (e α 1))
    (σ : Fin (5 * n) → Fin 4) :
    ∃ (i j k : Fin (5 * n)) (α : Fin D),
      i ≠ j ∧ σ i = σ j ∧ σ i = σ k ∧
      sourceVectors D e i α = true ∧ sourceVectors D e j α = true ∧
      sourceVectors D e k α = false := by
  obtain ⟨i, j, k, α, hij, hσij, hσik, hi, hj, hk⟩ :=
    encodedFiveCopy_badTriplet e hinj hbad σ
  refine ⟨i, j, k, Fin.castLE hD α, hij, hσij, hσik, ?_, ?_, ?_⟩
  · simpa [sourceVectors] using hi
  · simpa [sourceVectors] using hj
  · simpa [sourceVectors] using hk

/-- The YES bound already applies to the constructed and padded graph source. -/
theorem D_sourceMatrix_le {a r N₁ N₂ n d : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a (2 ^ r) N₂)
    (e : Fin d → Fin 2 → Fin n) (colour : Fin n → Fin 4)
    (hproper : ∀ α : Fin d, colour (e α 0) ≠ colour (e α 1)) :
    D (matrix ha C₁ C₂ (sourceVectors (2 ^ r) e) (sourceVectors_cap (2 ^ r) e))
      ≤ 2 + r + (a + 1) :=
  D_matrix_le_of_feasible ha C₁ C₂ _ _ _ (sourceVectors_feasible _ e colour hproper)

end FiveCopies

end EthInapproximability.CurrentPaper.ExactConstruction
