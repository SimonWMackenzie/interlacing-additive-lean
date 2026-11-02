import Paper2.SourceMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Rank of the concrete source construction

Source: Paper 2, frozen `2026-09-22-protocol-labels-v12`,
`sections/05-amplifier-proof.tex`, lines 24--40, equation
`eq:amplifier-rank`.  The row-stacking bounds below express the actual
row-space argument: stacking blocks adds, rather than multiplies, their ranks.
No communication or promise assumption is involved.
-/

namespace Paper2

open scoped BigOperators
open RankLeaves

variable {I X Y A B : Type*}

/-- Stack finitely many row blocks with a shared column set. -/
def stackedRows (F : I → X → Y → Bool) : (I × X) → Y → Bool :=
  fun ix y => F ix.1 ix.2 y

/-- The rank of a stack is at most the sum of its block ranks, including
empty blocks and an empty family. -/
theorem stackedRows_rank_le [Fintype I] [Finite X] [Fintype Y]
    (F : I → X → Y → Bool) :
    (realMatrix (stackedRows F)).rank ≤ ∑ i, (realMatrix (F i)).rank := by
  classical
  let V : I → Submodule ℝ (Y → ℝ) := fun i =>
    Submodule.span ℝ (Set.range (realMatrix (F i)).row)
  let L : ((i : I) → V i) →ₗ[ℝ] (Y → ℝ) :=
    { toFun := fun vs y => ∑ i, (vs i).val y
      map_add' := by
        intro a b
        funext y
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        funext y
        simp [Finset.mul_sum] }
  have hrows : Submodule.span ℝ (Set.range (realMatrix (stackedRows F)).row)
      ≤ LinearMap.range L := by
    rw [Submodule.span_le]
    rintro v ⟨⟨i, x⟩, rfl⟩
    let row : V i := ⟨(realMatrix (F i)).row x, Submodule.subset_span ⟨x, rfl⟩⟩
    refine ⟨Pi.single i row, ?_⟩
    funext y
    change (∑ j, ((Pi.single i row : (k : I) → V k) j).val y) =
      (realMatrix (F i)) x y
    rw [Finset.sum_eq_single i]
    · simp [row, Matrix.row]
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  calc
    (realMatrix (stackedRows F)).rank =
        Module.finrank ℝ (Submodule.span ℝ
          (Set.range (realMatrix (stackedRows F)).row)) :=
      Matrix.rank_eq_finrank_span_row _
    _ ≤ Module.finrank ℝ (LinearMap.range L) := Submodule.finrank_mono hrows
    _ ≤ Module.finrank ℝ ((i : I) → V i) := LinearMap.finrank_range_le L
    _ = ∑ i, Module.finrank ℝ (V i) := Module.finrank_pi_fintype ℝ
    _ = ∑ i, (realMatrix (F i)).rank := by
      congr 1
      funext i
      exact (Matrix.rank_eq_finrank_span_row (realMatrix (F i))).symm

/-- Stack two row types without padding one of them to the other type. -/
def sumRows (F : A → Y → Bool) (G : B → Y → Bool) : (A ⊕ B) → Y → Bool :=
  Sum.elim F G

/-- Rank subadditivity for a literal disjoint union of row labels. -/
theorem sumRows_rank_le [Finite A] [Finite B] [Fintype Y]
    (F : A → Y → Bool) (G : B → Y → Bool) :
    (realMatrix (sumRows F G)).rank ≤ (realMatrix F).rank + (realMatrix G).rank := by
  classical
  let V : Submodule ℝ (Y → ℝ) := Submodule.span ℝ (Set.range (realMatrix F).row)
  let W : Submodule ℝ (Y → ℝ) := Submodule.span ℝ (Set.range (realMatrix G).row)
  have hrows : Submodule.span ℝ (Set.range (realMatrix (sumRows F G)).row) ≤ V ⊔ W := by
    rw [Submodule.span_le]
    rintro v ⟨a | b, rfl⟩
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨b, rfl⟩)
  calc
    (realMatrix (sumRows F G)).rank =
        Module.finrank ℝ (Submodule.span ℝ
          (Set.range (realMatrix (sumRows F G)).row)) :=
      Matrix.rank_eq_finrank_span_row _
    _ ≤ Module.finrank ℝ (V ⊔ W : Submodule ℝ (Y → ℝ)) :=
      Submodule.finrank_mono hrows
    _ ≤ Module.finrank ℝ V + Module.finrank ℝ W := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq V W
      omega
    _ = (realMatrix F).rank + (realMatrix G).rank := by
      rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]

namespace SourceMatrix

variable [Fintype X] [Fintype Y] [Fintype I] {s q₁ q₂ : ℕ}

theorem M₁_rank_le (R : X → Y → Bool) :
    (realMatrix (M₁ (q₁ := q₁) (s := s) R)).rank ≤ q₁ * (realMatrix R).rank :=
  indexedInterlace_rank_le R head

theorem M₂_rank_le (R : X → Y → Bool) :
    (realMatrix (M₂ (q₁ := q₁) (q₂ := q₂) (s := s) R)).rank ≤
      q₁ * q₂ * (realMatrix R).rank := by
  rw [M₂_eq_fullInterlace]
  calc
    _ ≤ q₂ * (realMatrix (fun γ a => M₁ (q₁ := q₁) (s := s) R a γ)).rank :=
      fullInterlace_rank_le _ q₂
    _ = q₂ * (realMatrix (M₁ (q₁ := q₁) (s := s) R)).rank := by
      rw [transpose_rank]
    _ ≤ q₂ * (q₁ * (realMatrix R).rank) := Nat.mul_le_mul_left q₂ (M₁_rank_le R)
    _ = q₁ * q₂ * (realMatrix R).rank := by ring

theorem T_rank_le (R : X → Y → Bool) :
    (realMatrix (T (q₁ := q₁) (q₂ := q₂) (s := s) R)).rank ≤
      q₁ * q₂ * (realMatrix R).rank := by
  change (realMatrix (fun z j => M₂ (q₁ := q₁) (q₂ := q₂) (s := s) R j z)).rank ≤ _
  rw [transpose_rank]
  exact M₂_rank_le R

omit [Fintype I] in
/-- The raw template block includes a repeated, unused tail coordinate.
That duplication cannot increase its rank. -/
theorem raw_template_rank_le [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) :
    (realMatrix (fun k Z => raw (q₁ := q₁) R activity (.inl k) Z)).rank ≤
      s * q₁ * q₂ * (realMatrix R).rank := by
  rw [raw_template_eq_interlace]
  calc
    _ ≤ (realMatrix (fullInterlace (T (q₁ := q₁) R) s)).rank :=
      pullback_rank_le (fullInterlace (T R) s) id Prod.snd
    _ ≤ s * (realMatrix (T (q₁ := q₁) (q₂ := q₂) (s := s) R)).rank :=
      fullInterlace_rank_le _ s
    _ ≤ s * (q₁ * q₂ * (realMatrix R).rank) := Nat.mul_le_mul_left s (T_rank_le R)
    _ = s * q₁ * q₂ * (realMatrix R).rank := by ring

omit [Fintype X] [Fintype I] in
/-- Each source item asks for a base column chosen independently of the row. -/
theorem raw_source_item_rank_le [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (i : I) :
    (realMatrix (fun u Z => raw (q₁ := q₁) R activity (.inr (i, u)) Z)).rank ≤
      (realMatrix R).rank :=
  pullback_rank_le R id (sourceColumn activity i)

/-- All source-item blocks together cost at most one base rank per item. -/
theorem raw_source_rank_le [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) :
    (realMatrix (fun k Z => raw (q₁ := q₁) R activity (.inr k) Z)).rank ≤
      Fintype.card I * (realMatrix R).rank := by
  calc
    _ ≤ ∑ i : I, (realMatrix (fun u Z =>
        raw (q₁ := q₁) R activity (.inr (i, u)) Z)).rank :=
      stackedRows_rank_le (fun i u Z => raw R activity (.inr (i, u)) Z)
    _ ≤ ∑ _i : I, (realMatrix R).rank := by
      exact Finset.sum_le_sum fun i _ => raw_source_item_rank_le R activity i
    _ = Fintype.card I * (realMatrix R).rank := by simp

/-- The actual raw source matrix, with no assumption on a source promise. -/
theorem raw_rank_le [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) :
    (realMatrix (raw (q₁ := q₁) R activity)).rank ≤
      (s * q₁ * q₂ + Fintype.card I) * (realMatrix R).rank := by
  have h := sumRows_rank_le
    (fun k Z => raw (q₁ := q₁) R activity (.inl k) Z)
    (fun k Z => raw (q₁ := q₁) R activity (.inr k) Z)
  have heq : sumRows (fun k Z => raw (q₁ := q₁) R activity (.inl k) Z)
      (fun k Z => raw (q₁ := q₁) R activity (.inr k) Z) =
      raw (q₁ := q₁) R activity := by
    funext k Z
    cases k <;> rfl
  rw [heq] at h
  exact h.trans ((Nat.add_le_add (raw_template_rank_le R activity)
    (raw_source_rank_le R activity)).trans_eq (by ring))

/-- Tags preserve every original column; both this duplication and the
subsequent transposition preserve rank exactly. -/
theorem N_rank_eq_raw [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) :
    (realMatrix (N (q₁ := q₁) R activity ξ₀)).rank =
      (realMatrix (raw (q₁ := q₁) R activity)).rank := by
  change (realMatrix (fun Z k => raw (q₁ := q₁) R activity k (forgetTag ξ₀ Z))).rank = _
  rw [transpose_rank]
  exact pullback_rank_eq_of_surjective (raw R activity) id (forgetTag ξ₀)
    Function.surjective_id (forgetTag_surjective ξ₀)

theorem N_rank_le [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) :
    (realMatrix (N (q₁ := q₁) R activity ξ₀)).rank ≤
      (s * q₁ * q₂ + Fintype.card I) * (realMatrix R).rank := by
  rw [N_rank_eq_raw]
  exact raw_rank_le R activity

/-- The first inequality in the manuscript's amplifier rank equation,
for the actual two-interlace successor matrix. -/
theorem successor_rank_le [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) (w Q : ℕ) :
    (realMatrix (successor (q₁ := q₁) R activity ξ₀ w Q)).rank ≤
      w * Q * (s * q₁ * q₂ + Fintype.card I) * (realMatrix R).rank := by
  unfold successor
  rw [transpose_rank]
  calc
    _ ≤ Q * (realMatrix (fun z a => fullInterlace (N (q₁ := q₁) R activity ξ₀) w a z)).rank :=
      fullInterlace_rank_le _ Q
    _ = Q * (realMatrix (fullInterlace (N (q₁ := q₁) R activity ξ₀) w)).rank := by
      rw [transpose_rank]
    _ ≤ Q * (w * (realMatrix (N (q₁ := q₁) R activity ξ₀)).rank) :=
      Nat.mul_le_mul_left Q (fullInterlace_rank_le _ w)
    _ ≤ Q * (w * ((s * q₁ * q₂ + Fintype.card I) * (realMatrix R).rank)) :=
      Nat.mul_le_mul_left Q (Nat.mul_le_mul_left w (N_rank_le R activity ξ₀))
    _ = w * Q * (s * q₁ * q₂ + Fintype.card I) * (realMatrix R).rank := by ring

/-- The source-item cardinality bound simplifies the actual successor rank
to the factor used in equation `eq:amplifier-rank`. -/
theorem successor_rank_le_factor [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) (w Q : ℕ)
    (hI : Fintype.card I ≤ 2 * s * q₂) :
    (realMatrix (successor (q₁ := q₁) R activity ξ₀ w Q)).rank ≤
      w * Q * s * q₂ * (q₁ + 2) * (realMatrix R).rank := by
  apply (successor_rank_le R activity ξ₀ w Q).trans
  calc
    _ ≤ w * Q * (s * q₁ * q₂ + 2 * s * q₂) * (realMatrix R).rank := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_left hI _))
    _ = w * Q * s * q₂ * (q₁ + 2) * (realMatrix R).rank := by ring

/-- For scheduled power-of-two widths, the factor is the exponential of
the communication overhead. The hypotheses here are literal parameter
equalities; proving that a parameter compiler satisfies them is separate. -/
theorem successor_rank_le_pow [NeZero s] (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) (w Q a b c d : ℕ)
    (hI : Fintype.card I ≤ 2 * s * q₂) (hq₁ : q₁ + 2 = s)
    (hs : s = 2 ^ a) (hq₂ : q₂ = 2 ^ b) (hw : w = 2 ^ c) (hQ : Q = 2 ^ d) :
    (realMatrix (successor (q₁ := q₁) R activity ξ₀ w Q)).rank ≤
      2 ^ (a + a + b + c + d) * (realMatrix R).rank := by
  apply (successor_rank_le_factor R activity ξ₀ w Q hI).trans_eq
  rw [hq₁, hs, hq₂, hw, hQ]
  simp only [pow_add]
  ring

end SourceMatrix

end Paper2
