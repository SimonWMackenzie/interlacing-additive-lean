import Paper2.ProductProjections
import Paper2.ClassicalCapacities
import EthBridge.Induction
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Defect under projection of actual retained columns

Frozen v12 source: Appendix A, `cl:projection` (lines 60--124).
The specified and disjoint-split estimates hold for arbitrary independent
finite laws. The averaged estimate below is explicitly restricted to uniform
finite alphabets. It consumes the frozen witness-producing
`EthBridge.member_max_projection`, whose output is an actual restricted
interlaced matrix, not a numerical density promise or a new lower-bound axiom.

The imported maximum-projection interface hides its selected coordinate set;
the statement here consequently exposes the retained matrix and its cost,
not a separately named coordinate witness. Rational-law averaged projection
is not claimed.
-/

namespace Paper2.ProjectionDefect

open scoped BigOperators
open Workspace.Types.CommComplexity Workspace.Types.Interlace

/-- Base-two logarithmic loss of positive retained mass. Every projection
comparison below assumes positive parent mass; Lean's total logarithm at
zero is not used as a convention for an empty column set. -/
noncomputable def defect (mass : ℝ) : ℝ := -Real.logb 2 mass

theorem defect_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    defect b ≤ defect a := by
  exact neg_le_neg (Real.logb_le_logb_of_le (by norm_num) ha hab)

theorem defect_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    defect (a * b) = defect a + defect b := by
  simp only [defect, Real.logb_mul ha.ne' hb.ne']
  ring

theorem defect_rpow {a : ℝ} (ha : 0 < a) (t : ℝ) :
    defect (Real.rpow a t) = t * defect a := by
  change -Real.logb 2 (a ^ t) = t * (-Real.logb 2 a)
  rw [Real.logb_rpow_eq_mul_logb_of_pos ha]
  ring

theorem defect_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ defect a := by
  exact neg_nonneg.mpr (Real.logb_nonpos (by norm_num) ha ha1)

section ProductLaws

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

/-- Any specified set of coordinates loses no more defect than the parent.
The retained event may correlate all coordinates. -/
theorem specified (μ : ι → FiniteLaw A) (Z : (ι → A) → Prop)
    (hZ : 0 < (FiniteLaw.pi μ).prob Z) (S : Finset ι) :
    defect (ProductProjections.projectionMass μ Z S) ≤
      defect ((FiniteLaw.pi μ).prob Z) :=
  defect_antitone hZ (ProductProjections.prob_le_projectionMass μ Z S)

/-- Disjoint coordinate projections have total defect at most the parent
defect. Coverage is unnecessary, so this also applies to a partition. -/
theorem split (μ : ι → FiniteLaw A) (Z : (ι → A) → Prop)
    (hZ : 0 < (FiniteLaw.pi μ).prob Z) (S T : Finset ι)
    (hST : Disjoint S T) :
    defect (ProductProjections.projectionMass μ Z S) +
      defect (ProductProjections.projectionMass μ Z T) ≤
        defect ((FiniteLaw.pi μ).prob Z) := by
  classical
  let blocks : Bool → Finset ι := fun b => if b then S else T
  have hd : Pairwise (fun b c => Disjoint (blocks b) (blocks c)) := by
    intro b c hbc
    cases b <;> cases c <;> simp_all [blocks, hST.symm]
  have hprod : (FiniteLaw.pi μ).prob Z ≤
      ProductProjections.projectionMass μ Z S *
        ProductProjections.projectionMass μ Z T := by
    calc
      _ ≤ (FiniteLaw.pi μ).prob (fun x =>
          ∀ b, ProductProjections.projected Z (blocks b) (fun i => x i.val)) := by
        apply FiniteLaw.prob_mono
        intro x hx b
        exact ⟨x, hx, rfl⟩
      _ = ∏ b, ProductProjections.projectionMass μ Z (blocks b) :=
        ProductProjections.prob_disjoint_blocks μ blocks hd
          (fun b => ProductProjections.projected Z (blocks b))
      _ = _ := by simp [blocks]
  have hS := lt_of_lt_of_le hZ (ProductProjections.prob_le_projectionMass μ Z S)
  have hT := lt_of_lt_of_le hZ (ProductProjections.prob_le_projectionMass μ Z T)
  rw [← defect_mul hS hT]
  exact defect_antitone hZ hprod

end ProductLaws

section Uniform

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]

private theorem law_ext {α : Type*} [Fintype α] (μ ν : FiniteLaw α)
    (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ
  cases ν
  congr 1
  exact funext h

/-- Independent uniform coordinates give the uniform law on labelled words. -/
theorem pi_uniform :
    FiniteLaw.pi (fun _ : ι => FiniteLaw.uniform A) =
      FiniteLaw.uniform (ι → A) := by
  apply law_ext
  intro x
  simp [FiniteLaw.pi, FiniteLaw.uniform, Nat.cast_pow]

/-- Uniform word density; both alphabets and surviving words retain their
actual finite labels. -/
noncomputable def columnDensity (p : ℕ) (C : Finset (Fin p → A)) : ℝ :=
  (C.card : ℝ) / (Fintype.card A : ℝ) ^ p

theorem columnDensity_eq_prob (p : ℕ) (C : Finset (Fin p → A)) :
    columnDensity p C = (FiniteLaw.uniform (Fin p → A)).prob (· ∈ C) := by
  rw [FiniteLaw.uniform_prob_finset]
  simp [columnDensity, Nat.cast_pow]

theorem columnDensity_pos (p : ℕ) {C : Finset (Fin p → A)}
    (hC : C.Nonempty) : 0 < columnDensity p C := by
  unfold columnDensity
  exact div_pos (by exact_mod_cast hC.card_pos) (pow_pos (by
    exact_mod_cast Fintype.card_pos) _)

theorem columnDensity_le_one (p : ℕ) (C : Finset (Fin p → A)) :
    columnDensity p C ≤ 1 := by
  rw [columnDensity_eq_prob]
  exact FiniteLaw.prob_le_one _ _

omit [Nonempty A] in
/-- This is exactly the appendix's `log_2 (n^p / |C|)` formula. -/
theorem defect_columnDensity (p : ℕ) (C : Finset (Fin p → A)) :
    defect (columnDensity p C) =
      Real.logb 2 ((Fintype.card A : ℝ) ^ p / (C.card : ℝ)) := by
  rw [defect, columnDensity, ← Real.logb_inv]
  simp only [inv_div]

variable [DecidableEq A]

omit [Fintype ι] in
/-- Cardinality form of the actual projected uniform mass. -/
theorem projectionMass_uniform (C : Finset (ι → A)) (S : Finset ι) :
    ProductProjections.projectionMass (fun _ => FiniteLaw.uniform A)
      (· ∈ C) S =
      ((C.image (fun x => fun i : S => x i.val)).card : ℝ) /
        (Fintype.card A : ℝ) ^ S.card := by
  classical
  unfold ProductProjections.projectionMass
  rw [pi_uniform]
  have he : ProductProjections.projected (· ∈ C) S =
      (fun y => y ∈ C.image (fun x => fun i : S => x i.val)) := by
    funext y
    apply propext
    simp [ProductProjections.projected]
  rw [he, FiniteLaw.uniform_prob_finset]
  simp [Nat.cast_pow]

/-- The literal specified-coordinate defect inequality from `cl:projection`. -/
theorem specified_columns (p : ℕ) (C : Finset (Fin p → A)) (hC : C.Nonempty)
    (S : Finset (Fin p)) :
    Real.logb 2 ((Fintype.card A : ℝ) ^ S.card /
      ((C.image (fun x => fun i : S => x i.val)).card : ℝ)) ≤
      Real.logb 2 ((Fintype.card A : ℝ) ^ p / (C.card : ℝ)) := by
  have hprob : (FiniteLaw.pi (fun _ : Fin p => FiniteLaw.uniform A)).prob (· ∈ C) =
      columnDensity p C := by
    rw [pi_uniform, columnDensity_eq_prob]
  have h := specified (fun _ : Fin p => FiniteLaw.uniform A) (· ∈ C)
    (by rw [hprob]; exact columnDensity_pos p hC) S
  rw [hprob, projectionMass_uniform, defect_columnDensity] at h
  simpa only [defect, ← Real.logb_inv, inv_div] using h

/-- The literal split-coordinate defect inequality. Disjointness is enough;
the paper's partition hypothesis is a special case. -/
theorem split_columns (p : ℕ) (C : Finset (Fin p → A)) (hC : C.Nonempty)
    (S T : Finset (Fin p)) (hST : Disjoint S T) :
    Real.logb 2 ((Fintype.card A : ℝ) ^ S.card /
      ((C.image (fun x => fun i : S => x i.val)).card : ℝ)) +
    Real.logb 2 ((Fintype.card A : ℝ) ^ T.card /
      ((C.image (fun x => fun i : T => x i.val)).card : ℝ)) ≤
      Real.logb 2 ((Fintype.card A : ℝ) ^ p / (C.card : ℝ)) := by
  have hprob : (FiniteLaw.pi (fun _ : Fin p => FiniteLaw.uniform A)).prob (· ∈ C) =
      columnDensity p C := by
    rw [pi_uniform, columnDensity_eq_prob]
  have h := split (fun _ : Fin p => FiniteLaw.uniform A) (· ∈ C)
    (by rw [hprob]; exact columnDensity_pos p hC) S T hST
  rw [hprob, projectionMass_uniform, projectionMass_uniform, defect_columnDensity] at h
  simpa only [defect, ← Real.logb_inv, inv_div] using h

end Uniform

section ActualMatrices

variable {X Y : Type*} [Finite X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- Averaged projection in its witness-producing form: an actual restriction
on `ell` blocks retains the row floor and at most the corresponding fraction
of column defect, and is no harder than this particular parent matrix.

The lower bound `H ≤ D` of the returned matrix therefore transfers to the
parent, including when its surviving columns are arbitrarily correlated. -/
theorem averaged_member (F : X → Y → Bool) (p ell T : ℕ)
    (hell : 1 ≤ ell) (hellp : ell ≤ p)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hR : NPCC.IsEquipartitionedGE R Finset.univ T) (hC : C.Nonempty) :
    ∃ (R' : Finset (Fin ell × X)) (C' : Finset (Fin ell → Y)),
      NPCC.IsEquipartitionedGE R' Finset.univ T ∧ C'.Nonempty ∧
      defect (columnDensity ell C') ≤
        ((ell : ℝ) / (p : ℝ)) * defect (columnDensity p C) ∧
      D (NPCC.subgame (interlaceFun F ell) R' C') ≤
        D (NPCC.subgame (interlaceFun F p) R C) := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  have hn : 0 < (Fintype.card Y : ℝ) := by exact_mod_cast Fintype.card_pos
  have hy := columnDensity_pos p hC
  have hcols : (Fintype.card Y : ℝ) ^ p * columnDensity p C ≤ (C.card : ℝ) := by
    unfold columnDensity
    rw [mul_div_cancel₀ _ (pow_pos hn p).ne']
  obtain ⟨R', C', hR', hbound, hD⟩ := EthBridge.member_max_projection F p ell T
    (columnDensity p C) hell hellp hy (columnDensity_le_one p C)
    (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero)
    (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero) R C hR hcols
  have hmass : Real.rpow (columnDensity p C) ((ell : ℝ) / (p : ℝ)) ≤
      columnDensity ell C' := by
    exact (le_div_iff₀ (pow_pos hn ell)).mpr (by simpa [mul_comm] using hbound)
  have hmasspos := lt_of_lt_of_le (Real.rpow_pos_of_pos hy _) hmass
  have hC' : C'.Nonempty := by
    apply Finset.card_pos.mp
    have hcpos : (0 : ℝ) < C'.card := by
      exact (div_pos_iff_of_pos_right (pow_pos hn ell)).mp hmasspos
    exact_mod_cast hcpos
  refine ⟨R', C', hR', hC', ?_, hD⟩
  calc
    _ ≤ defect (Real.rpow (columnDensity p C) ((ell : ℝ) / (p : ℝ))) :=
      defect_antitone (Real.rpow_pos_of_pos hy _) hmass
    _ = _ := defect_rpow hy _

end ActualMatrices

end Paper2.ProjectionDefect
