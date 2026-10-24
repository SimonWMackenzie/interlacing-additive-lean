import EthInapproximability.CurrentPaper.ProtectedPreparation
import EthInapproximability.CurrentPaper.ParameterGates
import EthInapproximability.CurrentPaper.ProtectedGraphItems

/-!
# Physical deletion budgets before protected protocol separation

Source: locked v8 `A-stage4-details.tex`, the first paragraph of
`lem:paper-protected-preparation` and `eq:paper-deletion-tolerances`.
The ambient row/column density conditions are converted to the actual
template-bin and reference-reservoir losses used by the prefix proof.
The lower bound on a template bin uses the extra template group alone;
all its full-group copies remain present in the selected physical set.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedDeletionGates

open scoped Classical
open Construction JointTransfer ProtectedPreparation

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y]

/-- The extra template copies alone have exactly `1/(2^21*s)` of the
ambient protected columns in each bin. This equality has no nonemptiness
premise and remains valid for degenerate counts. -/
theorem extra_template_count (s L nv nb : ℕ) :
    Fintype.card (ProtectedRows s L nv nb X) =
      2 ^ 21 * s * L * extraTemplateMultiplicity (X := X) s L nv nb := by
  have hg := WeightedDuplication.card_group
    (WeightedDuplication.rowSupport (RawRows s L nv nb X) (TemplateSupport.{u} s L)
      (VertexRows nv X) (AuxiliaryRows nb X)) WeightedDuplication.rowWeight (1 : Fin 4)
  change Fintype.card (TemplateSupport.{u} s L ×
    Fin (extraTemplateMultiplicity (X := X) s L nv nb)) = _ at hg
  simp only [Fintype.card_prod, Fintype.card_fin] at hg
  norm_num [WeightedDuplication.card_rowSupport, WeightedDuplication.rowWeight,
    Fin.prod_univ_succ, TemplateSupport, ThirdRows] at hg
  rw [WeightedDuplication.card_rows]
  norm_num [TemplateSupport, ThirdRows]
  nlinarith [hg]

theorem template_bin_mass_bound (s L nv nb : ℕ) (i : Fin s) :
    Fintype.card (ProtectedRows s L nv nb X) ≤
      2 ^ 21 * s * (templateBin (X := X) s L nv nb i).card := by
  rw [extra_template_count, template_bin_card]
  simp only [TemplateLabels, Fintype.card_sum, Fintype.card_fin]
  have hm : extraTemplateMultiplicity (X := X) s L nv nb ≤
      fullRowMultiplicity (X := X) s L nv nb + extraTemplateMultiplicity (X := X) s L nv nb := by omega
  calc
    _ ≤ (2 ^ 21 * s * L) *
        (fullRowMultiplicity (X := X) s L nv nb + extraTemplateMultiplicity (X := X) s L nv nb) :=
      Nat.mul_le_mul_left _ hm
    _ = _ := by ring

/-- The reference reservoir has exactly its stated proportion, including
the uniform duplication and the unused graph input coordinates. -/
theorem reference_count (a s q : ℕ) :
    ((referenceRows (Y := Y) a s q).card : ℝ) =
      (91 / 92 : ℝ) * Fintype.card (ProtectedColumns a s q Y) := by
  have hc : (referenceRows (Y := Y) a s q).card =
      Fintype.card (WeightedDuplication.Group
        (WeightedDuplication.columnSupport (RawColumns a s q Y) (SecondRows a s q Y))
        WeightedDuplication.columnWeight 0) * uniformCopies (Y := Y) a s q := by
    rw [referenceRows, Finset.card_image_of_injective _ (referenceEmbedding a s q).injective,
      Finset.card_univ]
    calc
      _ = Fintype.card
          (WeightedDuplication.Group
            (WeightedDuplication.columnSupport (RawColumns a s q Y) (SecondRows a s q Y))
            WeightedDuplication.columnWeight 0 × Fin (uniformCopies (Y := Y) a s q)) :=
        Fintype.card_congr
          { toFun := fun z => (((z.2.1, z.1), z.2.2.1), z.2.2.2)
            invFun := fun z => (z.1.1.2, (z.1.1.1, (z.1.2, z.2)))
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      _ = _ := by rw [Fintype.card_prod, Fintype.card_fin]
  rw [hc, WeightedDuplication.card_group, WeightedDuplication.card_columns]
  norm_num [WeightedDuplication.columnWeight, WeightedDuplication.card_columnSupport,
    Fin.prod_univ_succ]
  ring

theorem complement_count {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset A) {η : ℝ} (h : (1 - η) * Fintype.card A ≤ S.card) :
    ((Finset.univ \ S).card : ℝ) ≤ η * Fintype.card A := by
  have hc : (Finset.univ \ S).card + S.card = Fintype.card A := by
    simpa only [Finset.univ_inter, Finset.card_univ] using Finset.card_sdiff_add_card_inter Finset.univ S
  have hcR : ((Finset.univ \ S).card : ℝ) + S.card = Fintype.card A := by exact_mod_cast hc
  nlinarith

/-- Dense physical restrictions satisfy both deletion premises of
`ProtectedPreparation.protected_prefix`; no protocol premise occurs here. -/
theorem prefix_deletion_gates (a s q L nv nb : ℕ)
    (A : Finset (ProtectedColumns a s q Y)) (B : Finset (ProtectedRows s L nv nb X))
    {ηR ηC x z : ℝ} (hηC : 0 ≤ ηC)
    (hA : (1 - ηR) * Fintype.card (ProtectedColumns a s q Y) ≤ A.card)
    (hB : (1 - ηC) * Fintype.card (ProtectedRows s L nv nb X) ≤ B.card)
    (hrow : ηC * (2 ^ 21 * (s : ℝ)) ≤ 1 - x)
    (hcol : ηR ≤ (91 / 92 : ℝ) * (1 - z)) :
    (∀ i : Fin s, ((Finset.univ \ B).card : ℝ) ≤
      (1 - x) * (templateBin (X := X) s L nv nb i).card) ∧
    (((Finset.univ \ A).card : ℝ) ≤ (1 - z) * (referenceRows (Y := Y) a s q).card) := by
  constructor
  · intro i
    have hc : (Fintype.card (ProtectedRows s L nv nb X) : ℝ) ≤
        2 ^ 21 * (s : ℝ) * (templateBin (X := X) s L nv nb i).card := by
      exact_mod_cast template_bin_mass_bound s L nv nb i
    calc
      _ ≤ ηC * Fintype.card (ProtectedRows s L nv nb X) := complement_count B hB
      _ ≤ ηC * (2 ^ 21 * (s : ℝ) * (templateBin (X := X) s L nv nb i).card) :=
        mul_le_mul_of_nonneg_left hc hηC
      _ = (ηC * (2 ^ 21 * (s : ℝ))) * (templateBin (X := X) s L nv nb i).card := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hrow (Nat.cast_nonneg _)
  · rw [reference_count]
    have hm := mul_le_mul_of_nonneg_right hcol
      (Nat.cast_nonneg (Fintype.card (ProtectedColumns a s q Y)))
    exact (complement_count A hA).trans (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hm)

/-- The actual source-constant choice supplies the two scalar deletion gates
with room to spare. These are arithmetic conclusions, not a protocol input. -/
theorem source_prefix_gates (i : Parameters.Input) (Δ : ℕ) (γ δ : ℚ)
    (hΔ : 1 ≤ Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ i.sourceConstant)
    (hvertex : γ / (4 * (Δ : ℚ)) ≤ δ) :
    (Parameters.columnTolerance i : ℝ) * (2 ^ 21 * (Parameters.bins i : ℝ)) ≤
        1 - 999 / 1000 ∧
      (Parameters.rowTolerance i : ℝ) ≤ (91 / 92 : ℝ) * (1 - 99 / 100) := by
  have h := ParameterGates.source_tolerances i Δ γ δ hΔ hγ hγone hsource hvertex
  have hC := (le_min_iff.mp h.2.1).1
  have hR := (le_min_iff.mp h.2.2).1
  have hs : (0 : ℚ) < Parameters.bins i := by exact_mod_cast Parameters.bins_pos i
  have hmul := (le_div_iff₀ (by positivity : (0 : ℚ) < 2000 * Parameters.bins i)).mp hC
  have hC' : Parameters.columnTolerance i * (2 ^ 21 * (Parameters.bins i : ℚ)) ≤
      1 - 999 / 1000 := by
    norm_num at hmul ⊢
    nlinarith
  have hR' : Parameters.rowTolerance i ≤ (91 / 92 : ℚ) * (1 - 99 / 100) := by
    norm_num at hR ⊢
    linarith
  constructor
  · have hcast := (Rat.cast_le (K := ℝ)).2 hC'
    norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
      Rat.cast_sub, Rat.cast_div, Rat.cast_one] at hcast
    norm_num
    exact hcast
  · have hcast := (Rat.cast_le (K := ℝ)).2 hR'
    norm_num only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_sub, Rat.cast_div,
      Rat.cast_one] at hcast
    norm_num
    exact hcast

/-- The near-full physical restriction in the protected theorem supplies
the exact template-bin and common-reference losses required before protocol
separation. Only the cited graph-source numerical hypotheses remain. -/
theorem prefix_deletion_gates_parameters (i : Parameters.Input) (Δ : ℕ) (γ δ : ℚ)
    (hΔ : 1 ≤ Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ i.sourceConstant)
    (hvertex : γ / (4 * (Δ : ℚ)) ≤ δ)
    (a q L nv nb : ℕ)
    (A : Finset (ProtectedColumns a (Parameters.bins i) q Y))
    (B : Finset (ProtectedRows (Parameters.bins i) L nv nb X))
    (hA : (1 - (Parameters.rowTolerance i : ℝ)) *
      Fintype.card (ProtectedColumns a (Parameters.bins i) q Y) ≤ A.card)
    (hB : (1 - (Parameters.columnTolerance i : ℝ)) *
      Fintype.card (ProtectedRows (Parameters.bins i) L nv nb X) ≤ B.card) :
    (∀ j : Fin (Parameters.bins i), ((Finset.univ \ B).card : ℝ) ≤
      (1 - 999 / 1000) * (templateBin (X := X) (Parameters.bins i) L nv nb j).card) ∧
    (((Finset.univ \ A).card : ℝ) ≤
      (1 - 99 / 100) * (referenceRows (Y := Y) a (Parameters.bins i) q).card) := by
  have hg := source_prefix_gates i Δ γ δ hΔ hγ hγone hsource hvertex
  exact prefix_deletion_gates a (Parameters.bins i) q L nv nb A B
    (by unfold Parameters.columnTolerance; positivity) hA hB hg.1 hg.2

theorem complement_count_rat {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset A) {η : ℚ} (h : (1 - η) * Fintype.card A ≤ S.card) :
    ((Finset.univ \ S).card : ℚ) ≤ η * Fintype.card A := by
  have hc : (Finset.univ \ S).card + S.card = Fintype.card A := by
    simpa only [Finset.univ_inter, Finset.card_univ] using
      Finset.card_sdiff_add_card_inter Finset.univ S
  have hcQ : ((Finset.univ \ S).card : ℚ) + S.card = Fintype.card A := by exact_mod_cast hc
  nlinarith

/-- The additional graph-group losses are obtained from one and the same
physical deletion. The factor-two slack makes both source budgets strict. -/
theorem graph_deletion_gates [Nonempty X] (s L n : ℕ)
    (hs : 4 ≤ s) (hL : 0 < L) (hn : 0 < n)
    (B : Finset (ProtectedRows s L (4 * s * n) (4 * s * (s - 3)) X))
    {η δ : ℚ} (hδ : 0 < δ)
    (hB : (1 - η) * Fintype.card
      (ProtectedRows s L (4 * s * n) (4 * s * (s - 3)) X) ≤ B.card)
    (hV : η ≤ (2 : ℚ) ^ (-22 : ℤ) * δ / 32)
    (haux : η ≤ (2 : ℚ) ^ (-22 : ℤ) / (32 * ((s : ℚ) - 3))) :
    2 * ((Finset.univ \ B).card : ℚ) <
      ((s : ℚ) / 2 * (δ * n)) *
        (Fintype.card X * ProtectedGraphItems.vertexMultiplicity (X := X) s L
          (4 * s * n) (4 * s * (s - 3)) : ℕ) ∧
    2 * ((Finset.univ \ B).card : ℚ) <
      ((s : ℚ) / 2) *
        (Fintype.card X * ProtectedGraphItems.auxiliaryMultiplicity (X := X) s L
          (4 * s * n) (4 * s * (s - 3)) : ℕ) := by
  have hdel := complement_count_rat B hB
  have hsQ : (0 : ℚ) < s := by exact_mod_cast (show 0 < s by omega)
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hm : 0 < Fintype.card X := Fintype.card_pos
  have hnv : 0 < 4 * s * n := by positivity
  have hnb : 0 < 4 * s * (s - 3) := Nat.mul_pos (by positivity) (by omega)
  have hv := ProtectedGraphItems.vertexMultiplicity_pos (X := X) s L
    (4 * s * n) (4 * s * (s - 3)) (by omega) hL hnv hnb
  have hb := ProtectedGraphItems.auxiliaryMultiplicity_pos (X := X) s L
    (4 * s * n) (4 * s * (s - 3)) (by omega) hL hnv hnb
  have hvQ : (0 : ℚ) < (Fintype.card X * ProtectedGraphItems.vertexMultiplicity
      (X := X) s L (4 * s * n) (4 * s * (s - 3)) : ℕ) := by
    exact_mod_cast Nat.mul_pos hm hv
  have hbQ : (0 : ℚ) < (Fintype.card X * ProtectedGraphItems.auxiliaryMultiplicity
      (X := X) s L (4 * s * n) (4 * s * (s - 3)) : ℕ) := by
    exact_mod_cast Nat.mul_pos hm hb
  constructor
  · rw [ProtectedGraphItems.vertex_group_card] at hdel
    push_cast at hdel ⊢
    norm_num at hV hdel
    have hmul := mul_le_mul_of_nonneg_right hV
      (show (0 : ℚ) ≤ (s : ℚ) * n * Fintype.card X *
        ProtectedGraphItems.vertexMultiplicity (X := X) s L
          (4 * s * n) (4 * s * (s - 3)) by positivity)
    have hpos := mul_pos (mul_pos (mul_pos hδ hsQ) hnQ) hvQ
    push_cast at hpos
    nlinarith
  · rw [ProtectedGraphItems.auxiliary_group_card] at hdel
    have hsub : ((s - 3 : ℕ) : ℚ) = (s : ℚ) - 3 := by
      rw [Nat.cast_sub (show 3 ≤ s by omega), Nat.cast_ofNat]
    have hs3Q : (3 : ℚ) < s := by exact_mod_cast (show 3 < s by omega)
    have hη := (le_div_iff₀ (by positivity : (0 : ℚ) < 32 * ((s : ℚ) - 3))).mp haux
    push_cast at hdel ⊢
    rw [hsub] at hdel
    norm_num at hη hdel
    have hmul := mul_le_mul_of_nonneg_right hη
      (show (0 : ℚ) ≤ (s : ℚ) * Fintype.card X *
        ProtectedGraphItems.auxiliaryMultiplicity (X := X) s L
          (4 * s * n) (4 * s * (s - 3)) by positivity)
    have hpos := mul_pos hsQ hbQ
    push_cast at hpos
    nlinarith

/-- Actual source parameters discharge the extra vertex and auxiliary
deletion budgets simultaneously, with strict slack in both conclusions. -/
theorem graph_deletion_gates_parameters [Nonempty X]
    (i : Parameters.Input) (Δ : ℕ) (γ δ : ℚ)
    (hΔ : 1 ≤ Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ i.sourceConstant)
    (hvertex : γ / (4 * (Δ : ℚ)) ≤ δ)
    (L n : ℕ) (hL : 0 < L) (hn : 0 < n)
    (B : Finset (ProtectedRows (Parameters.bins i) L
      (4 * Parameters.bins i * n) (4 * Parameters.bins i * (Parameters.bins i - 3)) X))
    (hB : (1 - Parameters.columnTolerance i) * Fintype.card
      (ProtectedRows (Parameters.bins i) L (4 * Parameters.bins i * n)
        (4 * Parameters.bins i * (Parameters.bins i - 3)) X) ≤ B.card) :
    2 * ((Finset.univ \ B).card : ℚ) <
      ((Parameters.bins i : ℚ) / 2 * (δ * n)) *
        (Fintype.card X * ProtectedGraphItems.vertexMultiplicity (X := X)
          (Parameters.bins i) L (4 * Parameters.bins i * n)
          (4 * Parameters.bins i * (Parameters.bins i - 3)) : ℕ) ∧
    2 * ((Finset.univ \ B).card : ℚ) <
      ((Parameters.bins i : ℚ) / 2) *
        (Fintype.card X * ProtectedGraphItems.auxiliaryMultiplicity (X := X)
          (Parameters.bins i) L (4 * Parameters.bins i * n)
          (4 * Parameters.bins i * (Parameters.bins i - 3)) : ℕ) := by
  have h := ParameterGates.source_tolerances i Δ γ δ hΔ hγ hγone hsource hvertex
  have hδ : 0 < δ := lt_of_lt_of_le (div_pos hγ (by positivity)) hvertex
  have hs : 4 ≤ Parameters.bins i := by
    have hh := Nat.le_of_dvd (Parameters.bins_pos i) (Parameters.sixtyfour_dvd_bins i)
    omega
  exact graph_deletion_gates (Parameters.bins i) L n hs hL hn B hδ hB
    (le_min_iff.mp (le_min_iff.mp h.2.1).2).1
    (le_min_iff.mp (le_min_iff.mp h.2.1).2).2

end EthInapproximability.CurrentPaper.ProtectedDeletionGates
