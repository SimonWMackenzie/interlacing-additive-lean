import Paper2.FiniteSampling
import Paper2.IndexedMatrices

/-!
# Rational input laws and uniformly labelled copies

Source: v12 Appendix A, `cl:rational-laws`, common-denominator construction
and preservation under forgetting duplicate labels. The uniform realization
is constructed from numerator/denominator arithmetic, not supplied as a
certificate. Interlacing-specific profile transfer and the final strict
rounding margin are separate obligations.
-/

namespace Paper2

open scoped BigOperators
open Workspace.Types.CommComplexity
open RankLeaves

/-- The strictly positive rational input laws used in the manuscript. -/
structure PositiveRationalLaw (α : Type*) [Fintype α] where
  weight : α → ℚ
  positive : ∀ a, 0 < weight a
  total : ∑ a, weight a = 1

namespace PositiveRationalLaw

variable {α : Type*} [Fintype α]

/-- Interpret rational weights as a finite real probability law. -/
noncomputable def toFiniteLaw (μ : PositiveRationalLaw α) : FiniteLaw α where
  weight a := μ.weight a
  nonneg a := by exact_mod_cast (μ.positive a).le
  total := by exact_mod_cast μ.total

theorem nonempty (μ : PositiveRationalLaw α) : Nonempty α :=
  μ.toFiniteLaw.nonempty

/-- An explicit common denominator; no least-common-multiple minimality is
needed for the proof-only realization. -/
def denominator (μ : PositiveRationalLaw α) : ℕ := ∏ a, (μ.weight a).den

theorem denominator_pos (μ : PositiveRationalLaw α) : 0 < μ.denominator := by
  exact Finset.prod_pos fun a _ => (μ.weight a).den_pos

/-- The integer number of copies of each original input. -/
noncomputable def multiplicity (μ : PositiveRationalLaw α) (a : α) : ℕ := by
  classical
  exact (μ.weight a).num.toNat * ∏ b ∈ Finset.univ.erase a, (μ.weight b).den

theorem multiplicity_pos (μ : PositiveRationalLaw α) (a : α) :
    0 < μ.multiplicity a := by
  classical
  unfold multiplicity
  apply Nat.mul_pos
  · have h := Rat.num_pos.mpr (μ.positive a)
    omega
  · exact Finset.prod_pos fun b _ => (μ.weight b).den_pos

/-- Each integer multiplicity is precisely its probability times the
common denominator. -/
theorem multiplicity_eq_scaled (μ : PositiveRationalLaw α) (a : α) :
    (μ.multiplicity a : ℚ) = μ.weight a * μ.denominator := by
  classical
  have hnum : (0 : ℤ) ≤ (μ.weight a).num := (Rat.num_pos.mpr (μ.positive a)).le
  have hden : ((μ.weight a).den : ℚ) ≠ 0 := by
    exact_mod_cast (μ.weight a).den_nz
  have hprod := Finset.mul_prod_erase (Finset.univ : Finset α)
    (fun b => (μ.weight b).den) (Finset.mem_univ a)
  unfold multiplicity denominator
  rw [← hprod, Nat.cast_mul, Nat.cast_mul]
  have hcast : ((μ.weight a).num.toNat : ℚ) = ((μ.weight a).num : ℚ) := by
    exact_mod_cast (Int.toNat_of_nonneg hnum)
  have hcancel : μ.weight a * ((μ.weight a).den : ℚ) = (μ.weight a).num := by
    apply (eq_div_iff hden).mp
    exact (μ.weight a).num_div_den.symm
  rw [hcast, ← mul_assoc, hcancel]

theorem sum_multiplicity (μ : PositiveRationalLaw α) :
    ∑ a, μ.multiplicity a = μ.denominator := by
  have h : (∑ a, (μ.multiplicity a : ℚ)) = (μ.denominator : ℚ) := by
    simp_rw [multiplicity_eq_scaled]
    rw [← Finset.sum_mul, μ.total, one_mul]
  exact_mod_cast h

theorem weight_eq_multiplicity_div (μ : PositiveRationalLaw α) (a : α) :
    μ.weight a = (μ.multiplicity a : ℚ) / μ.denominator := by
  apply (eq_div_iff (by exact_mod_cast (μ.denominator_pos.ne'))).mpr
  exact (μ.multiplicity_eq_scaled a).symm

/-- The actual finite duplicate-label carrier. -/
abbrev Copies (μ : PositiveRationalLaw α) := Σ a, Fin (μ.multiplicity a)

def forget (μ : PositiveRationalLaw α) : μ.Copies → α := Sigma.fst

theorem forget_surjective (μ : PositiveRationalLaw α) :
    Function.Surjective μ.forget := by
  intro a
  exact ⟨⟨a, ⟨0, μ.multiplicity_pos a⟩⟩, rfl⟩

instance (μ : PositiveRationalLaw α) : Nonempty μ.Copies := by
  obtain ⟨a⟩ := μ.nonempty
  exact ⟨⟨a, ⟨0, μ.multiplicity_pos a⟩⟩⟩

theorem card_copies (μ : PositiveRationalLaw α) :
    Fintype.card μ.Copies = μ.denominator := by
  simp only [Copies, Fintype.card_sigma, Fintype.card_fin]
  exact μ.sum_multiplicity

/-- Every duplicate label has the same mass, the reciprocal of the
explicit common denominator. -/
noncomputable def uniformCopies (μ : PositiveRationalLaw α) : FiniteLaw μ.Copies where
  weight _ := (μ.denominator : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_copies]
    exact mul_inv_cancel₀ (by exact_mod_cast μ.denominator_pos.ne')

theorem real_weight_eq (μ : PositiveRationalLaw α) (a : α) :
    (μ.weight a : ℝ) = (μ.multiplicity a : ℝ) * (μ.denominator : ℝ)⁻¹ := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (μ.weight_eq_multiplicity_div a)
  simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast,
    div_eq_mul_inv] using h

/-- Forgetting labels pushes the uniform copy law to exactly the prescribed
rational law, for every original event. -/
theorem uniformCopies_prob_preimage (μ : PositiveRationalLaw α) (E : α → Prop) :
    μ.uniformCopies.prob (fun z => E (μ.forget z)) = μ.toFiniteLaw.prob E := by
  classical
  unfold FiniteLaw.prob
  change (∑ z : (Σ a, Fin (μ.multiplicity a)),
      if E z.1 then (μ.denominator : ℝ)⁻¹ else 0) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : E a
  · simp only [ha, ↓reduceIte, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, toFiniteLaw]
    exact (μ.real_weight_eq a).symm
  · simp [ha]

/-- The uniform fraction of an arbitrary copy subset is no greater than
the original mass of its projection, including partial copy fibres. -/
theorem uniformCopies_prob_le_projection (μ : PositiveRationalLaw α)
    (S : μ.Copies → Prop) :
    μ.uniformCopies.prob S ≤
      μ.toFiniteLaw.prob (fun a => ∃ i : Fin (μ.multiplicity a), S ⟨a, i⟩) := by
  rw [← μ.uniformCopies_prob_preimage]
  apply μ.uniformCopies.prob_mono
  intro z hz
  exact ⟨z.2, hz⟩

/-- Projection of a retained copy set; no closure under entire fibres is
assumed. -/
def projected (μ : PositiveRationalLaw α) (S : μ.Copies → Prop) (a : α) : Prop :=
  ∃ i : Fin (μ.multiplicity a), S ⟨a, i⟩

def forgetRetained (μ : PositiveRationalLaw α) (S : μ.Copies → Prop) :
    {z : μ.Copies // S z} → {a : α // μ.projected S a} :=
  fun z => ⟨z.val.1, z.val.2, z.property⟩

/-- Every projected retained input has an actual surviving representative. -/
theorem forgetRetained_surjective (μ : PositiveRationalLaw α) (S : μ.Copies → Prop) :
    Function.Surjective (μ.forgetRetained S) := by
  rintro ⟨a, i, hi⟩
  exact ⟨⟨⟨a, i⟩, hi⟩, rfl⟩

/-- Independent copy draws give the prescribed independent original draw
law on every coordinatewise event. -/
theorem uniformCopies_iid_prob_all (μ : PositiveRationalLaw α)
    (m : ℕ) (E : α → Prop) :
    (μ.uniformCopies.iid m).prob (fun z => ∀ i, E (μ.forget (z i))) =
      (μ.toFiniteLaw.prob E) ^ m := by
  calc
    _ = (μ.uniformCopies.prob (fun z => E (μ.forget z))) ^ m :=
      μ.uniformCopies.iid_prob_all m (fun z => E (μ.forget z))
    _ = _ := by rw [μ.uniformCopies_prob_preimage]

end PositiveRationalLaw

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Rational-law duplication preserves the exact deterministic cost. -/
theorem rationalCopies_D_eq (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) :
    D (fun x : μ.Copies => fun y : ν.Copies => F (μ.forget x) (ν.forget y)) = D F :=
  pullback_D_eq_of_surjective F μ.forget ν.forget μ.forget_surjective ν.forget_surjective

/-- The same duplicate matrix preserves its ordinary real rank exactly. -/
theorem rationalCopies_rank_eq (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) :
    (realMatrix (fun x : μ.Copies => fun y : ν.Copies =>
      F (μ.forget x) (ν.forget y))).rank = (realMatrix F).rank :=
  pullback_rank_eq_of_surjective F μ.forget ν.forget μ.forget_surjective ν.forget_surjective

/-- Exact cost of a restriction to arbitrary retained copy sets. The finite
instances on these subtypes can always be chosen classically. This is the
matrix-transport step underlying profile transfer, not the full interlacing
profile theorem or its numerical admissibility hypotheses. -/
theorem rationalCopies_restricted_D_eq
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (F : X → Y → Bool)
    (S : μ.Copies → Prop) (T : ν.Copies → Prop)
    [Fintype {z : μ.Copies // S z}] [Fintype {z : ν.Copies // T z}]
    [Fintype {x : X // μ.projected S x}] [Fintype {y : Y // ν.projected T y}] :
    D (fun x : {z : μ.Copies // S z} => fun y : {z : ν.Copies // T z} =>
      F (μ.forget x.val) (ν.forget y.val)) =
    D (fun x : {x : X // μ.projected S x} => fun y : {y : Y // ν.projected T y} =>
      F x.val y.val) := by
  exact pullback_D_eq_of_surjective
    (fun x : {x : X // μ.projected S x} => fun y : {y : Y // ν.projected T y} =>
      F x.val y.val)
    (μ.forgetRetained S) (ν.forgetRetained T)
    (μ.forgetRetained_surjective S) (ν.forgetRetained_surjective T)

theorem rationalCopies_restricted_rank_eq
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (F : X → Y → Bool)
    (S : μ.Copies → Prop) (T : ν.Copies → Prop)
    [Fintype {z : ν.Copies // T z}] [Fintype {y : Y // ν.projected T y}] :
    (realMatrix (fun x : {z : μ.Copies // S z} => fun y : {z : ν.Copies // T z} =>
      F (μ.forget x.val) (ν.forget y.val))).rank =
    (realMatrix (fun x : {x : X // μ.projected S x} =>
      fun y : {y : Y // ν.projected T y} => F x.val y.val)).rank := by
  exact pullback_rank_eq_of_surjective
    (fun x : {x : X // μ.projected S x} => fun y : {y : Y // ν.projected T y} =>
      F x.val y.val)
    (μ.forgetRetained S) (ν.forgetRetained T)
    (μ.forgetRetained_surjective S) (ν.forgetRetained_surjective T)

end Paper2
