import EthInapproximability.CurrentPaper.MatrixUniformEntryBounds
import EthInapproximability.CurrentPaper.MatrixTemplateEntry
import EthInapproximability.CurrentPaper.MatrixRowDecode

/-!
# Final branch and work-space envelopes for the literal entry program

All expressions below are the explicit budgets and residual stack lengths
of the already implemented controllers. The complete execution theorem is
supplied by the separate semantic composition, not by these inequalities.
-/

namespace EthInapproximability.CurrentPaper.MatrixEntryFinalBounds

open MatrixUniformEntryBounds

theorem template_bound {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (p : Fin 4) (z : Fin N₂)
    (c : ExactConstruction.Columns d N₁) :
    MatrixTemplateEntry.bound (c.2 p).2.val (ExactConstruction.prefixLength a + 3)
      z.val d (c.2 p).1.val a (ExactConstruction.prefixLength a)
      (MatrixMaterialization.storeBits C₁ C₂ v).first.length
      (MatrixMaterialization.storeBits C₁ C₂ v).second.length ≤
      32896 * scale a d N₁ N₂ n ^ 4 := by
  have h₁ := template_address_bound (d := d) (N₁ := N₁) (N₂ := N₂) (n := n)
    ha (c.2 p).2 z (c.2 p).1
  have h₂ := MatrixEntryRuntimeBounds.template_bound ha C₁ C₂ v p z c
  dsimp only at h₂
  change _ ≤ 128 * scale a d N₁ N₂ n ^ 4 at h₂
  unfold MatrixTemplateEntry.bound MatrixTemplateEntry.preparationBound
  omega

theorem label_work_bound {a d N₁ N₂ n : ℕ}
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁) :
    MatrixRowDecode.sourceIndex r + MatrixRowDecode.templateIndex r +
      (∑ p : Fin 4, ((c.2 p).2.val + (c.2 p).1.val)) ≤
      9 * scale a d N₁ N₂ n := by
  let S := scale a d N₁ N₂ n
  have hb := scale_bounds a d N₁ N₂ n
  have hr : MatrixRowDecode.sourceIndex r + MatrixRowDecode.templateIndex r ≤ S := by
    cases r with
    | inl r =>
        have hz : r.2.val ≤ S := (Nat.le_of_lt r.2.isLt).trans hb.2.2.2.2.2.1
        simpa [MatrixRowDecode.sourceIndex, MatrixRowDecode.templateIndex] using hz
    | inr i =>
        have hi : i.val ≤ S := (Nat.le_of_lt i.isLt).trans hb.2.2.2.2.2.2
        simpa [MatrixRowDecode.sourceIndex, MatrixRowDecode.templateIndex] using hi
  have hp (p : Fin 4) : (c.2 p).2.val + (c.2 p).1.val ≤ 2 * S := by
    have h₁ := (Nat.le_of_lt (c.2 p).2.isLt).trans hb.2.2.2.2.1
    have h₂ := (Nat.le_of_lt (c.2 p).1.isLt).trans hb.2.2.2.1
    omega
  have hs := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin 4))) => hp p)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  change _ ≤ 9 * S
  omega

theorem source_query_bound {a d N₁ N₂ n : ℕ} (i : Fin n)
    (c : ExactConstruction.Columns d N₁) :
    (i.val + 1) *
      (3 * ((c.2 0).1.val + (i.val + 1) * d) + 3 * (n * d) + 2 * d + 12) +
      3 * i.val + 5 + 2 * (c.2 0).1.val + 2 ≤
      64 * scale a d N₁ N₂ n ^ 3 := by
  let S := scale a d N₁ N₂ n
  have hb := scale_bounds a d N₁ N₂ n
  have hg := MatrixEntryRuntimeBounds.source_bound (a := a) (N₁ := N₁) (N₂ := N₂)
    i (c.2 0).1
  change _ ≤ 32 * S ^ 3 at hg
  have hi : i.val ≤ S := (Nat.le_of_lt i.isLt).trans hb.2.2.2.2.2.2
  have hα : (c.2 0).1.val ≤ S := (Nat.le_of_lt (c.2 0).1.isLt).trans hb.2.2.2.1
  have h13 : S ≤ S ^ 3 := by simpa using Nat.pow_le_pow_right hb.1 (by decide : 1 ≤ 3)
  have h03 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hb.1
  change _ ≤ 64 * S ^ 3
  omega

theorem source_work_bound {a d N₁ N₂ n : ℕ} (i : Fin n)
    (c : ExactConstruction.Columns d N₁) :
    (c.2 0).1.val + (i.val + 1) * d ≤ 2 * scale a d N₁ N₂ n ^ 2 := by
  let S := scale a d N₁ N₂ n
  have hb := scale_bounds a d N₁ N₂ n
  have hi : i.val + 1 ≤ S := (Nat.succ_le_of_lt i.isLt).trans hb.2.2.2.2.2.2
  have hα : (c.2 0).1.val ≤ S := (Nat.le_of_lt (c.2 0).1.isLt).trans hb.2.2.2.1
  have hd : d ≤ S := hb.2.2.2.1
  have h12 : S ≤ S ^ 2 := by simpa using Nat.pow_le_pow_right hb.1 (by decide : 1 ≤ 2)
  change _ ≤ 2 * S ^ 2
  nlinarith [Nat.mul_le_mul hi hd]

end EthInapproximability.CurrentPaper.MatrixEntryFinalBounds
