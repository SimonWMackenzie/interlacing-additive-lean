import EthInapproximability.CurrentPaper.MatrixEntryCorrectness
import EthInapproximability.CurrentPaper.MatrixEntryFinalBounds

/-!
# Uniform runtime of the complete literal matrix-entry evaluator

The bound includes physical label decoding, literal array reads, arithmetic,
branch selection, and clearing every temporary stack. Parameters and payload
arrays are supplied physically in the input bank; their construction is a
separate stage of the complete encoded reduction.
-/

namespace EthInapproximability.CurrentPaper.MatrixEntryRuntime

open MatrixEntryCorrectness MatrixEntryProgram MatrixEntryData
open MatrixUniformEntryBounds

def bound (a d N₁ N₂ n : ℕ) : ℕ := 65536 * scale a d N₁ N₂ n ^ 8

theorem entryBound_le {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool)
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁) :
    entryBound a (MatrixMaterialization.storeBits C₁ C₂ v) r c ≤ bound a d N₁ N₂ n := by
  let S := scale a d N₁ N₂ n
  have hb := scale_bounds a d N₁ N₂ n
  have h18 : S ≤ S ^ 8 := by simpa using Nat.pow_le_pow_right hb.1 (by decide : 1 ≤ 8)
  have h28 : S ^ 2 ≤ S ^ 8 := Nat.pow_le_pow_right hb.1 (by decide : 2 ≤ 8)
  have h38 : S ^ 3 ≤ S ^ 8 := Nat.pow_le_pow_right hb.1 (by decide : 3 ≤ 8)
  have h48 : S ^ 4 ≤ S ^ 8 := Nat.pow_le_pow_right hb.1 (by decide : 4 ≤ 8)
  have h08 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hb.1
  have hp := preparation_bound (a := a)
    (MatrixMaterialization.rowCode N₂ n r).isLt (MatrixMaterialization.columnCode d N₁ c).isLt
  change preparationBound r c ≤ 1024 * S ^ 8 at hp
  have hl := MatrixEntryFinalBounds.label_work_bound (a := a) r c
  change _ ≤ 9 * S at hl
  change entryBound a _ r c ≤ 65536 * S ^ 8
  rcases r with ⟨p,z⟩ | i
  · have ht := MatrixEntryFinalBounds.template_bound ha C₁ C₂ v p z c
    have hw := template_work_bound (d := d) (n := n) ha (c.2 p).2 z (c.2 p).1
    change _ ≤ 32896 * S ^ 4 at ht
    change _ ≤ 16 * S ^ 3 at hw
    unfold entryBound queryBound cleanupSize
    simp only [List.length_replicate, List.length_nil]
    omega
  · have hq := MatrixEntryFinalBounds.source_query_bound (a := a) (N₂ := N₂) i c
    have hw := MatrixEntryFinalBounds.source_work_bound (a := a) (N₂ := N₂) i c
    change _ ≤ 64 * S ^ 3 at hq
    change _ ≤ 2 * S ^ 2 at hw
    unfold entryBound queryBound cleanupSize sourceQueryBound
    simp only [List.length_replicate, List.length_nil]
    omega

/-- The machine is fixed and finite; only the contents of its Boolean stacks
depend on the dimensions, sampled families, source matrix, or chosen entry. -/
theorem entry_run {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (r : (Fin 4 × Fin N₂) ⊕ Fin n) (c : ExactConstruction.Columns d N₁) (out : List Bool) :
    let data := MatrixMaterialization.storeBits C₁ C₂ v
    ∃ t ≤ bound a d N₁ N₂ n,
      run t (cfg (some start) initial
        (input a d N₁ N₂ (MatrixMaterialization.rowCode N₂ n r).val
          (MatrixMaterialization.columnCode d N₁ c).val data out)) =
      cfg none initial
        (input a d N₁ N₂ (MatrixMaterialization.rowCode N₂ n r).val
          (MatrixMaterialization.columnCode d N₁ c).val data
          (ExactConstruction.matrix ha C₁ C₂ v cap r c :: out)) := by
  obtain ⟨t, ht, he⟩ := MatrixEntryCorrectness.entry_run ha C₁ C₂ v cap r c out
  exact ⟨t, ht.trans (entryBound_le ha C₁ C₂ v r c), he⟩

end EthInapproximability.CurrentPaper.MatrixEntryRuntime
