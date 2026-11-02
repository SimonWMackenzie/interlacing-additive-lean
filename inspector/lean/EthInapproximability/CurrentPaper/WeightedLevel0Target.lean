import EthInapproximability.CurrentPaper.WeightedLevel0Clean

/-! Lane owner:b-weighted-level-4, unit 2, segment 1 (1c-iii), piece 1c-a.

After the charged clear (`WeightedLevel0Clean.level0_clean`), EVERY writer cell
`k : Fin 64` of the combined bank equals the literal writer bank of the admitted
physical-step start `ProtectedFullBankBridgeScratch.actualWriterStart` at level 0,

  `MatrixWeightedOrderPreparation.sourceBank (persistentBank d) |VG| (s-3) (4s) k`,

except writer 22, which is blank (`d.rawBits` there is the named premise of lane
owner:b-stage4-entry-program-2). In particular writer 60 is blank, as
`sourceBank` requires. Pure identities about the exit bank; no machine claim. -/

namespace EthInapproximability.CurrentPaper.WeightedLevel0Target

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

/-! ## `sourceBank` at literal cells, for a VARIABLE input record -/

theorem sb_slot7 (d : MatrixWeightedEntryController.Input) (v a K : ℕ) :
    MatrixWeightedOrderPreparation.sourceBank (MatrixWeightedEntryController.persistentBank d)
      v a K 7 = List.replicate v true := by
  show bank MatrixWeightedOrderPreparation.slots _ _ (MatrixWeightedOrderPreparation.slots 0) = _
  rw [bank_at]
  rfl

theorem sb_slot8 (d : MatrixWeightedEntryController.Input) (v a K : ℕ) :
    MatrixWeightedOrderPreparation.sourceBank (MatrixWeightedEntryController.persistentBank d)
      v a K 8 = List.replicate a true := by
  show bank MatrixWeightedOrderPreparation.slots _ _ (MatrixWeightedOrderPreparation.slots 1) = _
  rw [bank_at]
  rfl

theorem sb_slot9 (d : MatrixWeightedEntryController.Input) (v a K : ℕ) :
    MatrixWeightedOrderPreparation.sourceBank (MatrixWeightedEntryController.persistentBank d)
      v a K 9 = List.replicate K true := by
  show bank MatrixWeightedOrderPreparation.slots _ _ (MatrixWeightedOrderPreparation.slots 2) = _
  rw [bank_at]
  rfl

theorem sb_other (d : MatrixWeightedEntryController.Input) (v a K : ℕ) (k : Fin 64)
    (hk : ∀ j, MatrixWeightedOrderPreparation.slots j ≠ k) :
    MatrixWeightedOrderPreparation.sourceBank (MatrixWeightedEntryController.persistentBank d)
      v a K k = MatrixWeightedEntryController.persistentBank d k := by
  unfold MatrixWeightedOrderPreparation.sourceBank
  exact bank_outside _ _ _ _ (fun ⟨j, hj⟩ => hk j hj)

theorem pb_blank (d : MatrixWeightedEntryController.Input) (k : Fin 64) (hk : k ∉ keepW)
    (h22 : k ≠ 22) (h60 : k ≠ 60) : MatrixWeightedEntryController.persistentBank d k = [] := by
  fin_cases k <;> first
    | rfl
    | (exfalso; revert hk; decide)
    | (exfalso; exact h22 rfl)
    | (exfalso; exact h60 rfl)

theorem sb_blank (d : MatrixWeightedEntryController.Input) (v a K : ℕ) (k : Fin 64)
    (hk : k ∉ keepW) (h22 : k ≠ 22) :
    MatrixWeightedOrderPreparation.sourceBank (MatrixWeightedEntryController.persistentBank d)
      v a K k = [] := by
  by_cases hs : ∃ j, MatrixWeightedOrderPreparation.slots j = k
  · obtain ⟨j, rfl⟩ := hs
    unfold MatrixWeightedOrderPreparation.sourceBank
    rw [bank_at]
    fin_cases j <;> first
      | rfl
      | (exfalso; revert hk; decide)
  · rw [sb_other d v a K k (fun j hj => hs ⟨j, hj⟩)]
    refine pb_blank d k hk h22 ?_
    rintro rfl
    exact hs ⟨8, rfl⟩

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The writer bank of `actualWriterStart` at level 0 with writer 22 blanked. -/
def targetW (G : EndpointGraph V E) (n c : ℕ) (k : Fin 64) : List Bool :=
  if k = 22 then [] else
    MatrixWeightedOrderPreparation.sourceBank
      (MatrixWeightedEntryController.persistentBank
        (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix))
      (Fintype.card V)
      (Iteration.s G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix - 3)
      (4 * Iteration.s G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix) k

/-- Every writer cell of the cleaned level-0 exit bank is the literal target. -/
theorem clean_writer_target (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts M G n c F Q P) (k : Fin 64) :
    BitMachineClearBank.cleared clearCells (level0RowsBank M G n c F Q P) (wc k) =
      targetW G n c k := by
  obtain ⟨h1, h3, h4, h6, h15, h16, h17, h18, h21, h26, h27, h28, h29, h47, h48, h49, h50, h51,
    h52, h53, h7, h8, h9, _, _⟩ := hf
  by_cases hk : k ∈ keepW
  · rw [clean_keep _ k hk]
    unfold targetW
    rw [if_neg (by rintro rfl; revert hk; decide)]
    simp only [keepW, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [sb_other _ _ _ _ 1 (by decide)]; exact h1
    · rw [sb_other _ _ _ _ 3 (by decide)]; exact h3
    · rw [sb_other _ _ _ _ 4 (by decide)]; exact h4
    · rw [sb_other _ _ _ _ 6 (by decide)]; exact h6
    · rw [sb_slot7]; exact h7
    · rw [sb_slot8]; exact h8
    · rw [sb_slot9]; exact h9
    · rw [sb_other _ _ _ _ 15 (by decide)]; exact h15
    · rw [sb_other _ _ _ _ 16 (by decide)]; exact h16
    · rw [sb_other _ _ _ _ 17 (by decide)]; exact h17
    · rw [sb_other _ _ _ _ 18 (by decide)]; exact h18
    · rw [sb_other _ _ _ _ 21 (by decide)]; exact h21
    · rw [sb_other _ _ _ _ 26 (by decide)]; exact h26
    · rw [sb_other _ _ _ _ 27 (by decide)]; exact h27
    · rw [sb_other _ _ _ _ 28 (by decide)]; exact h28
    · rw [sb_other _ _ _ _ 29 (by decide)]; exact h29
    · rw [sb_other _ _ _ _ 47 (by decide)]; exact h47
    · rw [sb_other _ _ _ _ 48 (by decide)]; exact h48
    · rw [sb_other _ _ _ _ 49 (by decide)]; exact h49
    · rw [sb_other _ _ _ _ 50 (by decide)]; exact h50
    · rw [sb_other _ _ _ _ 51 (by decide)]; exact h51
    · rw [sb_other _ _ _ _ 52 (by decide)]; exact h52
    · rw [sb_other _ _ _ _ 53 (by decide)]; exact h53
  · rw [clean_writer _ k hk]
    unfold targetW
    split_ifs with h22
    · rfl
    · exact (sb_blank _ _ _ _ k hk h22).symm

/-- The admitted physical-step writer bank, read literally: its `Fin 64` cells
are exactly `targetW` away from writer 22. -/
theorem actualWriterStart_cells (G : EndpointGraph V E) (n c : ℕ) (k : Fin 64) (h22 : k ≠ 22) :
    (ProtectedFullBankBridgeScratch.actualWriterStart G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk (.inl (.inl k)) =
      targetW G n c k := by
  unfold targetW
  rw [if_neg h22]
  rfl

#print axioms sb_blank
#print axioms clean_writer_target
#print axioms actualWriterStart_cells

end
end EthInapproximability.CurrentPaper.WeightedLevel0Target
