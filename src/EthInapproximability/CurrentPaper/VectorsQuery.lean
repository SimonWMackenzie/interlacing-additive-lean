import EthInapproximability.CurrentPaper.VectorsMiddle

namespace EthInapproximability.CurrentPaper.VectorsQuery

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EntryVectorsCell
open EthInapproximability.CurrentPaper.VectorsPrefix
open EthInapproximability.CurrentPaper.VectorsMiddle

noncomputable section

def B9 (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) : CS → List Bool :=
  Function.update (B8 edges D nV m M4 x y) (c 24)
    [SourceGraphPayloadMachine.endpointHit edges (y % m) (x % D)]

theorem query (edges : List (ℕ × ℕ)) (D nV m M4 x y : ℕ) :
    ∃ t ≤ 3*(x % D) + 3*(y % m) + 6 +
      16*((SourceGraphPayloadMachine.endpointStream edges).length+1)*(edges.length+1),
      ∃ v,
        ((advance P9)^[t])
          (⟨some SourceGraphPayloadMachine.BaseCell.start,
            SourceGraphPayloadMachine.BaseCell.initial,
            B8 edges D nV m M4 x y⟩ : TM2.Cfg (fun _ : CS => Bool) _ _) =
          ⟨none, v, B9 edges D nV m M4 x y⟩ := by
  obtain ⟨t, ht, v, hr⟩ :=
    SourceGraphPayloadMachine.BaseCell.cell_run edges (x % D) (y % m)
  have hrun := BitMachineStackRun.run baseSlots (B8 edges D nV m M4 x y)
    SourceGraphPayloadMachine.BaseCell.program
    (SourceGraphPayloadMachine.BaseCell.cell
      (some SourceGraphPayloadMachine.BaseCell.start)
      SourceGraphPayloadMachine.BaseCell.initial
      (SourceGraphPayloadMachine.endpointStream edges) [] [] [] [] [] []
      (List.replicate (x % D) true) (List.replicate (y % m) true) []) t
  unfold SourceGraphPayloadMachine.BaseCell.run at hr
  rw [hr] at hrun
  have hs : bank baseSlots (B8 edges D nV m M4 x y)
      (SourceGraphPayloadMachine.BaseCell.cell
        (some SourceGraphPayloadMachine.BaseCell.start)
        SourceGraphPayloadMachine.BaseCell.initial
        (SourceGraphPayloadMachine.endpointStream edges) [] [] [] [] [] []
        (List.replicate (x % D) true) (List.replicate (y % m) true) []).stk =
      B8 edges D nV m M4 x y := by
    apply bank_eq_self
    intro k
    rcases k with k | k <;> fin_cases k <;> rfl
  have hf : bank baseSlots (B8 edges D nV m M4 x y)
      (SourceGraphPayloadMachine.BaseCell.cell none v
        (SourceGraphPayloadMachine.endpointStream edges) [] [] [] [] [] []
        (List.replicate (x % D) true) (List.replicate (y % m) true)
        [SourceGraphPayloadMachine.endpointHit edges (y % m) (x % D)]).stk =
      B9 edges D nV m M4 x y := by
    funext j
    by_cases hj : ∃ k, baseSlots k = j
    · obtain ⟨k, rfl⟩ := hj
      rw [bank_at]
      rcases k with k | k <;> fin_cases k <;> rfl
    · rw [bank_outside _ _ _ j hj]
      have hne : j ≠ c 24 := by
        intro e
        apply hj
        refine ⟨.inr 2, ?_⟩
        rw [e]
        rfl
      simp only [B9, Function.update_of_ne hne]
  refine ⟨t, ht, v, ?_⟩
  simpa only [P9, stackCfg, hs, hf] using hrun

#print axioms query

end
end EthInapproximability.CurrentPaper.VectorsQuery
