import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalCombinedAll
import EthInapproximability.CurrentPaper.SourceCSPRowLoopOne

/-!
# Shared-bank lifts for the corrected all-input row loop

The new controller changes only the yield instruction. Parser/query and
reset labels are physically identical to the frozen positive-only controller.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalOne

open Turing BitMachineEncoding SourceCSPRowLoopController

theorem query_lift (q H : Nat)
    (T U : SourceCSPRowQueryFrame.Stack q → List Bool)
    (E : Fin 4 → List Bool) (v : QueryControl) (t : Nat)
    (hrun : ((advance (SourceCSPRowQueryFrame.combinedProgram q H))^[t])
      (⟨some (BitMachineRawSequence.leftLabel
        (.start 0 : SourceCSPRowController.Label q H)), queryStart, T⟩ :
        TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
          (QueryLabel q H) QueryControl) = ⟨none, v, U⟩) :
    ∃ u ≤ t,
      ((advance (SourceCSPRowLoopTotalController.program q H))^[u])
        (⟨some (queryLabel (BitMachineRawSequence.leftLabel
          (.start 0 : SourceCSPRowController.Label q H))),
          initialControl, Sum.elim T E⟩ : Config q H) =
        ⟨some (adminLabel .yield), queryControl v, Sum.elim U E⟩ := by
  let S : Stack q → List Bool := Sum.elim T E
  let c : TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
      (QueryLabel q H) QueryControl :=
    ⟨some (BitMachineRawSequence.leftLabel
      (.start 0 : SourceCSPRowController.Label q H)), queryStart, T⟩
  have hh : (((advance (SourceCSPRowQueryFrame.combinedProgram q H))^[t]) c).l =
      none := by rw [hrun]
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs queryStack S
    queryLabel queryControl (fun v : Control => v.1.1)
    (by intro v; rfl) (some (adminLabel .yield))
    (SourceCSPRowQueryFrame.combinedProgram q H)
    (SourceCSPRowLoopTotalController.program q H)
    (by intro l; rfl) c t hh
  rw [hrun] at he
  simp only [BitMachineStackEmbedding.cfg, BitMachineInline.cfg,
    BitMachineStackEmbedding.stackCfg] at he
  rw [SourceCSPRowLoopOne.query_bank_elim q S T,
    SourceCSPRowLoopOne.query_bank_elim q S U] at he
  refine ⟨u, hu, ?_⟩
  simpa only [S, c, initialControl, queryControl] using he

theorem reset_lift (q H : Nat) (S : Stack q → List Bool)
    (rest cap : List Bool) (hrest : S (.inl (.inr 0)) = rest)
    (hcap : S (.inr 1) = cap) (hscratch : S (.inr 3) = []) :
    ∃ t ≤ (∑ i : Fin (q * 5 + 4),
        (S (SourceCSPRowLoopClear.scratch q i)).length) +
          (q * 5 + 4) + 2 + (2 * cap.length + 2) + 1,
      ((advance (SourceCSPRowLoopTotalController.program q H))^[t])
        (⟨some (resetLabel (BitMachineRawSequence.leftLabel 0)),
          initialControl, S⟩ : Config q H) =
        ⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial rest cap)
            (fun k => S (.inr k))⟩ := by
  obtain ⟨tr, htr, hrun⟩ := SourceCSPRowLoopReset.reset_run q S rest cap
    hrest hcap hscratch
  let c : TM2.Cfg (fun _ : Stack q => Bool)
      (ResetLabel q) ResetControl :=
    ⟨some (BitMachineRawSequence.leftLabel 0), resetStart, S⟩
  have hrunC : ((advance (SourceCSPRowLoopReset.program q))^[tr]) c =
      ⟨none, resetStart, Sum.elim
        (SourceCSPRowQueryFrame.initial rest cap) (fun k => S (.inr k))⟩ := by
    simpa only [c, resetStart] using hrun
  have hh : (((advance (SourceCSPRowLoopReset.program q))^[tr]) c).l = none := by
    rw [hrunC]
  obtain ⟨u, hu, he⟩ := BitMachineInline.outputs resetLabel resetControl
    (fun v : Control => v.1.2) (by intro v; rfl)
    (some (adminLabel .check))
    (SourceCSPRowLoopReset.program q)
    (SourceCSPRowLoopTotalController.program q H)
    (by intro l; rfl) c tr hh
  rw [hrunC] at he
  simp only [BitMachineInline.cfg] at he
  refine ⟨u, by omega, ?_⟩
  simpa only [c, initialControl, resetControl] using he

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalOne
