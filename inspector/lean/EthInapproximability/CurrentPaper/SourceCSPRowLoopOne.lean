import EthInapproximability.CurrentPaper.SourceCSPRowLoopController

/-!
# One physical row-loop iteration and its callback boundary

The query subroutine is inlined into the permanent row-loop bank. Its halt
transfers control to `.yield`, preserving the entire parsed bank and the
outer row counter. A separate reset phase follows that boundary.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopOne

open Turing BitMachineEncoding
open SourceCSPRowLoopController

theorem query_bank (q : Nat) (S : Stack q → List Bool)
    (T : SourceCSPRowQueryFrame.Stack q → List Bool)
    (hT : ∀ k, T k = S (.inl k)) :
    BitMachineStackEmbedding.bank queryStack S T = S := by
  apply BitMachineStackEmbedding.bank_eq_self
  exact hT

theorem query_bank_elim (q : Nat) (S : Stack q → List Bool)
    (T : SourceCSPRowQueryFrame.Stack q → List Bool) :
    BitMachineStackEmbedding.bank queryStack S T =
      Sum.elim T (fun k => S (.inr k)) := by
  funext k
  cases k with
  | inl k => exact BitMachineStackEmbedding.bank_at queryStack S T k
  | inr k =>
      apply BitMachineStackEmbedding.bank_outside
      rintro ⟨x, hx⟩
      cases hx

theorem query_lift (q H : Nat)
    (T U : SourceCSPRowQueryFrame.Stack q → List Bool)
    (E : Fin 4 → List Bool) (v : QueryControl) (t : Nat)
    (hrun : ((advance (SourceCSPRowQueryFrame.combinedProgram q H))^[t])
      (⟨some (BitMachineRawSequence.leftLabel
        (.start 0 : SourceCSPRowController.Label q H)), queryStart, T⟩ :
        TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
          (QueryLabel q H) QueryControl) = ⟨none, v, U⟩) :
    ∃ u ≤ t,
      ((advance (program q H))^[u])
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
    (SourceCSPRowQueryFrame.combinedProgram q H) (program q H)
    (by intro l; rfl) c t hh
  rw [hrun] at he
  simp only [BitMachineStackEmbedding.cfg, BitMachineInline.cfg,
    BitMachineStackEmbedding.stackCfg] at he
  rw [query_bank_elim q S T, query_bank_elim q S U] at he
  refine ⟨u, hu, ?_⟩
  simpa only [S, c, initialControl, queryControl] using he

theorem reset_lift (q H : Nat) (S : Stack q → List Bool)
    (rest cap : List Bool) (hrest : S (.inl (.inr 0)) = rest)
    (hcap : S (.inr 1) = cap) (hscratch : S (.inr 3) = []) :
    ∃ t ≤ (∑ i : Fin (q * 5 + 4),
        (S (SourceCSPRowLoopClear.scratch q i)).length) +
          (q * 5 + 4) + 2 + (2 * cap.length + 2) + 1,
      ((advance (program q H))^[t])
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
    (SourceCSPRowLoopReset.program q) (program q H)
    (by intro l; rfl) c tr hh
  rw [hrunC] at he
  simp only [BitMachineInline.cfg] at he
  refine ⟨u, by omega, ?_⟩
  simpa only [c, initialControl, resetControl] using he

end EthInapproximability.CurrentPaper.SourceCSPRowLoopOne
