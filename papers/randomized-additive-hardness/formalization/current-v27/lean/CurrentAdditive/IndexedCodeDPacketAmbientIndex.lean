import CurrentAdditive.IndexedCodeDPacketAmbient

/-! The unary-coordinate copy uses the same concrete low-bank embedding as
the word copy, with all higher scheduler cells retained. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open Turing

def ambientIndexCopyProgram (N : ℕ) :=
  fun l : SourceClausePreservingBroadcast.Label ⊕ Unit =>
    match l with
    | .inl l => BitMachineStackEmbedding.stmt
        (packetAmbient N) Sum.inl id id (some (.inr ()))
        (SourceClausePreservingBroadcast.program
          (4 : packetStack) 22 [17] l)
    | .inr () => (TM2.Stmt.halt :
        TM2.Stmt (fun _ : StackN N => Bool)
          (SourceClausePreservingBroadcast.Label ⊕ Unit)
          (Unit × Option Bool))

theorem ambient_index_copy_run (N : ℕ)
    (S : StackN N → List Bool) (index : List Bool)
    (hindex : S ((packetAmbient N) 4) = index)
    (hscratch : S ((packetAmbient N) 22) = []) :
    let low := fun k : packetStack => S (packetAmbient N k)
    let low' := packetIndexCopied low index
    ∃ t ≤ 2*index.length+3,
      ((advance (ambientIndexCopyProgram N))^[t])
        (ambientPacketFrame S
          (⟨some .scan, ((), none), low⟩ :
            TM2.Cfg (fun _ : packetStack => Bool)
              SourceClausePreservingBroadcast.Label (Unit × Option Bool))
          (some (.inr ()))) =
        ambientPacketFrame S
          (⟨none, ((), none), low'⟩ :
            TM2.Cfg (fun _ : packetStack => Bool)
              SourceClausePreservingBroadcast.Label (Unit × Option Bool))
          (some (.inr ())) := by
  dsimp only
  let low := fun k : packetStack => S (packetAmbient N k)
  let low' := packetIndexCopied low index
  have hlocal := SourceClausePreservingBroadcast.run_halt
    (4 : packetStack) 22 [17]
    (by decide) (by decide) (by decide) (by decide)
    index low hindex hscratch
  have hhalt :
      (((advance (SourceClausePreservingBroadcast.program
        (4 : packetStack) 22 [17]))^[2*index.length+3])
        (⟨some .scan, ((), none), low⟩ :
          TM2.Cfg (fun _ : packetStack => Bool)
            SourceClausePreservingBroadcast.Label (Unit × Option Bool))).l = none := by
    rw [hlocal]
  obtain ⟨t, ht, hr⟩ := BitMachineStackEmbedding.outputs
    (packetAmbient N) S Sum.inl id id (by intro v; rfl)
    (some (.inr ()))
    (SourceClausePreservingBroadcast.program (4 : packetStack) 22 [17])
    (ambientIndexCopyProgram N) (by intro l; rfl)
    (⟨some .scan, ((), none), low⟩ :
      TM2.Cfg (fun _ : packetStack => Bool)
        SourceClausePreservingBroadcast.Label (Unit × Option Bool))
    (2*index.length+3) hhalt
  refine ⟨t, ht, ?_⟩
  rw [hlocal] at hr
  simpa only [ambientPacketFrame, low'] using hr

#print axioms ambient_index_copy_run

end CurrentAdditive.IndexedExecutableStepRecovery
