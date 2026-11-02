import CurrentAdditive.IndexedCodeDContextTwoFields
import CurrentAdditive.IndexedCodeDCoordinatePacketJoin

/-! The fixed 32-cell packet builder can execute in the same larger ambient
bank used by the Code D getter callbacks. Every higher scheduler cell is
preserved by the concrete embedding. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open Turing

def packetAmbient (N : ℕ) : packetStack ↪ StackN N where
  toFun k := ⟨k.val, by omega⟩
  inj' := by
    intro x y h
    apply Fin.ext
    simpa using congrArg Fin.val h

def ambientWordCopyProgram (N : ℕ) :=
  fun l : SourceClausePreservingBroadcast.Label ⊕ Unit =>
    match l with
    | .inl l => BitMachineStackEmbedding.stmt
        (packetAmbient N) Sum.inl id id (some (.inr ()))
        (SourceClausePreservingBroadcast.program
          (3 : packetStack) 22 [18] l)
    | .inr () => (TM2.Stmt.halt :
        TM2.Stmt (fun _ : StackN N => Bool)
          (SourceClausePreservingBroadcast.Label ⊕ Unit)
          (Unit × Option Bool))

noncomputable def ambientPacketFrame {N : ℕ}
    {L : Type} {V : Type}
    (foreign : StackN N → List Bool)
    (c : TM2.Cfg (fun _ : packetStack => Bool) L V)
    (next : Option (L ⊕ Unit)) :
    TM2.Cfg (fun _ : StackN N => Bool) (L ⊕ Unit) V :=
  BitMachineStackEmbedding.cfg (packetAmbient N) foreign Sum.inl id next c

theorem ambientPacketFrame_initial {N : ℕ} {L V : Type}
    (S : StackN N → List Bool) (l : L) (v : V)
    (next : Option (L ⊕ Unit)) :
    ambientPacketFrame S
      (⟨some l, v, fun k : packetStack => S (packetAmbient N k)⟩ :
        TM2.Cfg (fun _ : packetStack => Bool) L V) next =
      (⟨some (.inl l), v, S⟩ :
        TM2.Cfg (fun _ : StackN N => Bool) (L ⊕ Unit) V) := by
  simp only [ambientPacketFrame, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  congr 1
  exact BitMachineStackEmbedding.bank_restrict (packetAmbient N) S

theorem ambient_word_copy_run (N : ℕ)
    (S : StackN N → List Bool) (word : List Bool)
    (hword : S ((packetAmbient N) 3) = word)
    (hscratch : S ((packetAmbient N) 22) = []) :
    let low := fun k : packetStack => S (packetAmbient N k)
    let low' := packetWordCopied low word
    ∃ t ≤ 2*word.length+3,
      ((advance (ambientWordCopyProgram N))^[t])
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
  let low' := packetWordCopied low word
  have hlocal := SourceClausePreservingBroadcast.run_halt
    (3 : packetStack) 22 [18]
    (by decide) (by decide) (by decide) (by decide)
    word low hword hscratch
  have hhalt :
      (((advance (SourceClausePreservingBroadcast.program
        (3 : packetStack) 22 [18]))^[2*word.length+3])
        (⟨some .scan, ((), none), low⟩ :
          TM2.Cfg (fun _ : packetStack => Bool)
            SourceClausePreservingBroadcast.Label (Unit × Option Bool))).l = none := by
    rw [hlocal]
  obtain ⟨t, ht, hr⟩ := BitMachineStackEmbedding.outputs
    (packetAmbient N) S Sum.inl id id (by intro v; rfl)
    (some (.inr ()))
    (SourceClausePreservingBroadcast.program (3 : packetStack) 22 [18])
    (ambientWordCopyProgram N) (by intro l; rfl)
    (⟨some .scan, ((), none), low⟩ :
      TM2.Cfg (fun _ : packetStack => Bool)
        SourceClausePreservingBroadcast.Label (Unit × Option Bool))
    (2*word.length+3) hhalt
  refine ⟨t, ht, ?_⟩
  rw [hlocal] at hr
  simpa only [ambientPacketFrame, low'] using hr

#print axioms ambient_word_copy_run
#print axioms ambientPacketFrame_initial

end CurrentAdditive.IndexedExecutableStepRecovery
