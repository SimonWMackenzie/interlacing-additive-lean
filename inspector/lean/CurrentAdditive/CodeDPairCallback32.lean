import CurrentAdditive.CodeDPairCallbackPrepared
import CurrentAdditive.CodeDSourceContextScheduler

/-! The charged pair callback embedded in the source-list scheduler's 32
physical banks. -/

namespace CurrentAdditive.CodeDPairCallback32

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDPairCallbackPrepared
open Turing BitMachineEncoding

abbrev Stack := Fin 32

def locate : Fin 15 ↪ Stack where
  toFun j := ⟨j.val, by omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    simpa using congrArg Fin.val h

def program (l : CodeDPairCallbackPrepared.Label) :
    TM2.Stmt (fun _ : Stack => Bool)
      CodeDPairCallbackPrepared.Label CodeDPairCallbackPrepared.Control :=
  BitMachineStackEmbedding.stackStmt locate
    (CodeDPairCallbackPrepared.program l)

def run (t : Nat)
    (c : TM2.Cfg (fun _ : Stack => Bool)
      CodeDPairCallbackPrepared.Label CodeDPairCallbackPrepared.Control) :=
  ((advance program)^[t]) c

noncomputable def frame (foreign : Stack → List Bool)
    (c : CodeDPairCallbackPrepared.Config) :
    TM2.Cfg (fun _ : Stack => Bool)
      CodeDPairCallbackPrepared.Label CodeDPairCallbackPrepared.Control :=
  BitMachineStackEmbedding.stackCfg locate foreign c

theorem advance_frame (foreign : Stack → List Bool)
    (c : CodeDPairCallbackPrepared.Config) :
    advance program (frame foreign c) =
      frame foreign (advance CodeDPairCallbackPrepared.program c) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l =>
      change TM2.stepAux (program l) v
          (BitMachineStackEmbedding.bank locate foreign S) =
        BitMachineStackEmbedding.stackCfg locate foreign
          (TM2.stepAux (CodeDPairCallbackPrepared.program l) v S)
      exact BitMachineStackEmbedding.stack_stepAux locate foreign
        (CodeDPairCallbackPrepared.program l) v S

theorem run_frame (foreign : Stack → List Bool)
    (c : CodeDPairCallbackPrepared.Config) (t : Nat) :
    run t (frame foreign c) =
      frame foreign (CodeDPairCallbackPrepared.run t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      calc
        run (t+1) (frame foreign c) =
            advance program (run t (frame foreign c)) := by
              simp only [run, Function.iterate_succ_apply']
        _ = advance program
            (frame foreign (CodeDPairCallbackPrepared.run t c)) := by rw [ih]
        _ = frame foreign
            (advance CodeDPairCallbackPrepared.program
              (CodeDPairCallbackPrepared.run t c)) :=
                advance_frame foreign _
        _ = frame foreign (CodeDPairCallbackPrepared.run (t+1) c) := by
              simp only [CodeDPairCallbackPrepared.run,
                Function.iterate_succ_apply']

theorem pair_selected32 (x : CurrentAdditive.CodeDSourceCodecV2.Entry)
    (y : Nat × ℚ) (output : List Bool)
    (foreign15 : Fin 15 → List Bool)
    (foreign32 : Stack → List Bool)
    (scratch0 scratch5 : List Bool) :
    ∃ t ≤ scratch0.length + scratch5.length + 2 +
        CodeDPairCallbackRun.fixedBudget x y output,
      ∃ S : Stack → List Bool,
        run t (frame foreign32
          ⟨some .clear0, ((), none),
            Function.update
              (Function.update
                (CodeDPairCallbackForeign.initialWithForeign x y output
                  foreign15).stk 0 scratch0) 5 scratch5⟩) =
          ⟨none, ((), none), S⟩ ∧
        S 9 = output ++ EncodedCommunication.field
          (CodeDPairProductTargetV2.pairBytes x.weight
            (CurrentAdditive.CodeDCanonicalSourceV2.rawOfRat y.2)) ∧
        S 12 = CurrentAdditive.CodeDSourceCodecV2.encodeEntry x ∧
        S 8 = foreign15 8 ∧ S 10 = foreign15 10 ∧
        S 13 = foreign15 13 ∧
        (∀ j : Stack, 15 ≤ j.val → S j = foreign32 j) := by
  obtain ⟨t, ht, S15, hr, h9, h12, h8, h10, h13⟩ :=
    CodeDPairCallbackPrepared.pair_from_selected x y output
      foreign15 scratch0 scratch5
  let S := BitMachineStackEmbedding.bank locate foreign32 S15
  refine ⟨t, ht, S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_frame, hr]
    rfl
  · change BitMachineStackEmbedding.bank locate foreign32 S15
      (locate 9) = _
    rw [BitMachineStackEmbedding.bank_at]
    exact h9
  · change BitMachineStackEmbedding.bank locate foreign32 S15
      (locate 12) = _
    rw [BitMachineStackEmbedding.bank_at]
    exact h12
  · change BitMachineStackEmbedding.bank locate foreign32 S15
      (locate 8) = _
    rw [BitMachineStackEmbedding.bank_at]
    exact h8
  · change BitMachineStackEmbedding.bank locate foreign32 S15
      (locate 10) = _
    rw [BitMachineStackEmbedding.bank_at]
    exact h10
  · change BitMachineStackEmbedding.bank locate foreign32 S15
      (locate 13) = _
    rw [BitMachineStackEmbedding.bank_at]
    exact h13
  · intro j hj
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, hk⟩
    have hv : k.val = j.val := by simpa [locate] using congrArg Fin.val hk
    omega

#print axioms pair_selected32

end CurrentAdditive.CodeDPairCallback32
