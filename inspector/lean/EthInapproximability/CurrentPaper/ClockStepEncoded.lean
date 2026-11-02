import EthInapproximability.CurrentPaper.ClockStepMachine
import EthInapproximability.CurrentPaper.BitMachineBankWrapper
import EthInapproximability.CurrentPaper.ClockIterationInput

/-!
# An ordinary-input polynomial-time prefix-clock step

Source: frozen v8 `05-iteration.tex`. The bank wrapper physically decodes
and encodes the fixed number of Boolean-stack fields. The first three
fields are active, unary budget, and accepted counter; all remaining fields
are transient storage. Malformed packets are rejected by the actual parser.
-/

namespace EthInapproximability.CurrentPaper.ClockStepEncoded

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Turing BitMachineEncoding
open scoped BigOperators

variable (M : BitMachine.Machine)

def width := ClockStepMachine.tempCount M + 3

def order : ClockStepMachine.Stack M ≃ Fin (width M) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 3))
    (Fintype.equivFin (ClockInputPreparation.Temp M))).trans finSumFinEquiv).trans
      (finCongr (Nat.add_comm 3 (ClockStepMachine.tempCount M)))

def toBank (S : ClockStepMachine.Stack M → List Bool) : Fin (width M) → List Bool :=
  fun i => S ((order M).symm i)

def fromBank (S : Fin (width M) → List Bool) : ClockStepMachine.Stack M → List Bool :=
  fun i => S (order M i)

theorem to_from (S : Fin (width M) → List Bool) : toBank M (fromBank M S) = S := by
  funext i
  simp [toBank,fromBank]

theorem from_to (S : ClockStepMachine.Stack M → List Bool) : fromBank M (toBank M S) = S := by
  funext i
  simp [toBank,fromBank]

def step (S : Fin (width M) → List Bool) : Fin (width M) → List Bool :=
  let T := fromBank M S
  toBank M (ClockStepMachine.result M (T (.inl 0)) (T (.inl 1)) (T (.inl 2)))

def program (l : ClockStepMachine.Label M) :
    TM2.Stmt (fun _ : Fin (width M) => Bool) (ClockStepMachine.Label M) (ClockStepMachine.Control M) :=
  renameStmt (order M) (Equiv.refl _) (Equiv.refl _) (ClockStepMachine.program M l)

theorem totalWords_from (S : Fin (width M) → List Bool) :
    ClockStepMachine.totalWords M (fromBank M S) = ∑ i, (S i).length :=
  Equiv.sum_comp (order M) (fun i => (S i).length)

theorem totalWords_le_encode (S : Fin (width M) → List Bool) :
    ClockStepMachine.totalWords M (fromBank M S) ≤ (BitMachineBankCodec.encode S).length := by
  rw [totalWords_from,BitMachineBankCodec.encode_length]
  omega

theorem raw_run (S : Fin (width M) → List Bool) :
    ∃ t ≤ ClockStepMachine.rawBound M * ((BitMachineBankCodec.encode S).length+1)^2,
      ∃ v : ClockStepMachine.Control M,
        ((advance (program M))^[t]) ⟨some (.clearBefore 0),(.idle,none),S⟩ =
          ⟨none,v,step M S⟩ := by
  obtain ⟨t,ht,v,hr⟩ := ClockStepMachine.raw_run M (fromBank M S)
  have he := rename_run (order M) (Equiv.refl (ClockStepMachine.Label M))
    (Equiv.refl (ClockStepMachine.Control M)) (ClockStepMachine.program M)
      ⟨some (.clearBefore 0),(.idle,none),fromBank M S⟩ t
  change ((advance (program M))^[t])
      ⟨some (.clearBefore 0),(.idle,none),toBank M (fromBank M S)⟩ =
        renameCfg _ _ _ (ClockStepMachine.run M t _) at he
  rw [to_from,hr] at he
  refine ⟨t,?_,v,he⟩
  exact ht.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right (totalWords_le_encode M S) 1) 2))

theorem step_size (S : Fin (width M) → List Bool) :
    (BitMachineBankCodec.encode (step M S)).length ≤
      (3 * width M) * ((BitMachineBankCodec.encode S).length+1) := by
  have hword : ∀ i, (step M S i).length ≤ (BitMachineBankCodec.encode S).length+1 := by
    intro i
    apply ClockStepMachine.result_word_length M
    all_goals exact BitMachineBankCodec.word_length_le_encode S _
  have hsum : (∑ i, (step M S i).length) ≤
      width M * ((BitMachineBankCodec.encode S).length+1) := by
    calc
      _ ≤ ∑ _i : Fin (width M), ((BitMachineBankCodec.encode S).length+1) :=
        Finset.sum_le_sum (fun i _ => hword i)
      _ = _ := by simp
  rw [BitMachineBankCodec.encode_length]
  nlinarith

def result := BitMachineBankWrapper.result (step M)

noncomputable def machine : BitMachine.Machine :=
  BitMachineBankWrapper.machine (program M) (.clearBefore 0) (.idle,none)

def timeConstant : ℕ := 8 * width M + ClockStepMachine.rawBound M + 5

theorem outputs_all (input : List Bool) :
    (machine M).OutputsWithin input (result M input) (timeConstant M * (input.length+1)^2) := by
  have h := BitMachineBankWrapper.outputs (program M) (.clearBefore 0) (.idle,none)
    (step M) input (ClockStepMachine.rawBound M*(input.length+1)^2)
    (3*width M*(input.length+1)) (by
      intro S hd
      obtain ⟨t,ht,v,hr⟩ := raw_run M S
      rw [BitMachineBankCodec.encode_decode hd] at ht
      exact ⟨t,⟨none,v,step M S⟩,ht,hr,rfl,rfl⟩) (by
      intro S hd
      have hs := step_size M S
      rw [BitMachineBankCodec.encode_decode hd] at hs
      exact hs)
  apply BitMachine.outputsWithin_mono _ h
  have hlin : input.length+1 ≤ (input.length+1)^2 := by nlinarith
  have hone : 1 ≤ (input.length+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hscale := Nat.mul_le_mul_left (8*width M+1) hlin
  unfold timeConstant
  nlinarith

theorem polytime : BitMachine.Polytime (result M) := by
  exact ⟨machine M,timeConstant M,2,outputs_all M⟩

end
end EthInapproximability.CurrentPaper.ClockStepEncoded
