import EthInapproximability.CurrentPaper.ClockStepEncoded

/-!
# Ordered packets of the three permanent clock fields

Source: frozen v8 `05-iteration.tex`. This file identifies the literal
initializer packet with the ordered stack codec and bounds its physical
length. It introduces no machine operation.
-/

namespace EthInapproximability.CurrentPaper.ClockPacketState

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open scoped BigOperators
open ClockStepEncoded

variable (M : BitMachine.Machine)

theorem order_inl (i : Fin 3) : (order M (.inl i)).val = i.val := rfl

theorem order_inr (i : ClockInputPreparation.Temp M) :
    (order M (.inr i)).val = 3 + (Fintype.equivFin _ i).val := rfl

def packet (active budget count : List Bool) : List Bool :=
  BitMachineBankCodec.encode (toBank M (ClockInputPreparation.readyBank M active budget count))

theorem packet_length (active budget count : List Bool) :
    (packet M active budget count).length =
      2 * (active.length + budget.length + count.length) + width M := by
  rw [packet,BitMachineBankCodec.encode_length]
  have he : (∑ i : Fin (width M),
      (toBank M (ClockInputPreparation.readyBank M active budget count) i).length) =
      ∑ i : ClockStepMachine.Stack M,
        (ClockInputPreparation.readyBank M active budget count i).length :=
    Equiv.sum_comp (order M).symm
      (fun i => (ClockInputPreparation.readyBank M active budget count i).length)
  rw [he]
  simp [ClockInputPreparation.readyBank,Fintype.sum_sum_type,Fin.sum_univ_succ,Nat.add_assoc]

theorem initial_bank (budget : List Bool) :
    fromBank M (ClockIterationInput.initialBank (ClockStepMachine.tempCount M) budget) =
      ClockInputPreparation.readyBank M [true] budget [] := by
  funext i
  cases i with
  | inl i =>
      fin_cases i
      · have hi : order M (.inl 0) = ⟨0,by unfold width; omega⟩ := Fin.ext (order_inl M 0)
        simp only [fromBank,hi]
        rfl
      · have hi : order M (.inl 1) = ⟨1,by unfold width; omega⟩ := Fin.ext (order_inl M 1)
        simp only [fromBank,hi]
        rfl
      · have hi : order M (.inl 2) = (0 : Fin (ClockStepMachine.tempCount M+1)).succ.succ :=
          Fin.ext (order_inl M 2)
        simp only [fromBank,hi,ClockIterationInput.initialBank_tail]
        rfl
  | inr i =>
      let j : Fin (ClockStepMachine.tempCount M+1) :=
        ⟨1+(Fintype.equivFin (ClockInputPreparation.Temp M) i).val,by
          have h := (Fintype.equivFin (ClockInputPreparation.Temp M) i).isLt
          change _ < ClockStepMachine.tempCount M at h
          omega⟩
      have hi : order M (.inr i) = j.succ.succ := by
        apply Fin.ext
        rw [order_inr]
        simp only [Fin.val_succ,j]
        omega
      simp only [fromBank,hi,ClockIterationInput.initialBank_tail]
      rfl

theorem packet_initial (budget : List Bool) :
    packet M [true] budget [] = ClockIterationInput.packet (ClockStepMachine.tempCount M) budget := by
  rw [ClockIterationInput.packet_eq_encode,packet,← initial_bank, to_from]
  rfl

theorem result_packet (active budget count : List Bool) :
    ClockStepEncoded.result M (packet M active budget count) =
      BitMachineBankCodec.encode (toBank M (ClockStepMachine.result M active budget count)) := by
  simp only [ClockStepEncoded.result,BitMachineBankWrapper.result,packet,
    BitMachineBankCodec.decode_encode]
  unfold ClockStepEncoded.step
  rw [from_to]
  rfl

theorem packet_decode (active budget count : List Bool) :
    BitMachineBankCodec.decode (width M) (packet M active budget count) =
      some (toBank M (ClockInputPreparation.readyBank M active budget count)) :=
  BitMachineBankCodec.decode_encode _

theorem packet_counter (active budget count : List Bool) :
    toBank M (ClockInputPreparation.readyBank M active budget count)
      (⟨2,by unfold width; omega⟩ : Fin (width M)) = count := by
  have h : (⟨2,by unfold width; omega⟩ : Fin (width M)) = order M (.inl 2) :=
    Fin.ext (order_inl M 2).symm
  rw [h]
  simp [toBank,ClockInputPreparation.readyBank]

end
end EthInapproximability.CurrentPaper.ClockPacketState
