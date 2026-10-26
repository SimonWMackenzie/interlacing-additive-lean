import CurrentAdditive.DynamicGetterPrimitives
import EthInapproximability.CurrentPaper.ProtocolBoundedUnary
import EthInapproximability.CurrentPaper.BitMachineBankWrapper

set_option maxHeartbeats 1000000
namespace CurrentAdditive.DynamicGetterBounded
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
noncomputable section

def packet (q cap : List Bool) :=
  BitMachineBankCodec.encode (![q,cap,[],[]] : Fin 4 → List Bool)
def wrapper := BitMachineBankWrapper.machine ProtocolBoundedUnary.program
  ProtocolBoundedUnary.Label.zeroScan (none,false)
def machine := BitMachineComposition.composition wrapper
  (BankFieldProjection.machine (3 : Fin 4))

theorem outputs (q cap : List Bool) : machine.OutputsWithin (packet q cap)
    (ProtocolBoundedUnary.result q cap []) (500*((packet q cap).length+1)^2) := by
  obtain ⟨t,c,ht,hc,hh,ho,hq,hw,hcap⟩ := ProtocolBoundedUnary.bounded_run_framed q cap []
  let packed := BitMachineBankCodec.encode c.stk
  have hd : BitMachineBankCodec.decode 4 (packet q cap) =
      some (![q,cap,[],[]] : Fin 4 → List Bool) := by simp [packet]
  have hr : ((advance ProtocolBoundedUnary.program)^[t])
      (⟨some ProtocolBoundedUnary.Label.zeroScan,(none,false),
        ![q,cap,[],[]]⟩ : TM2.Cfg (fun _ : Fin 4 => Bool)
          ProtocolBoundedUnary.Label ProtocolBoundedUnary.Control) = c := by
    have hb : ProtocolBoundedUnary.stackContents q cap [] [] =
        (![q,cap,[],[]] : Fin 4 → List Bool) := by
      funext k
      fin_cases k <;> rfl
    simpa only [ProtocolBoundedUnary.run,ProtocolBoundedUnary.cfg,hb] using hc
  obtain ⟨u,S',hu,hpacked⟩ := BitMachineBankWrapper.packed_run
    ProtocolBoundedUnary.program .zeroScan (none,false) (packet q cap)
    (![q,cap,[],[]] : Fin 4 → List Bool) hd t c hr hh
  have he : BitMachineBankSerialize.encode (List.ofFn c.stk) = packed := by
    dsimp only [packed]
    rw [BitMachineBankCodec.encode_eq_list]; rfl
  rw [he] at hu hpacked
  have hp : packed.length ≤ 2*q.length+4*cap.length+6 := by
    have hlo := ProtocolBoundedUnary.result_length q cap []
    have hmin : min (EncodedCommunication.bitsValue q) cap.length ≤ cap.length := min_le_right _ _
    change (BitMachineBankCodec.encode c.stk).length ≤ _
    rw [BitMachineBankCodec.encode_length]
    simp only [Fin.sum_univ_succ]
    change 2*((c.stk 0).length+((c.stk 1).length+((c.stk 2).length+
      ((c.stk 3).length+0))))+4 ≤ _
    rw [hq,hw,ho]
    simp only [List.length_nil] at *
    omega
  have h1 : wrapper.OutputsWithin (packet q cap) packed
      (9*((packet q cap).length+1)+t+2*packed.length+4) := by
    apply outputsWithin_of_raw_run (.inr 0) (.inr 2) (.inr (.parse (.scan 0)))
      ((none,false),none)
      (BitMachineBankWrapper.program ProtocolBoundedUnary.program .zeroScan (none,false))
      (packet q cap) packed u _ hu
    · rw [BitMachineBankWrapper.initial_cfg]
      change (BitMachineBankWrapper.run _ _ _ u _).l = none
      rw [hpacked]; rfl
    · rw [BitMachineBankWrapper.initial_cfg]
      change (BitMachineBankWrapper.run _ _ _ u _).stk (.inr 2) = packed
      rw [hpacked]; rfl
  have h2 : (BankFieldProjection.machine (3 : Fin 4)).OutputsWithin packed
      (ProtocolBoundedUnary.result q cap []) (12*(packed.length+1)) := by
    have h := BankFieldProjection.outputs (3 : Fin 4) packed
    have heq : BankFieldProjection.result (3 : Fin 4) packed =
        ProtocolBoundedUnary.result q cap [] := by
      rw [show packed = BitMachineBankCodec.encode c.stk from rfl,
        BankFieldProjection.result_encode,ho]
    simpa only [heq] using h
  apply BitMachine.outputsWithin_mono _
    (BitMachineComposition.composition_outputsWithin wrapper
      (BankFieldProjection.machine (3 : Fin 4)) h1 h2)
  have hin : (packet q cap).length = 2*q.length+2*cap.length+4 := by
    rw [packet,BitMachineBankCodec.encode_length]
    simp [Fin.sum_univ_succ]; omega
  nlinarith

#print axioms outputs
end
end CurrentAdditive.DynamicGetterBounded
