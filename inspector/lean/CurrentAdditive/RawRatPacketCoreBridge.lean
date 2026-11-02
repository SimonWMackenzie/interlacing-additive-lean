import CurrentAdditive.RawRatPacketValidate
import CurrentAdditive.RawRatCoreBytes
import Mathlib.Tactic

namespace CurrentAdditive.RawRatPacketCoreBridge

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding
open CurrentAdditive.CodeDCodec
open CurrentAdditive.RawRatPacketWrapper

def coreInitial :=
  (RawRatCoreController.firstInitial, RawRatCoreController.secondInitial)

theorem input_eq (r : RawRat) :
    inputBank (rawRatBank r) = RawRatPreparation.inputBank r := by
  funext i
  fin_cases i <;> simp [inputBank, rawRatBank, RawRatPreparation.inputBank]

theorem selected_eq (r : RawRat) (hr : r.Valid) :
    selected (RawRatCoreController.result r) =
      rawRatBank (CodeDCanonicalSource.rawOfRat r.value) := by
  convert RawRatCoreBytes.selected_exact r hr using 1
  funext i
  fin_cases i <;> rfl

theorem encoded_eq (r : RawRat) (hr : r.Valid) :
    BitMachineBankSerialize.encode
      (List.ofFn (selected (RawRatCoreController.result r))) =
      encodeRawRat (CodeDCanonicalSource.rawOfRat r.value) := by
  rw [selected_eq r hr]
  exact (BitMachineBankCodec.encode_eq_list _).symm

theorem packed_run (r : RawRat) :
    ∃ t ≤ 7*((encodeRawRat r).length+1) + 2 +
        RawRatCoreController.clock r +
        2*(BitMachineBankSerialize.encode
          (List.ofFn (selected (RawRatCoreController.result r)))).length+4,
      let c := RawRatPacketWrapper.run RawRatCoreController.program
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))
        coreInitial t
        (cfg (some (.inl (.scan 0))) (coreInitial,none)
          (fun _ => []) (encodeRawRat r) [] [])
      c.l = none ∧ c.stk (.inr 2) =
        BitMachineBankSerialize.encode
          (List.ofFn (selected (RawRatCoreController.result r))) := by
  obtain ⟨q,hq,hv⟩ := RawRatPacketValidate.sign_valid
    RawRatCoreController.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))
    coreInitial r
  obtain ⟨t,v,ht,hcore⟩ := RawRatCoreController.run r
  have hd : BitMachineBankCodec.decode 3 (encodeRawRat r) = some (rawRatBank r) := by
    simp [encodeRawRat]
  have hcore' : ((advance RawRatCoreController.program)^[t])
      (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))),
        coreInitial,inputBank (rawRatBank r)⟩ :
        TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
      ⟨none, (RawRatCoreController.firstInitial,
          (((((), none), none), (BitMachineBinaryDivision.initial, none)),
            (none, v))), RawRatCoreController.result r⟩ := by
    simpa only [coreInitial, input_eq] using hcore
  obtain ⟨u,hu,hr⟩ := RawRatPacketWrapper.packed_run
    RawRatCoreController.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))
    coreInitial (encodeRawRat r)
    (rawRatBank r) (RawRatCoreController.result r)
    (RawRatCoreController.firstInitial,
      (((((), none), none), (BitMachineBinaryDivision.initial, none)),
        (none, v))) t q hd hv hcore'
  exact ⟨u, by omega, hr⟩

end CurrentAdditive.RawRatPacketCoreBridge
