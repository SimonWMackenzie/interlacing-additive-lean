import CurrentAdditive.RawRatGCDStage
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! One fixed raw controller performs physical preparation and Euclidean GCD. -/
namespace CurrentAdditive.RawRatPreGCD

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding
open CurrentAdditive.CodeDCodec

abbrev PrepControl := (Option Bool × Option Bool) × (Option Bool × Option Bool)
abbrev GCDControl := (Unit × Option Bool) × BinaryGCDCore.Control

def program := BitMachineRawSequence.program
  RawRatPreparation.program RawRatGCDStage.program
  (BitMachineRawSequence.leftLabel (0 : Fin 7))
  ((none, none), (none, none))
  (((), none), BinaryGCDCore.initial)

def clock (r : RawRat) : Nat :=
  3 * (r.numerator.length + r.denominator.length) + 10 +
    RawRatGCDStage.localClock r

theorem run (r : RawRat) :
    ∃ (t : Nat) (v : GCDControl), t ≤ clock r ∧
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
          (((none, none), (none, none)),
            (((), none), BinaryGCDCore.initial)),
          RawRatPreparation.inputBank r⟩ : TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, (((none, none), (none, none)), v), RawRatGCDStage.result r⟩ := by
  obtain ⟨tp, htp, hp⟩ := RawRatPreparation.prepared_run r
  obtain ⟨vg, hg⟩ := RawRatGCDStage.run r
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    RawRatPreparation.program RawRatGCDStage.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (BitMachineRawSequence.leftLabel (0 : Fin 7))
    ((none, none), (none, none)) ((none, none), (none, none))
    (((), none), BinaryGCDCore.initial) vg
    (RawRatPreparation.inputBank r) (RawRatPreparation.prepared r)
    (RawRatGCDStage.result r) tp (RawRatGCDStage.localClock r) hp hg
  refine ⟨t, vg, ?_, hr⟩
  unfold clock
  omega

theorem divisor_value (r : RawRat) (hr : r.Valid) :
    EncodedCommunication.bitsValue (RawRatGCDStage.result r 4) =
      CurrentAdditive.BinaryGCDNormalization.commonDivisor r :=
  RawRatGCDStage.result_divisor_value r hr

end CurrentAdditive.RawRatPreGCD
