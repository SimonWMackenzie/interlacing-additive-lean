import CurrentAdditive.RawRatCopyEmbedded
import CurrentAdditive.RawRatReverseTransfer
import CurrentAdditive.RationalCanonical
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import Mathlib.Tactic

/-!
One fixed eight-stack preprocessing program preserves the sign and originals,
and prepares the exact pair expected by the physical Euclidean GCD routine:
MSB-first numerator and LSB-first denominator.
-/
namespace CurrentAdditive.RawRatPreparation

open Turing
open EthInapproximability.CurrentPaper
open BitMachineEncoding
open CurrentAdditive.CodeDCodec

abbrev Bank := Fin 13 → List Bool

def inputBank (r : RawRat) : Bank := fun k =>
  if k = 0 then (if r.negative then [true] else []) else
  if k = 1 then r.numerator else
  if k = 2 then r.denominator else []

def copyNum : Fin 3 ↪ Fin 13 where
  toFun i := if i = 0 then 1 else if i = 1 then 5 else 7
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def copyDen : Fin 3 ↪ Fin 13 where
  toFun i := if i = 0 then 2 else if i = 1 then 6 else 7
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def afterNumCopy (r : RawRat) : Bank :=
  Function.update (inputBank r) 5 r.numerator

def afterDenCopy (r : RawRat) : Bank :=
  Function.update (afterNumCopy r) 6 r.denominator

def afterNumReverse (r : RawRat) : Bank :=
  Function.update (Function.update (afterDenCopy r) 1 []) 3 r.numerator.reverse

def prepared (r : RawRat) : Bank :=
  Function.update (Function.update (afterNumReverse r) 2 []) 4 r.denominator.reverse

theorem copyNum_run (r : RawRat) :
    ((advance (RawRatCopyEmbedded.program copyNum))^[2 * r.numerator.length + 2])
      (⟨some BitMachineCopy.Label.scan, none, inputBank r⟩ :
        TM2.Cfg (fun _ : Fin 13 => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, afterNumCopy r⟩ := by
  have h := RawRatCopyEmbedded.run_correct copyNum (inputBank r)
    (by simp [copyNum, inputBank]) (by simp [copyNum, inputBank])
  simpa [copyNum, inputBank, afterNumCopy] using h

theorem copyDen_run (r : RawRat) :
    ((advance (RawRatCopyEmbedded.program copyDen))^[2 * r.denominator.length + 2])
      (⟨some BitMachineCopy.Label.scan, none, afterNumCopy r⟩ :
        TM2.Cfg (fun _ : Fin 13 => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, afterDenCopy r⟩ := by
  have h := RawRatCopyEmbedded.run_correct copyDen (afterNumCopy r)
    (by simp [copyDen, afterNumCopy, inputBank])
    (by simp [copyDen, afterNumCopy, inputBank])
  simpa [copyDen, afterNumCopy, afterDenCopy, inputBank] using h

theorem reverseNum_run (r : RawRat) :
    RawRatReverseTransfer.run (1 : Fin 13) 3 (r.numerator.length + 1)
      (RawRatReverseTransfer.cfg (some .move) none (afterDenCopy r)) =
      RawRatReverseTransfer.cfg none none (afterNumReverse r) := by
  have h := RawRatReverseTransfer.run_correct (1 : Fin 13) 3 (by decide)
    (afterDenCopy r) none
  simpa [afterDenCopy, afterNumCopy, afterNumReverse, inputBank] using h

theorem reverseDen_run (r : RawRat) :
    RawRatReverseTransfer.run (2 : Fin 13) 4 (r.denominator.length + 1)
      (RawRatReverseTransfer.cfg (some .move) none (afterNumReverse r)) =
      RawRatReverseTransfer.cfg none none (prepared r) := by
  have h := RawRatReverseTransfer.run_correct (2 : Fin 13) 4 (by decide)
    (afterNumReverse r) none
  simpa [afterNumReverse, afterDenCopy, afterNumCopy, prepared, inputBank] using h

def copies := BitMachineRawSequence.program
  (RawRatCopyEmbedded.program copyNum) (RawRatCopyEmbedded.program copyDen)
  BitMachineCopy.Label.scan (none : Option Bool) (none : Option Bool)

def reversals := BitMachineRawSequence.program
  (RawRatReverseTransfer.program (1 : Fin 13) 3)
  (RawRatReverseTransfer.program (2 : Fin 13) 4)
  RawRatReverseTransfer.Label.move (none : Option Bool) (none : Option Bool)

def program := BitMachineRawSequence.program copies reversals
  (BitMachineRawSequence.leftLabel RawRatReverseTransfer.Label.move)
  ((none : Option Bool), (none : Option Bool))
  ((none : Option Bool), (none : Option Bool))

theorem copies_run (r : RawRat) :
    ∃ t ≤ 2 * r.numerator.length + 2 +
        (2 * r.denominator.length + 2) + 1,
      ((advance copies)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, none), inputBank r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool)
            (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
            (Option Bool × Option Bool)) =
        ⟨none, (none, none), afterDenCopy r⟩ := by
  exact BitMachineRawSequence.runs _ _
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan none none none none
    (inputBank r) (afterNumCopy r) (afterDenCopy r)
    (2 * r.numerator.length + 2) (2 * r.denominator.length + 2)
    (copyNum_run r) (copyDen_run r)

theorem reversals_run (r : RawRat) :
    ∃ t ≤ (r.numerator.length + 1) + (r.denominator.length + 1) + 1,
      ((advance reversals)^[t])
        (⟨some (BitMachineRawSequence.leftLabel RawRatReverseTransfer.Label.move),
          (none, none), afterDenCopy r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool)
            (BitMachineRawSequence.Label RawRatReverseTransfer.Label
              RawRatReverseTransfer.Label)
            (Option Bool × Option Bool)) =
        ⟨none, (none, none), prepared r⟩ := by
  exact BitMachineRawSequence.runs _ _ .move .move none none none none
    (afterDenCopy r) (afterNumReverse r) (prepared r)
    (r.numerator.length + 1) (r.denominator.length + 1)
    (reverseNum_run r) (reverseDen_run r)

theorem prepared_run (r : RawRat) :
    ∃ t ≤ 3 * (r.numerator.length + r.denominator.length) + 9,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none, none), (none, none)), inputBank r⟩ :
          TM2.Cfg (fun _ : Fin 13 => Bool) _ _) =
        ⟨none, ((none, none), (none, none)), prepared r⟩ := by
  obtain ⟨ta, hta, ha⟩ := copies_run r
  obtain ⟨tb, htb, hb⟩ := reversals_run r
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs copies reversals
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel RawRatReverseTransfer.Label.move)
    (none, none) (none, none) (none, none) (none, none)
    (inputBank r) (afterDenCopy r) (prepared r) ta tb ha hb
  refine ⟨t, by omega, ?_⟩
  exact hr

end CurrentAdditive.RawRatPreparation
