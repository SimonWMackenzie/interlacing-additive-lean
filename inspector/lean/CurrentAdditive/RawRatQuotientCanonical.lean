import EthInapproximability.CurrentPaper.BG34Canon
import EthInapproximability.CurrentPaper.CutoffBitMachine
import EthInapproximability.CurrentPaper.BitMachineBinaryDivision
import Mathlib.Tactic

/-!
The restoring division routine leaves a little-endian quotient word with
possible zero padding. This fixed three-stack pass removes the padding before
the word is placed in a RawRat packet. No host-level Nat.bits call is a
machine instruction; Nat.bits occurs only in the correctness statement.
-/
namespace CurrentAdditive.RawRatQuotientCanonical

open Turing
open EthInapproximability.CurrentPaper

theorem canon_exact (q : List Bool) :
    BG34Canon.canon q = (EncodedCommunication.bitsValue q).bits := by
  obtain ⟨m, hm⟩ := BG34Canon.canon_canonical q
  have hv := CutoffBitMachine.Totalizer.bitsValue_canon q
  rw [hm, EncodedCommunication.bitsValue_bits] at hv
  simpa [hm, hv]

theorem physical_run (q : List Bool) :
    BG34Canon.run (q.length + 1 + BG34Canon.trimTime q.reverse)
      (BG34Canon.cfg (some .rev) none q [] []) =
    BG34Canon.cfg none none [] []
      (EncodedCommunication.bitsValue q).bits := by
  simpa only [canon_exact] using BG34Canon.canon_run q

theorem physical_clock (q : List Bool) :
    q.length + 1 + BG34Canon.trimTime q.reverse ≤ 2 * q.length + 2 := by
  have h := BG34Canon.trimTime_le q.reverse
  simpa using (show q.length + 1 + BG34Canon.trimTime q.reverse ≤
      2 * q.length + 2 by
    rw [List.length_reverse] at h
    omega)

theorem divide_quotient_canonical (input divisor : List Bool)
    (hd : 0 < EncodedCommunication.bitsValue divisor) :
    let q := (BitMachineBinaryDivision.divideFrom input divisor [] []).2
    BG34Canon.canon q =
      (BitMachineBinaryDivision.msbValue input /
        EncodedCommunication.bitsValue divisor).bits := by
  have hspec := BitMachineBinaryDivision.standard_division_spec input divisor hd
  simpa only [canon_exact] using
    congrArg Nat.bits hspec.1

end CurrentAdditive.RawRatQuotientCanonical
