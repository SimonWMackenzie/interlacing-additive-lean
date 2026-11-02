import CurrentAdditive.GenericRecursiveGeneratorClock
import CurrentAdditive.CompactRationalPacket
import CurrentAdditive.CompactRationalRecursiveBase

/-! Bind the generic fixed code-building machine to the actual rational
row and column laws carried by an arbitrary indexed base packet.  The
separate support code used by entry navigation does not replace these
weighted generator codes. -/

namespace Paper2.GenericRationalPacketGenerator

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSource
open Paper2.GeneratorSerialization
open Paper2.GenericRecursiveCodeSize
open Paper2.GenericRecursiveGeneratorClock
open Paper2.CompactRationalPacket
open Paper2.CompactRationalRecursiveBase
open Paper2.RecursiveLabelCodecScratch
open Paper2.CompactFinCodec
open Paper2.RecursiveSampling Paper2.RecursiveSamplingLaws
open Paper2.RecursiveSamplingProgram

set_option maxHeartbeats 4000000

theorem packet_generator_run
    {nr nc n s q₁ q₂ w Q : ℕ}
    [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (P : Packet nr nc) (k L : ℕ)
    (hs : 4 ≤ s)
    (hn : n ≤ 2 ^ L) (hsize : s ≤ 2 ^ L)
    (hq₁ : q₁ ≤ 2 ^ L) (hq₂ : q₂ ≤ 2 ^ L)
    (hw : w ≤ 2 ^ L) (hQ : Q ≤ 2 ^ L)
    (hbase : baseSize (rowCode P) (colCode P) ≤ 2 ^ L) :
    ∃ t ≤ 2 ^ (Paper2.CodeGeneratorExponentPublic.coeff + (k + 1) +
        (9 * (k + 1) * (L + 10)) * 6),
      ((advance Paper2.CodeRecursiveLoop.program)^[t])
        (Paper2.CodeRecursiveLoop.ready n s q₁ q₂ w Q
          (rowCode P) (colCode P) (List.replicate k true)) =
        Paper2.CodeRecursiveLoop.finished n s q₁ q₂ w Q
          (recursiveCodes n s q₁ q₂ w Q (rowCode P) (colCode P) k).1
          (recursiveCodes n s q₁ q₂ w Q (rowCode P) (colCode P) k).2 := by
  exact generator_run_exp n s q₁ q₂ w Q L k
    (rowCode P) (colCode P) (by omega)
    hn hsize hq₁ hq₂ hw hQ hbase

theorem packet_generator_law
    {nr nc n s q₁ q₂ w Q : ℕ}
    [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (P : Packet nr nc) (hnr : 0 < nr) (hnc : 0 < nc)
    (hs : 4 ≤ s) (k : ℕ) :
    let C := carrierCodecs s q₁ q₂ w Q (codec nr) (codec nc)
      (defaultItemCodec n s) k
    let G := programs
      (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      (finCongr (Fintype.card_fin n)) hs
      (Paper2.IndexedRationalDenominator.rationalProgram hnr P.rowLaw)
      (Paper2.IndexedRationalDenominator.rationalProgram hnc P.colLaw) k
    meaning (recursiveCodes n s q₁ q₂ w Q (rowCode P) (colCode P) k).1 =
        Program.map C.1.encode G.1 ∧
      meaning (recursiveCodes n s q₁ q₂ w Q (rowCode P) (colCode P) k).2 =
        Program.map C.2.encode G.2 := by
  exact recursive_rational_codes_exact hnr hnc hs P.rowLaw P.colLaw k

#print axioms packet_generator_run
#print axioms packet_generator_law

end Paper2.GenericRationalPacketGenerator
