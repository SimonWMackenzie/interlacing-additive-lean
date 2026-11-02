import CurrentAdditive.CompactIndexedRationalCode
import CurrentAdditive.IndexedRationalDenominator

/-! An arbitrary positive rational law on explicit finite positions is
compiled by denominator clearing, then sampled through the short binary
index codec. This supplies the generic recursive-code base premises. -/

namespace Paper2.CompactRationalRecursiveBase

open Paper2.RecursiveSamplingProgram Paper2.RecursiveSampling
open Paper2.RecursiveSamplingLaws Paper2.GeneratorCode
open Paper2.GeneratorSource Paper2.RecursiveLabelCodecScratch
open Paper2.IndexedRationalProgramBridge
open Paper2.IndexedRationalDenominator Paper2.CompactFinCodec

def rationalCode {n : ℕ} (μ : PositiveRationalLaw (Fin n)) : Code :=
  Paper2.CompactIndexedRationalCode.code (mass μ.weight)

theorem rationalCode_exact {n : ℕ} (hn : 0 < n)
    (μ : PositiveRationalLaw (Fin n)) :
    meaning (rationalCode μ) =
      Program.map (codec n).encode (rationalProgram hn μ) := by
  exact Paper2.CompactIndexedRationalCode.code_exact
    hn (mass μ.weight) (mass_pos μ)

theorem rationalProgram_generates {n : ℕ} (hn : 0 < n)
    (μ : PositiveRationalLaw (Fin n)) :
    Generates (rationalProgram hn μ) μ.toFiniteLaw :=
  Paper2.IndexedRationalDenominator.rationalProgram_generates hn μ

theorem recursive_rational_codes_exact
    {nr nc n s q₁ q₂ w Q : ℕ}
    [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (hnr : 0 < nr) (hnc : 0 < nc) (hs : 4 ≤ s)
    (μ : PositiveRationalLaw (Fin nr))
    (ν : PositiveRationalLaw (Fin nc)) (k : ℕ) :
    let C := carrierCodecs s q₁ q₂ w Q (codec nr) (codec nc)
      (defaultItemCodec n s) k
    let P := programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      (finCongr (Fintype.card_fin n)) hs
      (rationalProgram hnr μ) (rationalProgram hnc ν) k
    meaning (recursiveCodes n s q₁ q₂ w Q
      (rationalCode μ) (rationalCode ν) k).1 =
        Program.map C.1.encode P.1 ∧
      meaning (recursiveCodes n s q₁ q₂ w Q
        (rationalCode μ) (rationalCode ν) k).2 =
        Program.map C.2.encode P.2 := by
  exact recursiveCodes_exact hs (codec nr) (codec nc)
    (rationalProgram hnr μ) (rationalProgram hnc ν)
    (rationalCode μ) (rationalCode ν)
    (rationalCode_exact hnr μ) (rationalCode_exact hnc ν) k

#print axioms rationalCode_exact
#print axioms recursive_rational_codes_exact

end Paper2.CompactRationalRecursiveBase
