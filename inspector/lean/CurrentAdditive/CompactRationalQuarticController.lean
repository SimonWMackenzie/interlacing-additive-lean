import CurrentAdditive.CompactRationalRecursiveBase
import Paper2.CodeRecursiveLoop
import CurrentAdditive.RandomizedQuarticSchedule

/-! Concrete compact rational base codes through the fixed recursive
controller at the literal v27 quartic parameter schedule. -/

namespace Paper2.CompactRationalQuarticController

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.RecursiveSamplingProgram Paper2.RecursiveSampling
open Paper2.RecursiveLabelCodecScratch Paper2.GeneratorCode
open Paper2.GeneratorSource Paper2.CompactFinCodec
open Paper2.CompactRationalRecursiveBase
open CurrentAdditive.RandomizedSchedule
open Paper2.SourceProfileParameters

variable {V E : Type*} [Fintype V] [Fintype E]

local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩
local instance (L : ℕ) : NeZero (outerWidth L) :=
  ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width27 L) :=
  ⟨by unfold width27; positivity⟩
local instance (L Δ : ℕ) (γ : ℚ) :
    NeZero (Q27 (V := V) (E := E) L γ Δ) := ⟨by
  unfold Q27
  exact Nat.ne_of_gt (RestorationPublicQScratch.publicQ_pos _ _)⟩

/-- The same literal recursive code is both produced by the fixed controller
and denotes the exact indexed rational source program. -/
theorem compact_rational_quartic_and_run27
    {nr nc n : ℕ} [NeZero n]
    (hnr : 0 < nr) (hnc : 0 < nc)
    (μ : PositiveRationalLaw (Fin nr))
    (ν : PositiveRationalLaw (Fin nc))
    (L Δ : ℕ) (γ : ℚ) (k : ℕ) :
    let s := width L
    let q₁ := s - 2
    let q₂ := outerWidth L
    let w := width27 L
    let Q := Q27 (V := V) (E := E) L γ Δ
    let C := carrierCodecs s q₁ q₂ w Q (codec nr) (codec nc)
      (defaultItemCodec n s) k
    let P := programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      (finCongr (Fintype.card_fin n)) (SourceProfiles.width_ge_four L)
      (Paper2.IndexedRationalDenominator.rationalProgram hnr μ)
      (Paper2.IndexedRationalDenominator.rationalProgram hnc ν) k
    (meaning (recursiveCodes n s q₁ q₂ w Q
      (rationalCode μ) (rationalCode ν) k).1 =
        Program.map C.1.encode P.1 ∧
      meaning (recursiveCodes n s q₁ q₂ w Q
        (rationalCode μ) (rationalCode ν) k).2 =
        Program.map C.2.encode P.2) ∧
    (∃ t ≤ Paper2.CodeRecursiveLoop.totalClock n s q₁ q₂ w Q
        (rationalCode μ) (rationalCode ν) k,
      ((advance Paper2.CodeRecursiveLoop.program)^[t])
        (Paper2.CodeRecursiveLoop.ready n s q₁ q₂ w Q
          (rationalCode μ) (rationalCode ν) (List.replicate k true)) =
        Paper2.CodeRecursiveLoop.finished n s q₁ q₂ w Q
          (recursiveCodes n s q₁ q₂ w Q
            (rationalCode μ) (rationalCode ν) k).1
          (recursiveCodes n s q₁ q₂ w Q
            (rationalCode μ) (rationalCode ν) k).2) := by
  exact ⟨recursive_rational_codes_exact hnr hnc
    (SourceProfiles.width_ge_four L) μ ν k,
    Paper2.CodeRecursiveLoop.run_k n (width L) (width L - 2)
      (outerWidth L) (width27 L)
      (Q27 (V := V) (E := E) L γ Δ)
      (rationalCode μ) (rationalCode ν) k (by
        have := SourceProfiles.width_ge_four L
        omega)⟩

#print axioms compact_rational_quartic_and_run27

end Paper2.CompactRationalQuarticController
