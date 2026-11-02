import CurrentAdditive.IndexedRationalRecursiveBase
import CurrentAdditive.RandomizedQuarticSchedule
import Paper2.CodeRecursiveLoop

/-! Literal v27 quartic width and public-ticket cardinality, with the
same concrete indexed base codes passed to the fixed recursive controller. -/

namespace Paper2.IndexedRationalQuarticController

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.RecursiveSamplingProgram Paper2.RecursiveSampling
open Paper2.RecursiveLabelCodecScratch Paper2.GeneratorCode
open Paper2.GeneratorSource Paper2.IndexedRationalFinCode
open Paper2.IndexedRationalProgramBridge
open Paper2.IndexedRationalRecursiveBase
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

theorem run_quartic_codes27
    {nr nc n : ℕ} [NeZero n]
    (wr : Fin nr → ℕ) (wc : Fin nc → ℕ)
    (L Δ : ℕ) (γ : ℚ) (k : ℕ) :
    ∃ t ≤ Paper2.CodeRecursiveLoop.totalClock n (width L)
        (width L - 2) (outerWidth L) (width27 L)
        (Q27 (V := V) (E := E) L γ Δ)
        (code nr wr) (code nc wc) k,
      ((advance Paper2.CodeRecursiveLoop.program)^[t])
        (Paper2.CodeRecursiveLoop.ready n (width L)
          (width L - 2) (outerWidth L) (width27 L)
          (Q27 (V := V) (E := E) L γ Δ)
          (code nr wr) (code nc wc) (List.replicate k true)) =
        Paper2.CodeRecursiveLoop.finished n (width L)
          (width L - 2) (outerWidth L) (width27 L)
          (Q27 (V := V) (E := E) L γ Δ)
          (recursiveCodes n (width L) (width L - 2) (outerWidth L)
            (width27 L) (Q27 (V := V) (E := E) L γ Δ)
            (code nr wr) (code nc wc) k).1
          (recursiveCodes n (width L) (width L - 2) (outerWidth L)
            (width27 L) (Q27 (V := V) (E := E) L γ Δ)
            (code nr wr) (code nc wc) k).2 := by
  exact Paper2.CodeRecursiveLoop.run_k n (width L) (width L - 2)
    (outerWidth L) (width27 L)
    (Q27 (V := V) (E := E) L γ Δ)
    (code nr wr) (code nc wc) k (by
      have := SourceProfiles.width_ge_four L
      omega)

#print axioms run_quartic_codes27

/-- The physical fixed controller and the exact recursive code law are
assembled for the literal quartic schedule. The explicit input arrays are
positive integer masses; their rational laws are proved by `base_laws_exact`. -/
theorem quartic_codes_and_run27
    {nr nc n : ℕ} [NeZero n]
    (hnr : 0 < nr) (hnc : 0 < nc)
    (wr : Fin nr → ℕ) (wc : Fin nc → ℕ)
    (hwr : ∀ i, 0 < wr i) (hwc : ∀ j, 0 < wc j)
    (L Δ : ℕ) (γ : ℚ) (k : ℕ) :
    let s := width L
    let q₁ := s - 2
    let q₂ := outerWidth L
    let w := width27 L
    let Q := Q27 (V := V) (E := E) L γ Δ
    let C := carrierCodecs s q₁ q₂ w Q (finCodec nr) (finCodec nc)
      (defaultItemCodec n s) k
    let P := programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      (finCongr (Fintype.card_fin n)) (SourceProfiles.width_ge_four L)
      (program hnr (indices nr wr)) (program hnc (indices nc wc)) k
    (meaning (recursiveCodes n s q₁ q₂ w Q (code nr wr) (code nc wc) k).1 =
        Program.map C.1.encode P.1 ∧
      meaning (recursiveCodes n s q₁ q₂ w Q (code nr wr) (code nc wc) k).2 =
        Program.map C.2.encode P.2) ∧
    (∃ t ≤ Paper2.CodeRecursiveLoop.totalClock n s q₁ q₂ w Q
        (code nr wr) (code nc wc) k,
      ((advance Paper2.CodeRecursiveLoop.program)^[t])
        (Paper2.CodeRecursiveLoop.ready n s q₁ q₂ w Q
          (code nr wr) (code nc wc) (List.replicate k true)) =
        Paper2.CodeRecursiveLoop.finished n s q₁ q₂ w Q
          (recursiveCodes n s q₁ q₂ w Q (code nr wr) (code nc wc) k).1
          (recursiveCodes n s q₁ q₂ w Q (code nr wr) (code nc wc) k).2) := by
  exact ⟨recursive_indexed_codes_exact hnr hnc
    (SourceProfiles.width_ge_four L) wr wc hwr hwc k,
    run_quartic_codes27 wr wc L Δ γ k⟩

#print axioms quartic_codes_and_run27

end Paper2.IndexedRationalQuarticController
