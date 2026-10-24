import CurrentAdditive.IndexedRationalLawBridge

/-! A concrete arbitrary finite rational base generator can be used by the
existing recursive code constructor. Both sides retain indexed positions. -/

namespace Paper2.IndexedRationalRecursiveBase

open Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingLaws
open Paper2.RecursiveSampling
open Paper2.RecursiveLabelCodecScratch Paper2.GeneratorCode
open Paper2.GeneratorSource Paper2.IndexedRationalFinCode
open Paper2.IndexedRationalProgramBridge Paper2.IndexedRationalLawBridge

/-- The two base codes denote the exact encoded row and column programs. -/
theorem base_codes_exact {nr nc : ℕ} (hnr : 0 < nr) (hnc : 0 < nc)
    (wr : Fin nr → ℕ) (wc : Fin nc → ℕ)
    (hwr : ∀ i, 0 < wr i) (hwc : ∀ j, 0 < wc j) :
    meaning (code nr wr) =
        Program.map (finCodec nr).encode (program hnr (indices nr wr)) ∧
      meaning (code nc wc) =
        Program.map (finCodec nc).encode (program hnc (indices nc wc)) := by
  exact ⟨code_exact hnr wr hwr, code_exact hnc wc hwc⟩

/-- Exact finite input laws for the same indexed base programs. -/
theorem base_laws_exact {nr nc : ℕ} (hnr : 0 < nr) (hnc : 0 < nc)
    (wr : Fin nr → ℕ) (wc : Fin nc → ℕ)
    (hwr : ∀ i, 0 < wr i) (hwc : ∀ j, 0 < wc j) :
    Generates (program hnr (indices nr wr)) (law hnr wr hwr).toFiniteLaw ∧
      Generates (program hnc (indices nc wc)) (law hnc wc hwc).toFiniteLaw := by
  exact ⟨program_generates hnr wr hwr, program_generates hnc wc hwc⟩

/-- The ordinary generic recursive generator is now instantiated with
actual first-order codes for arbitrary finite indexed rational inputs. -/
theorem recursive_indexed_codes_exact
    {nr nc n s q₁ q₂ w Q : ℕ}
    [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (hnr : 0 < nr) (hnc : 0 < nc) (hs : 4 ≤ s)
    (wr : Fin nr → ℕ) (wc : Fin nc → ℕ)
    (hwr : ∀ i, 0 < wr i) (hwc : ∀ j, 0 < wc j) (k : ℕ) :
    let C := carrierCodecs s q₁ q₂ w Q (finCodec nr) (finCodec nc)
      (defaultItemCodec n s) k
    let P := programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      (finCongr (Fintype.card_fin n)) hs
      (program hnr (indices nr wr)) (program hnc (indices nc wc)) k
    meaning (recursiveCodes n s q₁ q₂ w Q (code nr wr) (code nc wc) k).1 =
        Program.map C.1.encode P.1 ∧
      meaning (recursiveCodes n s q₁ q₂ w Q (code nr wr) (code nc wc) k).2 =
        Program.map C.2.encode P.2 := by
  exact recursiveCodes_exact hs (finCodec nr) (finCodec nc)
    (program hnr (indices nr wr)) (program hnc (indices nc wc))
    (code nr wr) (code nc wc)
    (code_exact hnr wr hwr) (code_exact hnc wc hwc) k

#print axioms recursive_indexed_codes_exact

end Paper2.IndexedRationalRecursiveBase
