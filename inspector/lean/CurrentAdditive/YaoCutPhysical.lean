import CurrentAdditive.YaoDepthFuel
import CurrentAdditive.YaoCutScanLoop
import CurrentAdditive.YaoCutTester

/-! Instantiate the physical unary-fuel scan with the checked feasibility
tester. The resulting bank contains the locked source cut index, not a
preloaded answer. -/

namespace CurrentAdditive.SmallBias.YaoCutPhysical

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding
open YaoCutScanBody YaoCutScanLoop

def program (t : ℕ) :=
  scanProgram (YaoCutTester.program t)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    YaoCutTester.v1

def bound (b t : ℕ) : ℕ :=
  let a := sourcePairDepth b t
  let R := 2 ^ (t + b - 3)
  a * (scanBound (fun j => YaoCutTester.timeBound j t R) a + 1) + 1

theorem count_eq_cutCount (b t m : ℕ) :
    count (fun j => decide (sourceCutFeasible b t j)) m =
      YaoCutCounting.cutCount b t m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      by_cases h : sourceCutFeasible b t (m + 1) <;>
        simp [count, YaoCutCounting.cutCount, ih, h]

theorem run (S : Fin 16 → List Bool) (b t : ℕ)
    (ht : 4 ≤ t)
    (h5 : S 5 = List.replicate (sourcePairDepth b t) true)
    (h4 : S 4 = []) (h3 : S 3 = [])
    (h6 : S 6 = List.replicate (2 ^ (t + b - 3)) true)
    (h12 : S 12 = []) (hscratch : scratchEmpty S) :
    ∃ u ≤ bound b t,
      ((advance (program t))^[u])
        (⟨some (.inl ()), (none, bodyControl YaoCutTester.v1), S⟩ :
          TM2.Cfg (fun _ : Fin 16 => Bool) _ _) =
      ⟨none, (none, bodyControl YaoCutTester.v1),
        scanState S (sourcePairDepth b t)
          (fun j => decide (sourceCutFeasible b t j))
          (sourcePairDepth b t)⟩ := by
  let R := 2 ^ (t + b - 3)
  let B := fun j => YaoCutTester.timeBound j t R
  let g := fun j => decide (sourceCutFeasible b t j)
  have hTester : ∀ (T : Fin 16 → List Bool) (j : ℕ),
      T 4 = List.replicate j true →
      T 6 = List.replicate R true → T 12 = [] → scratchEmpty T →
      ∃ u ≤ B j,
        ((advance (YaoCutTester.program t))^[u])
          (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
            YaoCutTester.v1, T⟩ : TM2.Cfg (fun _ : Fin 16 => Bool) _ _) =
        ⟨none, YaoCutTester.v1, Function.update T 12 [g j]⟩ := by
    intro T j hj hR hO hw
    have h7 := hw 7 (by decide) (by decide)
    have h8 := hw 8 (by decide) (by decide)
    have h9 := hw 9 (by decide) (by decide)
    have h10 := hw 10 (by decide) (by decide)
    have h11 := hw 11 (by decide) (by decide)
    have h13 := hw 13 (by decide) (by decide)
    have h14 := hw 14 (by decide) (by decide)
    have h15 := hw 15 (by decide) (by decide)
    simpa only [B, g, R] using
      YaoCutTester.verdict_source b t j ht T hj hR
        h7 h8 h9 h10 h11 hO h13 h14 h15
  obtain ⟨u, hu, hr⟩ := scan_run (YaoCutTester.program t)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    YaoCutTester.v1 B g R (sourcePairDepth b t)
    hTester S h5 h4 h3 h6 h12 hscratch
  exact ⟨u, by simpa [bound, B, R] using hu, by simpa [program, B, g, R] using hr⟩

theorem output_cut (S : Fin 16 → List Bool) (b t : ℕ) (ht : 4 ≤ t) :
    scanState S (sourcePairDepth b t)
      (fun j => decide (sourceCutFeasible b t j))
      (sourcePairDepth b t) 3 =
        List.replicate (sourceCutIndex b t) true := by
  rw [scanState_3, count_eq_cutCount,
    YaoCutCounting.cutCount_full b t ht]

#print axioms run
#print axioms output_cut

end CurrentAdditive.SmallBias.YaoCutPhysical
