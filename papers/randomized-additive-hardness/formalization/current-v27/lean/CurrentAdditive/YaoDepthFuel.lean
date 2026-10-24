import CurrentAdditive.YaoThreshold
import EthInapproximability.CurrentPaper.SourceClauseFixedUnary

/-! Initialize the scan's unary fuel to the source pair depth from unary b
using a source-preserving copy and a fixed-t push program. -/

namespace CurrentAdditive.SmallBias.YaoDepthFuel

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding MatrixStage4ScalarPreparationOps

def copyEmbed : Fin 3 ↪ Fin 16 :=
  ⟨![0, 5, 7], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all⟩

def fixedExtra (t : ℕ) : ℕ := 2 * t - 2

def program (t : ℕ) :=
  BitMachineRawSequence.program
    (copyProgram copyEmbed)
    (SourceClauseFixedUnary.program (5 : Fin 16) (fixedExtra t))
    (0 : SourceClauseFixedUnary.Label (fixedExtra t)) none ()

theorem run (S : Fin 16 → List Bool) (b t : ℕ)
    (h0 : S 0 = List.replicate b true)
    (h5 : S 5 = []) (h7 : S 7 = []) :
    ∃ u ≤ (2 * b + 2) + (fixedExtra t + 1) + 1,
      ((advance (program t))^[u])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none, ()), S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool) _ _) =
      ⟨none, (none, ()),
        Function.update S 5 (List.replicate (b + fixedExtra t) true)⟩ := by
  let S1 := Function.update S (5 : Fin 16) (List.replicate b true)
  have hcopy : ((advance (copyProgram copyEmbed))^[2 * b + 2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool)
        BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, S1⟩ := by
    have hr := copy_run copyEmbed S h7
    simpa [copyEmbed, S1, h0, h5] using hr
  have hstart : SourceClauseFixedUnary.state (5 : Fin 16) S1
      (0 : SourceClauseFixedUnary.Label (fixedExtra t))
      (List.replicate b true) =
      (⟨some 0, (), S1⟩ : TM2.Cfg (fun _ : Fin 16 => Bool)
        (SourceClauseFixedUnary.Label (fixedExtra t)) Unit) := by
    simp [SourceClauseFixedUnary.state, S1]
  have hpush := SourceClauseFixedUnary.run_from (5 : Fin 16) S1
    (0 : SourceClauseFixedUnary.Label (fixedExtra t)) (fixedExtra t)
    (by simp) (List.replicate b true)
  rw [hstart] at hpush
  have hfinish : Function.update S1 5
      (List.replicate (fixedExtra t) true ++ List.replicate b true) =
      Function.update S 5 (List.replicate (b + fixedExtra t) true) := by
    simp only [← List.replicate_add]
    rw [Nat.add_comm (fixedExtra t) b, Function.update_idem]
  rw [hfinish] at hpush
  obtain ⟨u, hu, hr⟩ := BitMachineRawSequence.runs
    (copyProgram copyEmbed)
    (SourceClauseFixedUnary.program (5 : Fin 16) (fixedExtra t))
    BitMachineCopy.Label.scan (0 : SourceClauseFixedUnary.Label (fixedExtra t))
    none none () () S S1 _ (2 * b + 2) (fixedExtra t + 1)
    hcopy hpush
  exact ⟨u, hu, hr⟩

theorem fuel_value (b t : ℕ) (ht : 2 ≤ t) :
    b + fixedExtra t = sourcePairDepth b t := by
  unfold fixedExtra sourcePairDepth
  omega

#print axioms run

end CurrentAdditive.SmallBias.YaoDepthFuel
