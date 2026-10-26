import CurrentAdditive.QuarticSourceClockFit
import Paper2.E7SqHd

/-!
# Physical formula header after the literal v27 square printer

The fixed machine preserves the formula while running a supplied v27 square
printer on the selected bank, then writes the gap header using the formula's
variable count. The theorem proves output identity; a tape-independent
closed clock for the full source decider is a later stage.
-/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.AEth4 Paper2.AEth5

noncomputable def headerMachine27 (M : BitMachine.Machine) : BitMachine.Machine :=
  BitMachineComposition.composition Pack.machine
    (BitMachineComposition.composition
      (Paper2.Unit4Shell.PairMap.machine M)
      (BitMachineComposition.composition Paper2.Unit4Shell.KofLoops.Swap.machine
        (BitMachineComposition.composition PairConcat.machine KHeader.machine)))

noncomputable def headerClock27 (Φ : EncodedCNF.Formula)
    (bank : List Bool) (i : EncodedCommunication.Instance) (T₀ : ℕ) : ℕ :=
  let e := EncodedCNF.encode Φ
  let so := EncodedCommunication.encodeInstance (Paper2.ASquare.squareInstance i)
  let f := EncodedCommunication.field e
  let w₀ := EncodedComplexity.pair e bank
  let w₁ := EncodedComplexity.pair w₀ (EncodedComplexity.pair f [])
  let w₂ := EncodedComplexity.pair so (EncodedComplexity.pair f [])
  let w₃ := EncodedComplexity.pair f (EncodedComplexity.pair so [])
  let w₄ := EncodedComplexity.pair e so
  8 * (w₀.length + 2) + 2 * w₁.length + 2 +
    ((2 * w₀.length + T₀ + 2 * so.length + 6) + 2 * w₂.length + 2 +
      ((3 * (w₂.length + 1)) + 2 * w₃.length + 2 +
        ((3 * (w₃.length + 1)) + 2 * w₄.length + 2 +
          KHeader.clock Φ (Paper2.ASquare.squareInstance i))))

theorem headerMachine27_outputs (M : BitMachine.Machine)
    (Φ : EncodedCNF.Formula)
    (hk : 1 ≤ Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)
    (bank : List Bool) (i : EncodedCommunication.Instance) (T₀ : ℕ)
    (hM : M.OutputsWithin (EncodedComplexity.pair (EncodedCNF.encode Φ) bank)
      (EncodedCommunication.encodeInstance (Paper2.ASquare.squareInstance i)) T₀) :
    (headerMachine27 M).OutputsWithin
        (EncodedComplexity.pair (EncodedCNF.encode Φ) bank)
        (Paper2.HeaderWordRun.headeredWord
          (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)
          (Paper2.ASquare.squareInstance i)) (headerClock27 Φ bank i T₀) := by
  let e := EncodedCNF.encode Φ
  let so := EncodedCommunication.encodeInstance (Paper2.ASquare.squareInstance i)
  have h2 := Pack.outputs e bank
  have h3 := Paper2.Unit4Shell.PairMap.machine_outputs (M := M)
    (EncodedComplexity.pair e bank) so (EncodedComplexity.pair
      (EncodedCommunication.field e) []) _ hM
  have h4 := Paper2.Unit4Shell.KofLoops.Swap.machine_outputs so
    (EncodedCommunication.field e) []
  have h5 := PairConcat.outputs
    (EncodedComplexity.pair (EncodedCommunication.field e)
      (EncodedComplexity.pair so []))
  rw [PairConcat.concat_pair] at h5
  have h6 := KHeader.machine_outputs Φ hk (Paper2.ASquare.squareInstance i)
  have hfe : EncodedCommunication.field e ++ so =
      EncodedComplexity.pair e so := rfl
  rw [hfe] at h5
  have hC := BitMachineComposition.composition_outputsWithin _ _ h2
    (BitMachineComposition.composition_outputsWithin _ _ h3
      (BitMachineComposition.composition_outputsWithin _ _ h4
        (BitMachineComposition.composition_outputsWithin _ _ h5 h6)))
  simpa only [headerClock27] using hC

theorem headerWord27_eq_square_classifier_word {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    let o := select27 hn edge Δ γ k
    let q := SquarePadding.side o.rows o.cols
    Paper2.HeaderWordRun.headeredWord k
      (Paper2.ASquare.squareInstance (selectedInstance27 hn edge Δ γ k t)) =
      EncodedCommunication.natField (2 * o.budget + k) ++
        AModel.matrixWord q q
          (MatrixMaterialization.rowMajor (Paper2.ASquare.squareTable o t)) := by
  rfl

#print axioms headerMachine27_outputs
#print axioms headerWord27_eq_square_classifier_word

end Paper2.CurrentAdditive.QuarticClassEndpoint
