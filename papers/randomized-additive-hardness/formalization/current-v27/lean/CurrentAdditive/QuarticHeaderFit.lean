import CurrentAdditive.QuarticHeaderSize

/-! Eventual v27 classifier tape and clock fit on sparse source formulas. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite

theorem source_classifier_fit27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (cs : ℕ) (C : Paper2.SelectedTape.Algorithm) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      ∀ t : (select27 (t10_vertices_pos Dsrc Bsrc Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
          (t10Graph_valid Dsrc Bsrc Φ))
        Bsrc.degreeBound (sourceGap Dsrc Bsrc) (kOf Φ.val.variables)).Tape,
      C.tapeLength (Paper2.HeaderWordRun.headeredWord
        (kOf Φ.val.variables)
        (Paper2.ASquare.squareInstance
          (selectedInstance27 (t10_vertices_pos Dsrc Bsrc Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
              (t10Graph_valid Dsrc Bsrc Φ))
            Bsrc.degreeBound (sourceGap Dsrc Bsrc)
            (kOf Φ.val.variables) t))) ≤
        C.cR * Paper2.AEth.expLen Φ.val.variables := by
  obtain ⟨N₁, hN₁⟩ := source_square_poly_clock_fit27
    Dsrc Bsrc cs (332 * C.dR)
  refine ⟨max N₁ 36, ?_⟩
  intro Φ hsp hlarge t
  have hN₁' : N₁ ≤ Φ.val.variables := (le_max_left _ _).trans hlarge
  have h36 : 36 ≤ Φ.val.variables := (le_max_right _ _).trans hlarge
  have hk : 1 ≤ kOf Φ.val.variables :=
    Paper2.Unit4Shell.AsymptoticsExplicit.kOf_pos _ h36
  have hpoly := headerWord_length_le_poly27
    (t10_vertices_pos Dsrc Bsrc Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph Dsrc Bsrc Φ)
      (t10Graph_valid Dsrc Bsrc Φ))
    Bsrc.degreeBound (sourceGap Dsrc Bsrc)
    (kOf Φ.val.variables) hk t
  have hfit := hN₁ Φ hsp hN₁'
  have hpow := Nat.pow_le_pow_left hpoly C.dR
  simp only [Paper2.SelectedTape.Algorithm.tapeLength]
  apply Nat.mul_le_mul_left
  calc
    _ ≤ ((t10Graph Dsrc Bsrc Φ).vertices + 2) ^
        (332 * (kOf Φ.val.variables + 1) * C.dR) := by
          simpa only [pow_mul] using hpow
    _ = ((t10Graph Dsrc Bsrc Φ).vertices + 2) ^
        (332 * C.dR * (kOf Φ.val.variables + 1)) := by congr 1; ring
    _ ≤ Paper2.AEth.expLen Φ.val.variables := hfit

#print axioms source_classifier_fit27

end Paper2.CurrentAdditive.QuarticClassEndpoint
