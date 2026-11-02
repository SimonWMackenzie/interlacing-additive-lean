import CurrentAdditive.QuarticSquarePoly
import Paper2.E3Inner

/-!
# Subexponential source bound for the actual v27 square printer

For each fixed machine exponent, sparse source graphs grow slowly enough
that the square printer's `(n+2)^(E(k+1))` clock fits the inherited
`expLen N` budget. This is the graph-bank-to-square-instance stage only.
-/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2 Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.CurrentAdditive.QuarticConstructor
open Paper2.CurrentAdditive.QuarticMachineWrapper

theorem source_square_poly_clock_fit27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (cs E : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables →
      ((t10Graph Dsrc Bsrc Φ).vertices + 2) ^
        (E * (kOf Φ.val.variables + 1)) ≤
        Paper2.AEth.expLen Φ.val.variables := by
  obtain ⟨N₁, hN₁⟩ := Paper2.AEth3.bits_fit E (Dsrc.sizeExponent + 2)
  refine ⟨max N₁
    (2 ^ (2 ^ (Dsrc.sizeExponent + 1) *
      Paper2.Unit4Shell.T10Size.t45C Dsrc Bsrc cs)), ?_⟩
  intro Φ hsparse hlarge
  have h1 : N₁ ≤ Φ.val.variables := (le_max_left _ _).trans hlarge
  have hbig : 2 ^ (2 ^ (Dsrc.sizeExponent + 1) *
      Paper2.Unit4Shell.T10Size.t45C Dsrc Bsrc cs) ≤ Φ.val.variables :=
    (le_max_right _ _).trans hlarge
  have hsize := Paper2.Unit4Shell.T10Size.t45_shell_form
    Dsrc Bsrc cs Φ hsparse hbig
  exact hN₁ Φ.val.variables h1 _ hsize

theorem source_square_printer_subexp27
    (Dsrc : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Dsrc))
    (cs : ℕ)
    (hA : H_A3_27 Bsrc.degreeBound (sourceGap Dsrc Bsrc)) :
    ∃ (M : BitMachine.Machine) (C N₀ : ℕ),
      ∀ (Φ : ValidFormula),
        Φ.val.clauses.length ≤ cs * Φ.val.variables →
        N₀ ≤ Φ.val.variables →
        let g := t10Graph Dsrc Bsrc Φ
        let hg := t10Graph_valid Dsrc Bsrc Φ
        let hn := t10_vertices_pos Dsrc Bsrc Φ
        let edge := CanonicalEdgeTape.graphEdge g hg
        let k := kOf Φ.val.variables
        ∀ t : (select27 hn edge Bsrc.degreeBound (sourceGap Dsrc Bsrc) k).Tape,
          M.OutputsWithin
            (BitMachineBankCodec.encode
              (QuarticDispatchSpec.inputBank27 Bsrc.degreeBound (sourceGap Dsrc Bsrc)
                g hg hn k t))
            (EncodedCommunication.encodeInstance
              (Paper2.ASquare.squareInstance
                (selectedInstance27 hn edge Bsrc.degreeBound (sourceGap Dsrc Bsrc) k t)))
            (C * Paper2.AEth.expLen Φ.val.variables) := by
  obtain ⟨M, C, E, hM⟩ :=
    H_square_poly_27_of_H_A3 Bsrc.degreeBound (sourceGap Dsrc Bsrc) hA
  obtain ⟨N₁, hN₁⟩ := source_square_poly_clock_fit27 Dsrc Bsrc cs E
  refine ⟨M, C, max N₁ 36, ?_⟩
  intro Φ hsparse hlarge g hg hn edge k t
  have h1 : N₁ ≤ Φ.val.variables := (le_max_left _ _).trans hlarge
  have h36 : 36 ≤ Φ.val.variables := (le_max_right _ _).trans hlarge
  obtain ⟨_, _, hinc, hdeg, _, _, _⟩ := t10_source Dsrc Bsrc Φ
  have hk : 1 ≤ k :=
    Paper2.Unit4Shell.AsymptoticsExplicit.kOf_pos _ h36
  have hrun := hM g hg hn k ⟨hk, hinc, hdeg⟩ t
  apply BitMachine.outputsWithin_mono _ hrun
  exact Nat.mul_le_mul_left C (hN₁ Φ hsparse h1)

#print axioms source_square_poly_clock_fit27
#print axioms source_square_printer_subexp27

end Paper2.CurrentAdditive.QuarticClassEndpoint
