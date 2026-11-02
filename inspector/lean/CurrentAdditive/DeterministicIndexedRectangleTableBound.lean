import CurrentAdditive.DeterministicIndexedRectangleSize
import CurrentAdditive.DeterministicETHFullSubexp

/-! The exact public T10 rectangle word has the same tableBound growth shape
used by the sparse deterministic ETH clock theorem. -/

namespace CurrentAdditive.DeterministicIndexedRectangleTableBound

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.IndexedExecutableStepRecovery
open CurrentAdditive.DeterministicIndexedRectangleSize
open CurrentAdditive.DeterministicETHFullSubexp
open Paper2.Unit4Shell.T10Finite
open Paper2

theorem t10_dynamic_rectangle_length_le_tableBound
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (Φ : ValidFormula) (L : ℕ)
    [NeZero (t10Graph D B Φ).vertices]
    [NeZero (s L)] [NeZero (s L-3)] [NeZero (q₁ L)]
    [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]
    (cs : ℕ) (hsparse : Φ.val.clauses.length ≤ cs * Φ.val.variables)
    (hgraphlarge : CurrentAdditive.DeterministicETHSourceBridge.graphPolynomialCutoff
      D B cs ≤ Φ.val.variables)
    (hparamlarge : sourceCutoffSize B.degreeBound (sourceGap D B) ≤
      Φ.val.variables)
    (hL : L = publicLog (max (t10Graph D B Φ).vertices Φ.val.variables)
      B.degreeBound (sourceGap D B))
    (T : Schedule (Fin (t10Graph D B Φ).vertices)
      (Fin (t10Graph D B Φ).edges.length) L)
    (inputs : ∀ R : Stage (N L),
      StepInputs (V := Fin (t10Graph D B Φ).vertices)
        (E := Fin (t10Graph D B Φ).edges.length) L R T)
    (numberings : ∀ R : Stage (N L), ExplicitNumberings R)
    (a C₁ C₀ : ℕ) (ha : 1 ≤ a) (hC₀ : 2*C₁+2 ≤ C₀)
    (hresource : ResourceContract
      (indexedActualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)) (N L) (2^a) C₁) :
    let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
      (t10Graph_valid D B Φ)
    let C := indexedActualConstruction (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs
    let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs numberings
    let k := CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables
    let R := state C G k
    let b := 2*budget (Paper2.LookupSeed.exponent L+1) (h L) k+k
    (encodeInstance
      (CurrentAdditive.DeterministicETHPhysicalSquare.rectangleInstance
        (P.table R) b)).length ≤
      10 * tableBound a C₀ (D.sizeExponent+4) Φ.val.variables := by
  have hs := CurrentAdditive.DeterministicETHSourceBridge.sparse_formula_public_schedule
    D B cs Φ hsparse hgraphlarge hparamlarge
  have hs' : N L ≤ Φ.val.variables^(D.sizeExponent+4) := by
    have hh : Φ.val.variables ≤ N L ∧
        Admissible L B.degreeBound (t10Graph D B Φ).vertices
          (t10Graph D B Φ).edges.length sourceC128Ceil (sourceGap D B) ∧
        N L ≤ Φ.val.variables^(D.sizeExponent+4) := by
      simpa only [hL] using hs
    exact hh.2.2
  let k := CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables
  have hpow :
      (N L)^(C₀*(2^a)^k) ≤
      tableBound a C₀ (D.sizeExponent+4) Φ.val.variables := by
    calc
      (N L)^(C₀*(2^a)^k)
          ≤ (Φ.val.variables^(D.sizeExponent+4))^(C₀*(2^a)^k) :=
            Nat.pow_le_pow_left hs' _
      _ = tableBound a C₀ (D.sizeExponent+4) Φ.val.variables := by
        unfold tableBound
        rw [← pow_mul]
        congr 1
        ring
  have hlen := t10_dynamic_rectangle_length_le_ten_power
    D B Φ L hL T inputs numberings a C₁ C₀ ha hC₀ hresource
  have hN_eq : N L = N (publicLog
      (max (t10Graph D B Φ).vertices Φ.val.variables)
      B.degreeBound (sourceGap D B)) := congrArg N hL
  dsimp only at hlen ⊢
  rw [← hN_eq] at hlen
  exact hlen.trans (Nat.mul_le_mul_left 10 hpow)

#print axioms t10_dynamic_rectangle_length_le_tableBound

end CurrentAdditive.DeterministicIndexedRectangleTableBound
