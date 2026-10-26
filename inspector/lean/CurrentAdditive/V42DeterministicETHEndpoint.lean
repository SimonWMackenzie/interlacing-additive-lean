import CurrentAdditive.V42ETHSourceLaw
import CurrentAdditive.V42ETHPhysical
import CurrentAdditive.DeterministicSparseETHEventual
import CurrentAdditive.V40DeterministicRoutedLaw

/-! Actual deterministic v42 growing-error endpoint. The CNF source,
least-dyadic public parameters, seven-call table, new threshold printer,
permitted estimator and comparison are composed as finite physical machines.
Only the named Dinur/BOT source records and sparse ETH remain external. -/
namespace CurrentAdditive.V42DeterministicETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V42ActualSource V42ETHSourceLaw V39RuntimeETHNumerics
open V39PermittedDeterministicExtraction V39FramedNumerical
open V40DeterministicSourcePack V40DeterministicETHEndpoint
open DeterministicETHFullSubexp
open scoped Classical
set_option maxHeartbeats 100000
set_option maxRecDepth 65536

variable (D:DinurReduction) (B:BOTReduction (booleanOccurrence D))

def semanticCutoff (A:PermittedDeterministicEstimator) (cs T₀:ℕ)
    (hA:GrowingSquareAccuracy A (V42ETHSourceLaw.constructionError D B) T₀) : ℕ :=
  max 1 (Classical.choose (V42ETHSourceLaw.classification_all_large D B A (cs+2) T₀ hA))

theorem semanticCutoff_pos (A:PermittedDeterministicEstimator) (cs T₀:ℕ)
    (hA:GrowingSquareAccuracy A (V42ETHSourceLaw.constructionError D B) T₀) :
    1 ≤ semanticCutoff D B A cs T₀ hA := le_max_left _ _

def algorithm (A:PermittedDeterministicEstimator) (cs T₀:ℕ)
    (hA:GrowingSquareAccuracy A (V42ETHSourceLaw.constructionError D B) T₀) :
    DeterministicSparseETH.Algorithm where
  machine:=V42ETHPhysical.machine D B (V42PermittedExtraction.estimator A) cs
    (semanticCutoff D B A cs T₀ hA) (semanticCutoff_pos D B A cs T₀ hA)
  answer w:=decide (EncodedCNF.Satisfiable
    (sparseFormula cs (semanticCutoff D B A cs T₀ hA) (semanticCutoff_pos D B A cs T₀ hA) w).val)
  time:=V42ETHPhysical.time D B (V42PermittedExtraction.estimator A) cs
    (semanticCutoff D B A cs T₀ hA) (semanticCutoff_pos D B A cs T₀ hA)
  run w:=by
    let cut:=semanticCutoff D B A cs T₀ hA
    let hc:=semanticCutoff_pos D B A cs T₀ hA
    let Φ:=sparseFormula cs cut hc w
    have hclass:=Classical.choose_spec
      (V42ETHSourceLaw.classification_all_large D B A (cs+2) T₀ hA) Φ
      (V40DeterministicETHEndpoint.routed_sparse cs cut hc w)
      ((le_max_right _ _).trans (AEth4.routed4_variables (cs+2) cut w))
    have hr:=V42ETHPhysical.outputs D B (V42PermittedExtraction.estimator A) cs cut hc w
    dsimp only [Φ,V42ETHSourceLaw.amplification] at hclass
    dsimp only [V42ETHPhysical.amplification] at hr
    rw [hclass] at hr
    exact hr

theorem algorithm_runs (A:PermittedDeterministicEstimator) (cs T₀:ℕ)
    (hA:GrowingSquareAccuracy A (V42ETHSourceLaw.constructionError D B) T₀) (w:List Bool) :
    (algorithm D B A cs T₀ hA).machine.OutputsWithin w
      [(algorithm D B A cs T₀ hA).answer w] ((algorithm D B A cs T₀ hA).time w) :=
  (algorithm D B A cs T₀ hA).run w

theorem physical_clock_all_large (E:Estimator) (cs cutoff:ℕ) (hcut:1 ≤ cutoff) :
    ∃ M₀ K d:ℕ,∀ Φ:ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables→M₀ ≤ Φ.val.variables→
      V42ETHPhysical.time D B E cs cutoff hcut (EncodedCNF.encode Φ.val) ≤
        K*tableBound (amplificationLog (V42ETHPhysical.amplification D B))
          (V42ETHPhysical.mainExponent D B E) (D.sizeExponent+4) Φ.val.variables*
          ((EncodedCNF.encode Φ.val).length+1)^d := by
  let F:=V42ETHPhysical.front D B cs cutoff hcut
  let C:=V42ETHPhysical.mainExponent D B E
  let A:=V42ETHPhysical.amplification D B
  let e:=D.sizeExponent+3
  refine ⟨max cutoff (max (DeterministicETHSourceBridge.graphPolynomialCutoff D B cs)
    (max (2^(4*k0 D B)) 16)),frontClockCoefficient F+1,frontClockDegree F,?_⟩
  intro Φ hsp hlarge
  let M:=Φ.val.variables
  have hcutΦ:cutoff ≤ M := (le_max_left _ _).trans hlarge
  have hrest:max (DeterministicETHSourceBridge.graphPolynomialCutoff D B cs)
      (max (2^(4*k0 D B)) 16) ≤ M := (le_max_right _ _).trans hlarge
  have hgcut:DeterministicETHSourceBridge.graphPolynomialCutoff D B cs ≤ M := (le_max_left _ _).trans hrest
  have hN₀:2^(4*k0 D B) ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hrest)
  have hM:16 ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans hrest)
  have hg:(t10Graph D B Φ).vertices ≤ M^e :=
    DeterministicETHSourceBridge.sparse_graph_vertices_polynomial D B cs Φ hsp hgcut
  have hN:V42ETHPhysical.N D B Φ ≤ M^(e+1) :=
    V42ETHNumerics.selected_polynomial (k0 D B) M e (t10Graph D B Φ) hM (by unfold e;omega) hg hN₀
  let Q:=tableBound (amplificationLog A) C (D.sizeExponent+4) M
  have hQ:1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hmain:V42ETHPhysical.mainTime D B E Φ (rounds A M) ≤ Q := by
    unfold V42ETHPhysical.mainTime
    calc
      _  ≤ (M^(e+1))^(C*A^(rounds A M)) := Nat.pow_le_pow_left hN _
      _ =M^((e+1)*C*A^(rounds A M)) := by rw [←pow_mul];congr 1;ring
      _  ≤ M^((e+1)*C*(2^amplificationLog A)^(rounds A M)) :=
        Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (amplification_le A) _))
      _ =Q := rfl
  have hcombine:=frontClock_combine F (EncodedCNF.encode Φ.val) Q 1 1
    (V42ETHPhysical.mainTime D B E Φ (rounds A M)) hQ (by simpa using hmain)
  unfold V42ETHPhysical.time
  rw [V40DeterministicETHEndpoint.routed_original cs cutoff hcut Φ hsp hcutΦ]
  simpa only [pow_one,one_mul] using hcombine

theorem algorithm_sparse (A:PermittedDeterministicEstimator) (cs T₀:ℕ)
    (hA:GrowingSquareAccuracy A (V42ETHSourceLaw.constructionError D B) T₀) :
    DeterministicSparseETH.SparseDecider cs (algorithm D B A cs T₀ hA) := by
  let cut:=semanticCutoff D B A cs T₀ hA
  let hc:=semanticCutoff_pos D B A cs T₀ hA
  let E:=V42PermittedExtraction.estimator A
  obtain ⟨M₀,K,d,hclock⟩:=physical_clock_all_large D B E cs cut hc
  apply DeterministicSparseETHEventual.sparse_decider_of_eventual_tableBound_clock cs
    (amplificationLog (V42ETHPhysical.amplification D B)) (V42ETHPhysical.mainExponent D B E)
    (D.sizeExponent+4) 1 K d M₀ (algorithm D B A cs T₀ hA)
    (by simpa only [V42ETHPhysical.amplification] using
      (show 1 ≤ amplificationLog (V42GraphRuntime.amplification (k0 D B)) from
        (by decide : 1 ≤ 64).trans (amplificationLog_ge _ (V42GraphRuntime.amplification_ge (k0 D B)))))
    ((by decide : 1 ≤ 1040).trans (V42ETHPhysical.mainExponent_ge D B E)) (by omega) (by decide)
  · intro Φ hsp
    change decide (EncodedCNF.Satisfiable (sparseFormula cs cut hc (EncodedCNF.encode Φ.val)).val)=true ↔ _
    simp only [decide_eq_true_eq]
    exact V40DeterministicETHEndpoint.routed_sat_iff cs cut hc Φ hsp
  · intro Φ hsp hM
    simpa only [pow_one] using hclock Φ hsp hM

theorem deterministic_growing_square_class (hETH:DeterministicSparseETH.Holds) :
    ¬∃ A:PermittedDeterministicEstimator,∃ T₀:ℕ,
      GrowingSquareAccuracy A (V42ETHSourceLaw.constructionError D B) T₀ := by
  rintro ⟨A,T₀,hA⟩
  apply DeterministicSparseETH.contradiction_of_decider hETH
  intro cs
  exact ⟨algorithm D B A cs T₀ hA,algorithm_sparse D B A cs T₀ hA⟩

theorem deterministic_growing_class (hETH:DeterministicSparseETH.Holds) :
    ¬∃ A:PermittedDeterministicEstimator,∃ T₀:ℕ,
      GrowingAccuracy A (V42ETHSourceLaw.constructionError D B) T₀ := by
  rintro ⟨A,T₀,hA⟩
  exact deterministic_growing_square_class D B hETH
    ⟨A,T₀,growingSquareAccuracy_of_growingAccuracy A _ T₀ hA⟩

include D B in
theorem deterministic_growing_hardness (hETH:DeterministicSparseETH.Holds) :
    ∃ c:ℝ,0<c ∧ ¬∃ A:PermittedDeterministicEstimator,∃ T₀:ℕ,GrowingAccuracy A c T₀ :=
  ⟨V42ETHSourceLaw.constructionError D B,V42ETHSourceLaw.constructionError_positive D B,
    deterministic_growing_class D B hETH⟩

#print axioms algorithm_runs
#print axioms algorithm_sparse
#print axioms deterministic_growing_square_class
#print axioms deterministic_growing_hardness
end
end CurrentAdditive.V42DeterministicETHEndpoint




