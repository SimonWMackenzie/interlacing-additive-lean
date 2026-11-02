import CurrentAdditive.V42RandomizedSourceLaw
import CurrentAdditive.V42RandomizedSourceTests
import CurrentAdditive.V39SourceCut

/-! Finite input exceptions are handled by the actual sparse router. This
module proves correctness on all sparse source encodings, including small
sizes, under the exact actual-source joint law. It supplies no machine run. -/
namespace CurrentAdditive.V42RandomizedETHEndpoint
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V42PublicSchedule V39PermittedNumericalExtraction
set_option maxHeartbeats 300000
set_option maxRecDepth 16384

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The router checks density cs+2, preserving every cs-sparse original
while retaining a valid fixed NO destination even when cs=0. -/
def routedSource (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) : ValidFormula :=
  AEth4.routedV (cs+2) cutoff hcutoff w

theorem routedSource_sparse (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) :
    (routedSource cs cutoff hcutoff w).val.clauses.length ≤
      (cs+2)*(routedSource cs cutoff hcutoff w).val.variables :=
  AEth4.routed4_sparse (cs+2) cutoff (by nlinarith) w

theorem routedSource_tests (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool)
    (hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff) :
    let Φ := routedSource cs cutoff hcutoff w
    SourceTests D B Φ := by
  apply (V42SourceGeometry.source_all_large D B (cs+2) _
    (routedSource_sparse cs cutoff hcutoff w) ?_).2.1
  exact hsource.trans (AEth4.routed4_variables (cs+2) cutoff w)

/-- Every source size is covered by the physical router's finite fallback.
Correctness remains explicitly on valid cs-sparse originals. -/
theorem permitted_routed_correctness (A : PermittedEstimator) (cs T₀ : ℕ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < 1/8) (hA : GrowingSquareAccuracy A c T₀) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ V42SourceGeometry.originalCutoff D B (cs+2) ≤ N₀ ∧
      ∀ cutoff, N₀ ≤ cutoff → ∀ hcutoff : 1 ≤ cutoff, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables →
      let ρ := routedSource cs cutoff hcutoff (EncodedCNF.encode Φ.val)
      ∀ ht : SourceTests D B ρ,
      (EncodedCNF.encode Φ.val ∈ EncodedCNF.Language →
        (99:ℝ)/100 ≤ (sourceLaw D B (extractedEstimator A) ρ).prob
          (fun z => sourceAccepts D B ρ ht (extractedEstimator A) z.1 z.2)) ∧
      (EncodedCNF.encode Φ.val ∉ EncodedCNF.Language →
        (sourceLaw D B (extractedEstimator A) ρ).prob
          (fun z => sourceAccepts D B ρ ht (extractedEstimator A) z.1 z.2) ≤ (3:ℝ)/100) := by
  obtain ⟨Ns,hNs,hS⟩ := permitted_source_law_all_large D B A (cs+2) T₀ c hc0 hc hA
  refine ⟨max Ns (V42SourceGeometry.originalCutoff D B (cs+2)),
    hNs.trans (le_max_left _ _),le_max_right _ _,?_⟩
  intro cutoff hcut hcutoff Φ hsp
  dsimp only
  let ρ := routedSource cs cutoff hcutoff (EncodedCNF.encode Φ.val)
  intro ht
  have hvars : Ns ≤ ρ.val.variables :=
    ((le_max_left _ _).trans hcut).trans (AEth4.routed4_variables (cs+2) cutoff _)
  have h := hS ρ (routedSource_sparse cs cutoff hcutoff _) hvars ht
  have hsp' : Φ.val.clauses.length ≤ (cs+2)*Φ.val.variables :=
    hsp.trans (Nat.mul_le_mul_right _ (by omega))
  have hlang : EncodedCNF.Satisfiable ρ.val ↔ EncodedCNF.encode Φ.val ∈ EncodedCNF.Language :=
    AEth4.routed4_sat_iff (cs+2) hcutoff Φ.val Φ.property hsp'
  exact ⟨fun hy => h.1 (hlang.2 hy),fun hn => h.2 (fun hy => hn (hlang.1 hy))⟩

#print axioms routedSource_tests
#print axioms permitted_routed_correctness
end
end CurrentAdditive.V42RandomizedETHEndpoint

