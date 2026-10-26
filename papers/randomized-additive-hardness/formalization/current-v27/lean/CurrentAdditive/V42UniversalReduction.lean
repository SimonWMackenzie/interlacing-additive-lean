import CurrentAdditive.V42UniversalRuntime
import CurrentAdditive.V42GeneratedIteration
import CurrentAdditive.V42FixedPromiseCutoff

/-! Source v42 det:reduction at every supplied admissible N=s^4. The seed,
public threshold and actual iterates all use that N. No least-selected
output is reused with a different claimed threshold or side lower bound. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option synthInstance.maxSize 32768

namespace CurrentAdditive.V42UniversalReduction
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open V42Schedule V39GeneratedConstruction Workspace.Types.CommComplexity

def budget (p K : ℕ) := LookupSeed.exponent (4*p)+1+K*(40*p)

theorem budget_exact (p K : ℕ) :
    V42DeterministicRequest.thresholdNumber (4*p) K=budget p K :=
  V42DeterministicRequest.generated_threshold p K

theorem actual_reduction (γ : ℚ) (Δ : ℕ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hnm : g.vertices ≤ 2*g.edges.length) (hdeg : 2*g.edges.length ≤ Δ*g.vertices)
    (p K : ℕ) (hp : fixedPromiseCutoff γ Δ ≤ p) (hnN : g.vertices ≤ 2^(4*p)) :
    ∃ I : Instance,
      V42UniversalRuntime.machine.OutputsWithin
        (V42UniversalPrefix.input (EncodedGraph.encode g) p K) (encodeInstance I)
        ((2^(4*p))^(V42UniversalRuntime.C Δ*V42UniversalRuntime.amplification^K)) ∧
      (encodeInstance I).length ≤ (2^(4*p))^(V42UniversalRuntime.C Δ*V42UniversalRuntime.amplification^K) ∧
      I.Valid ∧ I.threshold=budget p K ∧ I.cols=I.rows ∧
      2^(4*p) ≤ I.rows ∧ (∃ e, I.rows=2^e) ∧
      (∀ colour : Fin g.vertices → Fin 3,
        (∀ e, colour (LiteralEdgeEncoder.edge g hg e false) ≠
          colour (LiteralEdgeEncoder.edge g hg e true)) →
        D (ProtocolVerifier.tableGame I.rows I.cols I.table) ≤ budget p K) ∧
      ((∀ v, SourceItems.degree (LiteralEdgeEncoder.edge g hg) v ≤ Δ) →
        (∀ colour : Fin g.vertices → Fin 3, (γ:ℝ)*g.edges.length ≤
          ((Finset.univ.filter (fun e => colour (LiteralEdgeEncoder.edge g hg e false)=
            colour (LiteralEdgeEncoder.edge g hg e true))).card:ℝ)) →
        D (ProtocolVerifier.tableGame I.rows I.cols I.table)=budget p K+K) := by
  have hp200 : 200 ≤ p := (fixedPromiseCutoff_ge γ Δ).1.trans hp
  have hp2 : 2 ≤ p := by omega
  have hpΔ : 2*Δ ≤ p := (fixedPromiseCutoff_ge γ Δ).2.trans hp
  let hq:=V42UniversalRuntime.width Δ g p hnN hdeg hpΔ
  let R:=V42RuntimeWords.run g hg p hp2 hn hq K
  let I:=V42UniversalFormatter.outputInstance (4*p) K R
  have hrun:=V42UniversalRuntime.outputs Δ g hg p K hp2 hn hnN hdeg hpΔ
  have hshape:=V42UniversalFormatter.shape (4*p) K R
  refine ⟨I,hrun.1,hrun.2,V42UniversalFormatter.instance_valid _ _ _,?_,hshape.2.1,?_,hshape.2.2.2,?_,?_⟩
  · exact hshape.2.2.1.trans (budget_exact p K)
  · exact V42ActualLower.public_side p hp2 hn hq (LiteralEdgeEncoder.edge g hg) K
  · intro colour proper
    rw [V42UniversalFormatter.cost]
    have h:=V42GeneratedConstruction.graphRun_yes p (4*p) hp2 hn hq
      (LiteralEdgeEncoder.edge g hg) (4*p) K colour proper
    change D R.entry ≤ _ at h
    have he : V42GeneratedConstruction.overhead p (4*p)=40*p := by
      unfold V42GeneratedConstruction.overhead
      omega
    simpa only [he,budget] using h
  · intro hdegree gap
    rw [V42UniversalFormatter.cost]
    have hm : 0 < g.edges.length := by omega
    have hk:=fixedPromiseCutoff_graph γ Δ g.vertices g.edges.length p hγ hΔ hn hnm hp
    have h:=V42GeneratedNo.graphRun_no γ Δ hγ hΔ hn hm hk hp2 hq
      (LiteralEdgeEncoder.edge g hg) (LiteralEdgeEncoder.edge_loopless g hg) hdegree gap K
    have hc:=h.1
    change D R.entry=LookupSeed.exponent (4*p)+1+K*(40*p+1) at hc
    exact hc.trans (by unfold budget; ring)

/-- A single machine and one amplification constant precede every public
size, graph and round. Only the clock coefficient uses the fixed degree. -/
theorem fixed_machine_and_constants (Δ : ℕ) :
    ∃ M : BitMachine.Machine, ∃ A C0 : ℕ,
      2 ≤ A ∧ 0 < C0 ∧ (∃ a, A=2^a) ∧
      M=V42UniversalRuntime.machine ∧ A=V42UniversalRuntime.amplification ∧ C0=V42UniversalRuntime.C Δ := by
  refine ⟨V42UniversalRuntime.machine,V42UniversalRuntime.amplification,V42UniversalRuntime.C Δ,?_,?_,
    V42UniversalRuntime.amplification_power,rfl,rfl,rfl⟩
  · exact (by decide : 2 ≤ (2:ℕ)^64).trans V42UniversalRuntime.amplification_ge
  · unfold V42UniversalRuntime.C
    omega

#print axioms actual_reduction
#print axioms fixed_machine_and_constants

end
end CurrentAdditive.V42UniversalReduction
