import CurrentAdditive.V42RuntimeSelector
import CurrentAdditive.V42RuntimeWords
import CurrentAdditive.V42RuntimeSeed
import CurrentAdditive.V40GraphConstructorFront

/-! Closed physical public prefix. Only graph bytes and unary round count
are inputs. The fixed source cutoff is part of the program. Counts, the
least valid dyadic order, every width, law, activity cell, seed and fuel are
all computed by the finite machines. -/
namespace CurrentAdditive.V42RuntimePrefix
open Paper2 EthInapproximability.CurrentPaper V42Schedule
open BitMachineComposition
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 65536

def input (graph : List Bool) (K : ℕ) := V40GraphConstructorFront.input graph 0 K
def selected (k₀ : ℕ) (g : EncodedGraph.Graph) := V42PublicCutoff.generatedExponent g.vertices k₀
def N (k₀ : ℕ) (g : EncodedGraph.Graph) := 2^(4*selected k₀ g)

theorem compose_paid (P Q : BitMachine.Machine) (cp dp cq dq N : ℕ)
    (x y z : List Bool)
    (hp : P.OutputsWithin x y (cp*(N+x.length+1)^dp))
    (hq : Q.OutputsWithin y z (cq*(N+y.length+1)^dq)) :
    (composition P Q).OutputsWithin x z
      (V40ConstructorComposition.coefficient cp dp cq dq P.pushBound 1*
        (N+x.length+1)^V40ConstructorComposition.degree dp dq) := by
  apply BitMachine.outputsWithin_mono _ (composition_outputsWithin P Q hp hq)
  exact V40ConstructorComposition.time_bound (N+x.length) cp dp cq dq P.pushBound 1 N y.length
    (by omega) ((BitMachine.output_length_bound P hp).trans (by omega))

def countedMachine := V40GraphConstructorFront.counts.machine
def countedCoefficient := V40GraphConstructorFront.counts.coefficient
def countedDegree := V40GraphConstructorFront.counts.degree
def selectedMachine (k₀ : ℕ) := composition countedMachine (V42RuntimeSelector.machine k₀)
def selectedCoefficient (k₀ : ℕ) := V40ConstructorComposition.coefficient countedCoefficient countedDegree
  (V42RuntimeSelector.coefficient k₀) (V42RuntimeSelector.degree k₀) countedMachine.pushBound 1
def selectedDegree (k₀ : ℕ) := V40ConstructorComposition.degree countedDegree (V42RuntimeSelector.degree k₀)
def parameterMachine (k₀ : ℕ) := composition (selectedMachine k₀) V42RuntimePacket.machine
def parameterCoefficient (k₀ : ℕ) := V40ConstructorComposition.coefficient
  (selectedCoefficient k₀) (selectedDegree k₀) V42RuntimePacket.coefficient V42RuntimePacket.degree
  (selectedMachine k₀).pushBound 1
def parameterDegree (k₀ : ℕ) := V40ConstructorComposition.degree (selectedDegree k₀) V42RuntimePacket.degree
def sourceMachine (k₀ : ℕ) := composition (parameterMachine k₀) V42RuntimeSource.machine
def sourceCoefficient (k₀ : ℕ) := V40ConstructorComposition.coefficient
  (parameterCoefficient k₀) (parameterDegree k₀) V42RuntimeSource.coefficient V42RuntimeSource.degree
  (parameterMachine k₀).pushBound 1
def sourceDegree (k₀ : ℕ) := V40ConstructorComposition.degree (parameterDegree k₀) V42RuntimeSource.degree
def machine (k₀ : ℕ) := composition (sourceMachine k₀) V42RuntimeSeed.roundMachine
def coefficient (k₀ : ℕ) := V40ConstructorComposition.coefficient
  (sourceCoefficient k₀) (sourceDegree k₀) V42RuntimeSeed.roundCoefficient V42RuntimeSeed.roundDegree
  (sourceMachine k₀).pushBound 1
def degree (k₀ : ℕ) := V40ConstructorComposition.degree (sourceDegree k₀) V42RuntimeSeed.roundDegree

theorem selected_outputs (k₀ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (K : ℕ) :
    (selectedMachine k₀).OutputsWithin (input (EncodedGraph.encode g) K)
      (V42RuntimePacket.input (EncodedGraph.encode g) g.vertices g.edges.length (selected k₀ g) K)
      (selectedCoefficient k₀*(N k₀ g+(input (EncodedGraph.encode g) K).length+1)^selectedDegree k₀) := by
  have hc := V40GraphConstructorFront.counts.outputs (input (EncodedGraph.encode g) K)
  rw [show input (EncodedGraph.encode g) K=V40GraphConstructorFront.input (EncodedGraph.encode g) 0 K from rfl,
    V40GraphConstructorFront.counts_result g hg 0 K] at hc
  have hs := V42RuntimeSelector.outputs k₀ (EncodedGraph.encode g) g.vertices g.edges.length 0 K
  change countedMachine.OutputsWithin (input (EncodedGraph.encode g) K)
    (V40GraphConstructorFront.countWord g 0 K)
    (countedCoefficient*((input (EncodedGraph.encode g) K).length+1)^countedDegree) at hc
  change (V42RuntimeSelector.machine k₀).OutputsWithin (V40GraphConstructorFront.countWord g 0 K)
    (V42RuntimePacket.input (EncodedGraph.encode g) g.vertices g.edges.length (selected k₀ g) K)
    (V42RuntimeSelector.coefficient k₀*((V40GraphConstructorFront.countWord g 0 K).length+1)^V42RuntimeSelector.degree k₀) at hs
  apply compose_paid countedMachine (V42RuntimeSelector.machine k₀) countedCoefficient countedDegree
    (V42RuntimeSelector.coefficient k₀) (V42RuntimeSelector.degree k₀) (N k₀ g)
    (input (EncodedGraph.encode g) K) (V40GraphConstructorFront.countWord g 0 K)
    (V42RuntimePacket.input (EncodedGraph.encode g) g.vertices g.edges.length (selected k₀ g) K)
  · exact BitMachine.outputsWithin_mono _ hc
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  · exact BitMachine.outputsWithin_mono _ hs
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

theorem parameter_outputs (k₀ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (K : ℕ) :
    (parameterMachine k₀).OutputsWithin (input (EncodedGraph.encode g) K)
      (V42RuntimePacket.output (EncodedGraph.encode g) g.vertices g.edges.length (selected k₀ g) K)
      (parameterCoefficient k₀*(N k₀ g+(input (EncodedGraph.encode g) K).length+1)^parameterDegree k₀) := by
  have hp := V42RuntimePacket.outputs (EncodedGraph.encode g) g.vertices g.edges.length (selected k₀ g) K
  have hn : 2^(selected k₀ g)≤N k₀ g := Nat.pow_le_pow_right (by decide) (by omega)
  apply compose_paid _ _ (selectedCoefficient k₀) (selectedDegree k₀)
    V42RuntimePacket.coefficient V42RuntimePacket.degree (N k₀ g) _ _ _
    (selected_outputs k₀ g hg K)
  exact BitMachine.outputsWithin_mono _ hp
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

theorem source_outputs (k₀ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (K : ℕ)
    (hk : 2 ≤ selected k₀ g) (hn : 0<g.vertices)
    (hq : q₂ (selected k₀ g) (4*selected k₀ g)=LiteralEdgeEncoder.Width (s (selected k₀ g)) g.edges.length
      (V42RuntimePacket.repetition (selected k₀ g) g.edges.length)) :
    (sourceMachine k₀).OutputsWithin (input (EncodedGraph.encode g) K)
      (V42RuntimeWords.source g hg (selected k₀ g) K hk hn hq)
      (sourceCoefficient k₀*(N k₀ g+(input (EncodedGraph.encode g) K).length+1)^sourceDegree k₀) := by
  apply compose_paid _ _ (parameterCoefficient k₀) (parameterDegree k₀)
    V42RuntimeSource.coefficient V42RuntimeSource.degree (N k₀ g) _ _ _
    (parameter_outputs k₀ g hg K)
  exact BitMachine.outputsWithin_mono _ (V42RuntimeWords.source_outputs g hg (selected k₀ g) K hk hn hq)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

theorem outputs (k₀ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (K : ℕ)
    (hk : 2 ≤ selected k₀ g) (hn : 0<g.vertices)
    (hq : q₂ (selected k₀ g) (4*selected k₀ g)=LiteralEdgeEncoder.Width (s (selected k₀ g)) g.edges.length
      (V42RuntimePacket.repetition (selected k₀ g) g.edges.length)) :
    (machine k₀).OutputsWithin (input (EncodedGraph.encode g) K)
      (WeightedIterationDriver.input (V42RuntimeWords.word g hg (selected k₀ g) K hk hn hq 0) K)
      (coefficient k₀*(N k₀ g+(input (EncodedGraph.encode g) K).length+1)^degree k₀) := by
  apply compose_paid _ _ (sourceCoefficient k₀) (sourceDegree k₀)
    V42RuntimeSeed.roundCoefficient V42RuntimeSeed.roundDegree (N k₀ g) _ _ _
    (source_outputs k₀ g hg K hk hn hq)
  exact V42RuntimeSeed.round_outputs (EncodedGraph.encode g) g.vertices g.edges.length (selected k₀ g) K
    (StoredWeightedState.lawBytes (V42RuntimeWords.law g (selected k₀ g) hk hn))
    (StoredStepContext.activityWords (V42RuntimeWords.activity g hg (selected k₀ g) hk hq)) hk

def base (k₀ : ℕ) (g : EncodedGraph.Graph) := N k₀ g+(EncodedGraph.encode g).length+2
def baseCoefficient (k₀ : ℕ) := coefficient k₀*2^degree k₀

theorem input_length (graph : List Bool) (K : ℕ) : (input graph K).length+1=2*(graph.length+K+2) := by
  simp [input,V40GraphConstructorFront.input,BitMachineBankCodec.encode_length,Fin.sum_univ_succ];ring

theorem outputs_base (k₀ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (K : ℕ)
    (hk : 2 ≤ selected k₀ g) (hn : 0<g.vertices)
    (hq : q₂ (selected k₀ g) (4*selected k₀ g)=LiteralEdgeEncoder.Width (s (selected k₀ g)) g.edges.length
      (V42RuntimePacket.repetition (selected k₀ g) g.edges.length)) :
    (machine k₀).OutputsWithin (input (EncodedGraph.encode g) K)
      (WeightedIterationDriver.input (V42RuntimeWords.word g hg (selected k₀ g) K hk hn hq 0) K)
      (baseCoefficient k₀*(base k₀ g+K+1)^degree k₀) := by
  apply BitMachine.outputsWithin_mono _ (outputs k₀ g hg K hk hn hq)
  rw [show N k₀ g+(input (EncodedGraph.encode g) K).length+1=
    N k₀ g+((input (EncodedGraph.encode g) K).length+1) by omega,input_length]
  calc
    _ ≤ coefficient k₀*(2*(base k₀ g+K+1))^degree k₀ :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by unfold base;omega) _)
    _ = _ := by rw [mul_pow];unfold baseCoefficient;ring

#print axioms outputs
#print axioms outputs_base
end
end CurrentAdditive.V42RuntimePrefix
