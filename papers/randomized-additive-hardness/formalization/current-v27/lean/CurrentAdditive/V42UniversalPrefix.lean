import CurrentAdditive.V42RuntimePrefix

/-! One fixed physical prefix retains the public caller's dyadic exponent.
It counts graph vertices/edges, computes all recipe parameters and source
data, and prints the actual seed/round envelope. It does not run the least
size selector and contains no desired state or execution premise. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option synthInstance.maxSize 32768

namespace CurrentAdditive.V42UniversalPrefix
noncomputable section
open Paper2 EthInapproximability.CurrentPaper BitMachineComposition
open V42Schedule

set_option maxHeartbeats 200000

def input := V40GraphConstructorFront.input
def N (p : ℕ) := 2^(4*p)
def base (g : EncodedGraph.Graph) (p : ℕ) := N p+(EncodedGraph.encode g).length+2

@[irreducible] def countedProducer := V40GraphConstructorFront.counts
def countedMachine := countedProducer.machine
def countedCoefficient := countedProducer.coefficient
def countedDegree := countedProducer.degree
@[irreducible] def parameterMachine := composition countedMachine V42RuntimePacket.machine
def parameterCoefficient := V40ConstructorComposition.coefficient
  countedCoefficient countedDegree V42RuntimePacket.coefficient V42RuntimePacket.degree
  countedMachine.pushBound 1
def parameterDegree := V40ConstructorComposition.degree countedDegree V42RuntimePacket.degree
@[irreducible] def sourceMachine := composition parameterMachine V42RuntimeSource.machine
def sourceCoefficient := V40ConstructorComposition.coefficient
  parameterCoefficient parameterDegree V42RuntimeSource.coefficient V42RuntimeSource.degree
  parameterMachine.pushBound 1
def sourceDegree := V40ConstructorComposition.degree parameterDegree V42RuntimeSource.degree
def machine := composition sourceMachine V42RuntimeSeed.roundMachine

private theorem numeral_exists (n : ℕ) : ∃ v : ℕ, v=n := ⟨n,rfl⟩
private def numeral (n : ℕ) : ℕ := Classical.choose (numeral_exists n)
private theorem numeral_value (n : ℕ) : numeral n=n := Classical.choose_spec (numeral_exists n)

def coefficient := numeral (V40ConstructorComposition.coefficient
  sourceCoefficient sourceDegree V42RuntimeSeed.roundCoefficient V42RuntimeSeed.roundDegree
  sourceMachine.pushBound 1)
def degree := numeral (V40ConstructorComposition.degree sourceDegree V42RuntimeSeed.roundDegree)
def baseCoefficient := coefficient*3^degree

theorem coefficient_value : coefficient=V40ConstructorComposition.coefficient
    sourceCoefficient sourceDegree V42RuntimeSeed.roundCoefficient V42RuntimeSeed.roundDegree
    sourceMachine.pushBound 1 := numeral_value _
theorem degree_value : degree=V40ConstructorComposition.degree sourceDegree V42RuntimeSeed.roundDegree := numeral_value _

private theorem arg_le (a b : ℕ) : a+1 ≤ b+a+1 := by omega
private theorem arg_mono (a b l : ℕ) (h : a ≤ b) : a+l+1 ≤ b+l+1 := by omega
private theorem scaled_clock (c d a b : ℕ) (h : a ≤ 3*b) :
    c*a^d ≤ (c*3^d)*b^d := by
  calc
    c*a^d ≤ c*(3*b)^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
    _ = _ := by rw [mul_pow,←mul_assoc]

#check parameterMachine

theorem parameter_outputs (g : EncodedGraph.Graph) (hg : g.Valid) (p K : ℕ) :
    parameterMachine.OutputsWithin (input (EncodedGraph.encode g) p K)
      (V42RuntimePacket.output (EncodedGraph.encode g) g.vertices g.edges.length p K)
      (parameterCoefficient*(N p+(input (EncodedGraph.encode g) p K).length+1)^parameterDegree) := by
  have hn : 2^p ≤ N p := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (by omega)
  have hr : countedProducer.result (input (EncodedGraph.encode g) p K)=
      V42RuntimePacket.input (EncodedGraph.encode g) g.vertices g.edges.length p K := by
    rw [countedProducer]
    exact V40GraphConstructorFront.counts_result g hg p K
  have hc:=countedProducer.outputs (input (EncodedGraph.encode g) p K)
  rw [hr] at hc
  have hp:=V42RuntimePacket.outputs (EncodedGraph.encode g) g.vertices g.edges.length p K
  rw [parameterMachine]
  apply V42RuntimePrefix.compose_paid countedMachine V42RuntimePacket.machine
    countedCoefficient countedDegree V42RuntimePacket.coefficient V42RuntimePacket.degree
    (N p) (input (EncodedGraph.encode g) p K)
    (V42RuntimePacket.input (EncodedGraph.encode g) g.vertices g.edges.length p K)
    (V42RuntimePacket.output (EncodedGraph.encode g) g.vertices g.edges.length p K)
  · exact BitMachine.outputsWithin_mono _ hc
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (arg_le _ _) _))
  · exact BitMachine.outputsWithin_mono _ hp
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (arg_mono _ _ _ hn) _))

#check parameter_outputs

theorem source_outputs (g : EncodedGraph.Graph) (hg : g.Valid) (p K : ℕ)
    (hp : 2 ≤ p) (hn : 0 < g.vertices)
    (hq : q₂ p (4*p)=LiteralEdgeEncoder.Width (s p) g.edges.length
      (V42RuntimePacket.repetition p g.edges.length)) :
    sourceMachine.OutputsWithin (input (EncodedGraph.encode g) p K)
      (V42RuntimeWords.source g hg p K hp hn hq)
      (sourceCoefficient*(N p+(input (EncodedGraph.encode g) p K).length+1)^sourceDegree) := by
  have ha:=parameter_outputs g hg p K
  have hs:=V42RuntimeWords.source_outputs g hg p K hp hn hq
  rw [sourceMachine]
  apply V42RuntimePrefix.compose_paid parameterMachine V42RuntimeSource.machine
    parameterCoefficient parameterDegree V42RuntimeSource.coefficient V42RuntimeSource.degree
    (N p) (input (EncodedGraph.encode g) p K)
    (V42RuntimePacket.output (EncodedGraph.encode g) g.vertices g.edges.length p K)
    (V42RuntimeWords.source g hg p K hp hn hq) ha
  exact BitMachine.outputsWithin_mono _ hs
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (arg_le _ _) _))

#check source_outputs

theorem outputs (g : EncodedGraph.Graph) (hg : g.Valid) (p K : ℕ)
    (hp : 2 ≤ p) (hn : 0 < g.vertices)
    (hq : q₂ p (4*p)=LiteralEdgeEncoder.Width (s p) g.edges.length
      (V42RuntimePacket.repetition p g.edges.length)) :
    machine.OutputsWithin (input (EncodedGraph.encode g) p K)
      (WeightedIterationDriver.input (V42RuntimeWords.word g hg p K hp hn hq 0) K)
      (coefficient*(N p+(input (EncodedGraph.encode g) p K).length+1)^degree) := by
  have hs:=source_outputs g hg p K hp hn hq
  have hz:=V42RuntimeSeed.round_outputs (EncodedGraph.encode g) g.vertices g.edges.length p K
    (StoredWeightedState.lawBytes (V42RuntimeWords.law g p hp hn))
    (StoredStepContext.activityWords (V42RuntimeWords.activity g hg p hp hq)) hp
  unfold machine
  rw [coefficient_value,degree_value]
  apply V42RuntimePrefix.compose_paid sourceMachine V42RuntimeSeed.roundMachine
    sourceCoefficient sourceDegree V42RuntimeSeed.roundCoefficient V42RuntimeSeed.roundDegree
    (N p) (input (EncodedGraph.encode g) p K)
    (V42RuntimeWords.source g hg p K hp hn hq) _ hs
  exact hz

#check outputs

theorem input_length (g : EncodedGraph.Graph) (p K : ℕ) :
    (input (EncodedGraph.encode g) p K).length=2*((EncodedGraph.encode g).length+p+K)+3 := by
  simp [input,V40GraphConstructorFront.input,BitMachineBankCodec.encode_length,Fin.sum_univ_succ]
  omega

theorem outputs_base (g : EncodedGraph.Graph) (hg : g.Valid) (p K : ℕ)
    (hp : 2 ≤ p) (hn : 0 < g.vertices)
    (hq : q₂ p (4*p)=LiteralEdgeEncoder.Width (s p) g.edges.length
      (V42RuntimePacket.repetition p g.edges.length)) :
    machine.OutputsWithin (input (EncodedGraph.encode g) p K)
      (WeightedIterationDriver.input (V42RuntimeWords.word g hg p K hp hn hq 0) K)
      (baseCoefficient*(base g p+K+1)^degree) := by
  have hpN : p ≤ N p := (V38Cutoff.coefficient_le_power p).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (by omega))
  have hb : N p+(input (EncodedGraph.encode g) p K).length+1 ≤ 3*(base g p+K+1) := by
    rw [input_length]
    unfold base
    omega
  exact BitMachine.outputsWithin_mono _ (outputs g hg p K hp hn hq)
    (scaled_clock coefficient degree _ _ hb)

#print axioms parameter_outputs
#print axioms outputs_base

end
end CurrentAdditive.V42UniversalPrefix
