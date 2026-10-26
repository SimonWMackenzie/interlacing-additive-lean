import CurrentAdditive.V40ActivityRow
import CurrentAdditive.V40SourceCellBounds

namespace CurrentAdditive.V40ActivityRow
noncomputable section
open Paper2 EthInapproximability.CurrentPaper BitMachineBankCodec
open V40SourceLocal D22PacketPrimitives V40SourceClockBounds GaussCellPolynomialClock
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768

theorem body_polynomial : HasPolynomialEnvelope body := by
  have hc : HasPolynomialEnvelope cellInput := by
    apply serialise_polynomial
    intro k
    fin_cases k <;> exact project_polynomial _
  have hcell : HasPolynomialEnvelope cell:=compose_polynomial hc V40SourceCell.producer_polynomial
  have hi : HasPolynomialEnvelope newItem:=compose_polynomial hcell (physical_polynomial PhysicalProducer.item)
  apply serialise_polynomial
  intro k
  fin_cases k
  all_goals first | exact project_polynomial _ | skip
  · exact append_polynomial (constant_polynomial [true]) (project_polynomial _)
  · exact append_polynomial (project_polynomial _) hi
theorem withFuel_polynomial : HasPolynomialEnvelope withFuel := by
  apply serialise_polynomial
  intro k
  fin_cases k
  · apply serialise_polynomial
    intro k
    fin_cases k
    all_goals first | exact project_polynomial _ | skip
    · exact constant_polynomial []
    · exact compose_polynomial (project_polynomial _) unary_field_polynomial
  · exact project_polynomial _

def bodyCoefficient:=Classical.choose body_polynomial
def bodyDegree:=Classical.choose (Classical.choose_spec body_polynomial)
theorem body_envelope : Envelope body bodyCoefficient bodyDegree :=
  Classical.choose_spec (Classical.choose_spec body_polynomial)
def fuelCoefficient:=Classical.choose withFuel_polynomial
def fuelDegree:=Classical.choose (Classical.choose_spec withFuel_polynomial)
theorem fuel_envelope : Envelope withFuel fuelCoefficient fuelDegree :=
  Classical.choose_spec (Classical.choose_spec withFuel_polynomial)
attribute [local irreducible] body withFuel bodyCoefficient bodyDegree fuelCoefficient fuelDegree

def measure (g : EncodedGraph.Graph) (s r q2 : Nat):=
  (EncodedGraph.encode g).length+g.edges.length+s+r+g.vertices+q2+count s g.vertices+1
def stateCap (n : Nat):=24*(n+1)^2

theorem value_le {s r : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s)
    (i : Fin (count s g.vertices)) (a : Fin (LiteralEdgeEncoder.Width s g.edges.length r)) :
    V40SourceCell.value g hg hs i a ≤ s := by
  unfold V40SourceCell.value
  split
  · rename_i p _
    exact p.isLt.le
  · exact le_rfl
theorem word_length {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (i : Fin (count s g.vertices)) (a : Fin q2) :
    (V40SourceCell.producer.result (V40SourceCell.raw g s r i.val a.val)).length ≤ s := by
  change (V40SourceCell.producer.result (V40SourceCell.raw g s r i.val (Fin.cast hq a).val)).length ≤ s
  rw [V40SourceCell.result g hg hn hs i (Fin.cast hq a)]
  exact (UnaryBinaryEncoding.bits_length_le _).trans (value_le g hg hs i (Fin.cast hq a))

theorem accumulator_length {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (i : Fin (count s g.vertices)) (j : Nat) (hj : j ≤ q2) :
    (accumulator g s r q2 i.val j).length ≤ 2*q2+1+3*(j*s)+j := by
  have ht:=SourceListEncoding.totalLength_map_le (List.range j)
    (fun a=>V40SourceCell.producer.result (V40SourceCell.raw g s r i.val a)) s (by
      intro a ha
      have ha':a<q2:=(List.mem_range.mp ha).trans_le hj
      exact word_length g hg hn hs hq i ⟨a,ha'⟩)
  have hf:=SourceListEncoding.fields_length (entries g s r i.val j)
  have hh:=EncodedGraph.natField_length_upper q2
  simp only [List.length_range] at ht
  simp only [entries,List.length_map,List.length_range] at hf
  simp only [accumulator,List.length_append,entries]
  omega

theorem state_length {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (i : Fin (count s g.vertices)) (j : Nat) (hj : j ≤ q2) :
    (state g s r q2 i.val j).length ≤ stateCap (measure g s r q2) := by
  let U:=measure g s r q2
  have ha:=accumulator_length g hg hn hs hq i j hj
  have hU:1 ≤ U:=by dsimp [U,measure]; omega
  have hq:q2 ≤ U:=by dsimp [U,measure]; omega
  have hs':s ≤ U:=by dsimp [U,measure]; omega
  have hj':j ≤ U:=hj.trans hq
  have hi:i.val ≤ U:=i.isLt.le.trans (by dsimp [U,measure]; omega)
  have hmul:j*s ≤ U^2:=by simpa [pow_two] using Nat.mul_le_mul hj' hs'
  have he:(state g s r q2 i.val j).length=
      2*((EncodedGraph.encode g).length+g.edges.length+s+r+g.vertices+q2+count s g.vertices+i.val+j+
        (accumulator g s r q2 i.val j).length)+10 := by
    unfold state
    rw [encode_length]
    simp [Fin.sum_univ_succ] <;> omega
  rw [he]
  change _ ≤ 24*(U+1)^2
  have hbase : (EncodedGraph.encode g).length+g.edges.length+s+r+g.vertices+q2+count s g.vertices=U-1 := by
    dsimp [U,measure]
  rw [hbase]
  have hsub:U-1 ≤ U:=Nat.sub_le _ _
  have ha':(accumulator g s r q2 i.val j).length ≤ 3*U^2+3*U+1:=by omega
  nlinarith

theorem measure_le_input (g : EncodedGraph.Graph) (s r q2 i : Nat) (carry : List Bool) :
    measure g s r q2 ≤ (input g s r q2 i carry).length := by
  unfold input measure
  rw [encode_length]
  simp [Fin.sum_univ_succ] <;> omega

def stepCap (n : Nat):=bodyCoefficient*(stateCap n+1)^bodyDegree
def loopCap (n : Nat):=5*(2*(stateCap n+n)+3)+n*BitMachineIteration.roundBound body.machine (stateCap n) (stepCap n)+2
def cap (n : Nat):=3*fuelCoefficient*(n+1)^fuelDegree+2+loopCap n+26*(stateCap n+1)

theorem clock_bound {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (i : Fin (count s g.vertices)) (carry : List Bool) :
    clock g s r q2 i.val carry ≤ cap (input g s r q2 i.val carry).length := by
  let N:=(input g s r q2 i.val carry).length
  have hmeasure:=measure_le_input g s r q2 i.val carry
  have hqN:q2 ≤ N:=by dsimp [N]; unfold measure at hmeasure; omega
  have hlen (j : Nat) (hj : j ≤ q2) : (state g s r q2 i.val j).length ≤ stateCap N := by
    apply (state_length g hg hn hs hq i j hj).trans
    unfold stateCap
    gcongr
  have htime (j : Nat) (hj : j ≤ q2) : body.clock (state g s r q2 i.val j) ≤ stepCap N := by
    have h:=body_envelope (state g s r q2 i.val j)
    have hm:=Nat.mul_le_mul_left bodyCoefficient (Nat.pow_le_pow_left (Nat.add_le_add_right (hlen j hj) 1) bodyDegree)
    change _ ≤ bodyCoefficient*(stateCap N+1)^bodyDegree
    omega
  have hc:=WeightedIterationClock.cumulative_le body.machine (state g s r q2 i.val)
    (fun j=>body.clock (state g s r q2 i.val j)) q2 (stateCap N) (stepCap N)
    (fun j hj=>hlen j hj.le) (fun j hj=>htime j hj.le)
  have hinit : (WeightedIterationDriver.input (state g s r q2 i.val 0) q2).length ≤
      2*(stateCap N+N)+2 := by
    have h0:=hlen 0 (by omega)
    simp [WeightedIterationDriver.input,WeightedIterationLoader.packet,encode_length,
      Fin.sum_univ_succ] <;> omega
  have hprod:=Nat.mul_le_mul_right (BitMachineIteration.roundBound body.machine (stateCap N) (stepCap N)) hqN
  have hloop:loopClock g s r q2 i.val ≤ loopCap N := by
    unfold loopClock WeightedIterationDriver.clock loopCap
    omega
  have hf:=fuel_envelope (input g s r q2 i.val carry)
  have hend:=hlen q2 le_rfl
  unfold clock cap
  change _ ≤ 3*fuelCoefficient*(N+1)^fuelDegree+2+loopCap N+26*(stateCap N+1)
  rw [show 3*fuelCoefficient*(N+1)^fuelDegree=3*(fuelCoefficient*(N+1)^fuelDegree) by ring]
  dsimp only [N] at *
  omega

theorem stateCap_polynomial : PolynomialBound (fun _ n=>stateCap n) :=
  GaussCellPolynomialClock.mul (GaussCellPolynomialClock.constant 24)
    (power (GaussCellPolynomialClock.add second (GaussCellPolynomialClock.constant 1)) 2)
theorem stepCap_polynomial : PolynomialBound (fun _ n=>stepCap n) :=
  GaussCellPolynomialClock.mul (GaussCellPolynomialClock.constant _)
    (power (GaussCellPolynomialClock.add stateCap_polynomial (GaussCellPolynomialClock.constant 1)) _)
theorem round_polynomial : PolynomialBound (fun _ n=>BitMachineIteration.roundBound body.machine (stateCap n) (stepCap n)) := by
  unfold BitMachineIteration.roundBound
  exact GaussCellPolynomialClock.add
    (GaussCellPolynomialClock.add
      (GaussCellPolynomialClock.add stepCap_polynomial
        (GaussCellPolynomialClock.mul (GaussCellPolynomialClock.constant (body.machine.stackCount+2))
          (GaussCellPolynomialClock.add stateCap_polynomial
            (GaussCellPolynomialClock.mul stepCap_polynomial (GaussCellPolynomialClock.constant body.machine.pushBound)))))
      (GaussCellPolynomialClock.constant body.machine.stackCount))
    (GaussCellPolynomialClock.constant 4)
theorem loopCap_polynomial : PolynomialBound (fun _ n=>loopCap n) :=
  GaussCellPolynomialClock.add (GaussCellPolynomialClock.add
    (GaussCellPolynomialClock.mul (GaussCellPolynomialClock.constant 5)
      (GaussCellPolynomialClock.add (GaussCellPolynomialClock.mul (GaussCellPolynomialClock.constant 2)
        (GaussCellPolynomialClock.add stateCap_polynomial second)) (GaussCellPolynomialClock.constant 3)))
    (GaussCellPolynomialClock.mul second round_polynomial)) (GaussCellPolynomialClock.constant 2)
theorem cap_polynomial : PolynomialBound (fun _ n=>cap n) :=
  GaussCellPolynomialClock.add (GaussCellPolynomialClock.add (GaussCellPolynomialClock.add
    (GaussCellPolynomialClock.mul (GaussCellPolynomialClock.constant (3*fuelCoefficient))
      (power (GaussCellPolynomialClock.add second (GaussCellPolynomialClock.constant 1)) fuelDegree))
    (GaussCellPolynomialClock.constant 2)) loopCap_polynomial)
    (GaussCellPolynomialClock.mul (GaussCellPolynomialClock.constant 26)
      (GaussCellPolynomialClock.add stateCap_polynomial (GaussCellPolynomialClock.constant 1)))
theorem exists_bound : ∃C d : Nat,∀n,cap n ≤ C*(n+1)^d := by
  obtain ⟨C,d,h⟩:=cap_polynomial
  exact ⟨C,d,fun n=>by simpa using h 0 n⟩
def coefficient:=Classical.choose exists_bound
def degree:=Classical.choose (Classical.choose_spec exists_bound)
theorem cap_bound (n : Nat):cap n ≤ coefficient*(n+1)^degree:=
  Classical.choose_spec (Classical.choose_spec exists_bound) n
theorem outputs_polynomial {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (i : Fin (count s g.vertices)) (carry : List Bool) :
    machine.OutputsWithin (input g s r q2 i.val carry) (packet g s r q2 i.val)
      (coefficient*((input g s r q2 i.val carry).length+1)^degree) := by
  apply BitMachine.outputsWithin_mono _ (outputs g hg hn hs hq i carry)
  exact (clock_bound g hg hn hs hq i carry).trans (cap_bound _)

#print axioms outputs_polynomial
end
end CurrentAdditive.V40ActivityRow
