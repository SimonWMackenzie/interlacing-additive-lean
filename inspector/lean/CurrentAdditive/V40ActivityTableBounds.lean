import CurrentAdditive.V40ActivityCurrent

namespace CurrentAdditive.V40ActivityTable
noncomputable section
open Paper2 EthInapproximability.CurrentPaper BitMachineBankCodec
open V40SourceLocal D22PacketPrimitives V40SourceClockBounds GaussCellPolynomialClock
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768

theorem body_polynomial : HasPolynomialEnvelope body := by
  have hr : HasPolynomialEnvelope row:=
    finite_run_polynomial V40ActivityRow.machine V40ActivityRow.coefficient V40ActivityRow.degree
  have hi : HasPolynomialEnvelope newItem:=compose_polynomial hr (physical_polynomial PhysicalProducer.item)
  apply serialise_polynomial
  intro k
  fin_cases k
  all_goals first | exact project_polynomial _ | skip
  · exact append_polynomial (constant_polynomial [true]) (project_polynomial _)
  · exact constant_polynomial []
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
    · exact constant_polynomial []
    · exact compose_polynomial (project_polynomial _) unary_field_polynomial
  · exact project_polynomial _
def bodyCoefficient:=Classical.choose body_polynomial
def bodyDegree:=Classical.choose (Classical.choose_spec body_polynomial)
theorem body_envelope : Envelope body bodyCoefficient bodyDegree:=
  Classical.choose_spec (Classical.choose_spec body_polynomial)
def fuelCoefficient:=Classical.choose withFuel_polynomial
def fuelDegree:=Classical.choose (Classical.choose_spec withFuel_polynomial)
theorem fuel_envelope : Envelope withFuel fuelCoefficient fuelDegree:=
  Classical.choose_spec (Classical.choose_spec withFuel_polynomial)
attribute [local irreducible] body withFuel bodyCoefficient bodyDegree fuelCoefficient fuelDegree

def measure (g : EncodedGraph.Graph) (s r q2 : Nat):=
  (EncodedGraph.encode g).length+g.edges.length+s+r+g.vertices+q2+count s g.vertices+1
def rowCap (n : Nat):=4*(n+1)^2
def stateCap (n : Nat):=100*(n+1)^3
theorem row_packet_length {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (i : Fin (count s g.vertices)) :
    (V40ActivityRow.packet g s r q2 i.val).length ≤ rowCap (measure g s r q2) := by
  have ha:=V40ActivityRow.accumulator_length g hg hn hs hq i q2 le_rfl
  have he:V40ActivityRow.packet g s r q2 i.val=V40ActivityRow.accumulator g s r q2 i.val q2 := by
    simp [V40ActivityRow.packet,V40ActivityRow.accumulator,SourceListEncoding.encode,V40ActivityRow.entries]
  rw [he]
  let U:=measure g s r q2
  have hq':q2 ≤ U:=by dsimp [U,measure]; omega
  have hs':s ≤ U:=by dsimp [U,measure]; omega
  have hm:q2*s ≤ U^2:=by simpa [pow_two] using Nat.mul_le_mul hq' hs'
  change _ ≤ 4*(U+1)^2
  nlinarith

theorem accumulator_length {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (j : Nat) (hj : j ≤ count s g.vertices) :
    (accumulator g s r q2 j).length ≤
      2*count s g.vertices+1+3*(j*rowCap (measure g s r q2))+j := by
  have ht:=SourceListEncoding.totalLength_map_le (List.range j)
    (fun i=>V40ActivityRow.packet g s r q2 i) (rowCap (measure g s r q2)) (by
      intro i hi
      exact row_packet_length g hg hn hs hq ⟨i,(List.mem_range.mp hi).trans_le hj⟩)
  have hf:=SourceListEncoding.fields_length (entries g s r q2 j)
  have hh:=EncodedGraph.natField_length_upper (count s g.vertices)
  simp only [List.length_range] at ht
  simp only [entries,List.length_map,List.length_range] at hf
  simp only [accumulator,List.length_append,entries]
  omega
theorem state_length {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r)
    (j : Nat) (hj : j ≤ count s g.vertices) :
    (state g s r q2 j).length ≤ stateCap (measure g s r q2) := by
  let U:=measure g s r q2
  have ha:=accumulator_length g hg hn hs hq j hj
  have hc:count s g.vertices ≤ U:=by dsimp [U,measure]; omega
  have hj':j ≤ U:=hj.trans hc
  have hm:=Nat.mul_le_mul_right (rowCap U) hj'
  have he:(state g s r q2 j).length=
      2*((EncodedGraph.encode g).length+g.edges.length+s+r+g.vertices+q2+count s g.vertices+j+
        (accumulator g s r q2 j).length)+10 := by
    unfold state V40ActivityRow.input
    rw [encode_length]
    simp [Fin.sum_univ_succ,count] <;> omega
  rw [he]
  have hbase:(EncodedGraph.encode g).length+g.edges.length+s+r+g.vertices+q2+count s g.vertices=U-1 := by
    dsimp [U,measure]
  rw [hbase]
  have hsub:U-1 ≤ U:=Nat.sub_le _ _
  change _ ≤ 100*(U+1)^3
  change j*(4*(U+1)^2) ≤ U*(4*(U+1)^2) at hm
  change (accumulator g s r q2 j).length ≤ 2*count s g.vertices+1+3*(j*(4*(U+1)^2))+j at ha
  nlinarith

theorem measure_le_input (g : EncodedGraph.Graph) (s r q2 : Nat) :
    measure g s r q2 ≤ (input g s r q2).length := by
  unfold input measure
  rw [encode_length]
  simp [Fin.sum_univ_succ,count] <;> omega

def stepCap (n : Nat):=bodyCoefficient*(stateCap n+1)^bodyDegree
def loopCap (n : Nat):=5*(2*(stateCap n+n)+3)+n*BitMachineIteration.roundBound body.machine (stateCap n) (stepCap n)+2
def cap (n : Nat):=3*fuelCoefficient*(n+1)^fuelDegree+2+loopCap n+26*(stateCap n+1)
theorem clock_bound {s r q2 : Nat} [NeZero s] (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r) :
    clock g s r q2 ≤ cap (input g s r q2).length := by
  let N:=(input g s r q2).length
  have hmeasure:=measure_le_input g s r q2
  have hcN:count s g.vertices ≤ N:=by dsimp [N]; unfold measure at hmeasure; omega
  have hlen (j : Nat) (hj : j ≤ count s g.vertices) : (state g s r q2 j).length ≤ stateCap N := by
    apply (state_length g hg hn hs hq j hj).trans
    unfold stateCap
    gcongr
  have htime (j : Nat) (hj : j ≤ count s g.vertices) : body.clock (state g s r q2 j) ≤ stepCap N := by
    have h:=body_envelope (state g s r q2 j)
    have hm:=Nat.mul_le_mul_left bodyCoefficient (Nat.pow_le_pow_left (Nat.add_le_add_right (hlen j hj) 1) bodyDegree)
    change _ ≤ bodyCoefficient*(stateCap N+1)^bodyDegree
    omega
  have hc:=WeightedIterationClock.cumulative_le body.machine (state g s r q2)
    (fun j=>body.clock (state g s r q2 j)) (count s g.vertices) (stateCap N) (stepCap N)
    (fun j hj=>hlen j hj.le) (fun j hj=>htime j hj.le)
  have hinit:(WeightedIterationDriver.input (state g s r q2 0) (count s g.vertices)).length ≤
      2*(stateCap N+N)+2 := by
    have h0:=hlen 0 (by omega)
    simp [WeightedIterationDriver.input,WeightedIterationLoader.packet,encode_length,Fin.sum_univ_succ] <;> omega
  have hprod:=Nat.mul_le_mul_right (BitMachineIteration.roundBound body.machine (stateCap N) (stepCap N)) hcN
  have hloop:loopClock g s r q2 ≤ loopCap N := by
    unfold loopClock WeightedIterationDriver.clock loopCap
    omega
  have hf:=fuel_envelope (input g s r q2)
  have hend:=hlen (count s g.vertices) le_rfl
  unfold clock cap
  change _ ≤ 3*fuelCoefficient*(N+1)^fuelDegree+2+loopCap N+26*(stateCap N+1)
  rw [show 3*fuelCoefficient*(N+1)^fuelDegree=3*(fuelCoefficient*(N+1)^fuelDegree) by ring]
  dsimp only [N] at *
  omega

theorem stateCap_polynomial : PolynomialBound (fun _ n=>stateCap n) :=
  GaussCellPolynomialClock.mul (GaussCellPolynomialClock.constant 100)
    (power (GaussCellPolynomialClock.add second (GaussCellPolynomialClock.constant 1)) 3)
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
    (hn : 0<g.vertices) (hs : 3 ≤ s) (hq : q2=LiteralEdgeEncoder.Width s g.edges.length r) :
    machine.OutputsWithin (input g s r q2)
      (StoredStepContext.activityWords (V39GeneratedConstruction.graphActivity hs hq (LiteralEdgeEncoder.edge g hg)))
      (coefficient*((input g s r q2).length+1)^degree) := by
  apply BitMachine.outputsWithin_mono _ (V40ActivityCurrent.outputs g hg hn hs hq)
  exact (clock_bound g hg hn hs hq).trans (cap_bound _)

#print axioms outputs_polynomial
end
end CurrentAdditive.V40ActivityTable
