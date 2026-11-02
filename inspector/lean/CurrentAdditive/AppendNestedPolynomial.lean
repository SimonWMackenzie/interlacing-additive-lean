import CurrentAdditive.AppendNestedMap
import CurrentAdditive.CylinderEvalMapPolynomial

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace CurrentAdditive.AppendNestedPolynomial
open EthInapproximability.CurrentPaper
open PhysicalProducer AppendNestedMap
noncomputable section

def composeCoefficient (M : BitMachine.Machine) (cf cg dg : Nat) :=
  cf+2*(cf*M.pushBound+1)+cg*(cf*M.pushBound+1)^dg

def composeDegree (df dg : Nat) := (df+1)*(dg+1)

theorem compose_outputs (M N : BitMachine.Machine) (input middle output : List Bool)
    (cf df cg dg : Nat)
    (hf : M.OutputsWithin input middle (cf*(input.length+1)^df))
    (hg : N.OutputsWithin middle output (cg*(middle.length+1)^dg)) :
    (BitMachineComposition.composition M N).OutputsWithin input output
      (composeCoefficient M cf cg dg*(input.length+1)^composeDegree df dg) := by
  apply BitMachine.outputsWithin_mono _ (BitMachineComposition.composition_outputsWithin M N hf hg)
  exact BitMachineCompositionArithmetic.composition_time_bound input.length cf df cg dg M.pushBound middle.length
    (BitMachine.output_length_bound M hf)

theorem inner_uniform (A : Producer) (framed : Bool) : ∃ K E : Nat,
    ∀ x : List Bool,∀ ys : List (List Bool),
      (FeatureContextMap.machine A.machine framed).OutputsWithin
        (packet x (SourceListEncoding.encode ys)) (rowRawResult A framed ys x)
        (K*((packet x (SourceListEncoding.encode ys)).length+1)^E) := by
  obtain ⟨K,E,hcap⟩ := CylinderEvalMapPolynomial.uniform_from_callback A.machine framed A.coefficient A.degree
  refine ⟨K,E,fun x ys => ?_⟩
  exact BitMachine.outputsWithin_mono _
    (FeatureContextMap.outputs_explicit A.machine framed x ys (pairResult A x) (pairTime A x) (pairRun A x ys))
    (hcap x ys (pairResult A x) (pairTime A x) (pairRun A x ys) (fun y hy => le_rfl))

theorem rowRaw_uniform (A : Producer) (framed : Bool) : ∃ c d : Nat,
    ∀ ys : List (List Bool),∀ x : List Bool,
      (rowRawMachine A framed).OutputsWithin (packet (SourceListEncoding.encode ys) x)
        (rowRawResult A framed ys x)
        (c*((packet (SourceListEncoding.encode ys) x).length+1)^d) := by
  obtain ⟨K,E,h⟩ := inner_uniform A framed
  refine ⟨composeCoefficient AppendOrdinaryPrep.swap.machine AppendOrdinaryPrep.swap.coefficient K E,
    composeDegree AppendOrdinaryPrep.swap.degree E,fun ys x => ?_⟩
  have hs := AppendOrdinaryPrep.swap.outputs (packet (SourceListEncoding.encode ys) x)
  rw [show AppendOrdinaryPrep.swap.result (packet (SourceListEncoding.encode ys) x) =
    packet x (SourceListEncoding.encode ys) from AppendOrdinaryPrep.swap_packet _ _] at hs
  exact compose_outputs _ _ _ _ _ _ _ _ _ hs (h x ys)

theorem row_uniform (A : Producer) (framed : Bool) : ∃ c d : Nat,
    ∀ ys : List (List Bool),∀ x : List Bool,
      (rowMachine A framed).OutputsWithin (packet (SourceListEncoding.encode ys) x)
        (rowResult A framed ys x)
        (c*((packet (SourceListEncoding.encode ys) x).length+1)^d) := by
  cases framed with
  | false => exact rowRaw_uniform A false
  | true =>
    obtain ⟨K,E,h⟩ := rowRaw_uniform A true
    refine ⟨composeCoefficient (rowRawMachine A true) K stripHeader.coefficient stripHeader.degree,
      composeDegree E stripHeader.degree,fun ys x => ?_⟩
    have hs := stripHeader.outputs (rowRawResult A true ys x)
    have he : stripHeader.result (rowRawResult A true ys x) = rowResult A true ys x := by
      exact AppendEntryPhysical.strip_encode (ys.map (pairResult A x))
    rw [he] at hs
    exact compose_outputs _ _ _ _ _ _ _ _ _ (h ys x) hs

theorem body_uniform (A : Producer) (framed : Bool) : ∃ c d : Nat,
    ∀ xs ys : List (List Bool),
      (bodyMachine A framed).OutputsWithin (input xs ys) (bodyResult A framed xs ys)
        (c*((input xs ys).length+1)^d) := by
  obtain ⟨a,e,hrow⟩ := row_uniform A framed
  obtain ⟨K,E,hcap⟩ := CylinderEvalMapPolynomial.uniform_from_callback (rowMachine A framed) false a e
  refine ⟨composeCoefficient AppendOrdinaryPrep.swap.machine AppendOrdinaryPrep.swap.coefficient K E,
    composeDegree AppendOrdinaryPrep.swap.degree E,fun xs ys => ?_⟩
  let b := fun x => a*((packet (SourceListEncoding.encode ys) x).length+1)^e
  have hM : ∀ x∈xs,(rowMachine A framed).OutputsWithin (packet (SourceListEncoding.encode ys) x)
      (rowResult A framed ys x) (b x) := fun x _ => hrow ys x
  have ho := FeatureContextMap.outputs_explicit (rowMachine A framed) false
    (SourceListEncoding.encode ys) xs (rowResult A framed ys) b hM
  have hop := BitMachine.outputsWithin_mono _ ho
    (hcap (SourceListEncoding.encode ys) xs (rowResult A framed ys) b hM (fun x hx => le_rfl))
  have hs := AppendOrdinaryPrep.swap.outputs (input xs ys)
  rw [show AppendOrdinaryPrep.swap.result (input xs ys) =
    packet (SourceListEncoding.encode ys) (SourceListEncoding.encode xs)
    from AppendOrdinaryPrep.swap_packet _ _] at hs
  exact compose_outputs _ _ _ _ _ _ _ _ _ hs hop

#print axioms body_uniform
end
end CurrentAdditive.AppendNestedPolynomial
