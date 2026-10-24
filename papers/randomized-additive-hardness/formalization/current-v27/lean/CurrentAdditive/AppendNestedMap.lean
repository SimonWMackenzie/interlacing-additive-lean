import CurrentAdditive.AppendOrdinaryPrep
import CurrentAdditive.FeatureContextMap

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

/-! A literal two-dimensional traversal. Original source indices are the
outer loop and original alphabet indices are the inner loop. The machine
contains two concrete contextual list mappers, with no callback contract
left as a premise. -/
namespace CurrentAdditive.AppendNestedMap
open EthInapproximability.CurrentPaper
open PhysicalProducer
noncomputable section

def packet := FeatureMapPairLoader.packet
def input (xs ys : List (List Bool)) := packet (SourceListEncoding.encode xs) (SourceListEncoding.encode ys)
def pairResult (A : Producer) (x y : List Bool) := A.result (packet x y)
def pairTime (A : Producer) (x y : List Bool) := A.coefficient*((packet x y).length+1)^A.degree

def pairRun (A : Producer) (x : List Bool) (ys : List (List Bool)) :
    ∀ y∈ys,A.machine.OutputsWithin (packet x y) (pairResult A x y) (pairTime A x y) :=
  fun y _ => A.outputs (packet x y)

def innerClock (A : Producer) (framed : Bool) (ys : List (List Bool)) (x : List Bool) :=
  FeatureContextMap.sumClock A.machine framed x ys (pairResult A x) (pairTime A x) (pairRun A x ys)

def rowRawMachine (A : Producer) (framed : Bool) : BitMachine.Machine :=
  BitMachineComposition.composition AppendOrdinaryPrep.swap.machine (FeatureContextMap.machine A.machine framed)

def rowRawResult (A : Producer) (framed : Bool) (ys : List (List Bool)) (x : List Bool) :=
  FeatureContextMap.result framed ys (pairResult A x)

def rowRawClock (A : Producer) (framed : Bool) (ys : List (List Bool)) (x : List Bool) :=
  AppendOrdinaryPrep.swap.coefficient*((packet (SourceListEncoding.encode ys) x).length+1)^AppendOrdinaryPrep.swap.degree +
  2*(packet x (SourceListEncoding.encode ys)).length+2+innerClock A framed ys x

theorem rowRaw_outputs (A : Producer) (framed : Bool) (ys : List (List Bool)) (x : List Bool) :
    (rowRawMachine A framed).OutputsWithin (packet (SourceListEncoding.encode ys) x)
      (rowRawResult A framed ys x) (rowRawClock A framed ys x) := by
  have hs := AppendOrdinaryPrep.swap.outputs (packet (SourceListEncoding.encode ys) x)
  rw [show AppendOrdinaryPrep.swap.result (packet (SourceListEncoding.encode ys) x) =
    packet x (SourceListEncoding.encode ys) from AppendOrdinaryPrep.swap_packet _ _] at hs
  exact BitMachineComposition.composition_outputsWithin _ _ hs
    (FeatureContextMap.outputs A.machine framed x ys (pairResult A x) (pairTime A x) (pairRun A x ys))

def rowMachine (A : Producer) (framed : Bool) : BitMachine.Machine :=
  if framed then BitMachineComposition.composition (rowRawMachine A true) CodeDStripHeaderV2.machine
  else rowRawMachine A false

def rowResult (A : Producer) (framed : Bool) (ys : List (List Bool)) (x : List Bool) :=
  if framed then SourceListEncoding.fields (ys.map (pairResult A x)) else ys.flatMap (pairResult A x)

def rowClock (A : Producer) (framed : Bool) (ys : List (List Bool)) (x : List Bool) :=
  if framed then rowRawClock A true ys x + 4*(rowRawResult A true ys x).length+5
  else rowRawClock A false ys x

theorem row_outputs (A : Producer) (framed : Bool) (ys : List (List Bool)) (x : List Bool) :
    (rowMachine A framed).OutputsWithin (packet (SourceListEncoding.encode ys) x)
      (rowResult A framed ys x) (rowClock A framed ys x) := by
  cases framed with
  | false => exact rowRaw_outputs A false ys x
  | true =>
    have h := rowRaw_outputs A true ys x
    have hstrip := CodeDStripHeaderV2.outputs_valid (ys.map (pairResult A x)).length
      (SourceListEncoding.fields (ys.map (pairResult A x)))
    have hc := BitMachineComposition.composition_outputsWithin
      (rowRawMachine A true) CodeDStripHeaderV2.machine h hstrip
    apply BitMachine.outputsWithin_mono _ hc
    dsimp [rowClock,rowRawResult,FeatureContextMap.result,SourceListEncoding.encode]
    omega

def outerRun (A : Producer) (framed : Bool) (xs ys : List (List Bool)) :
    ∀ x∈xs,(rowMachine A framed).OutputsWithin (packet (SourceListEncoding.encode ys) x)
      (rowResult A framed ys x) (rowClock A framed ys x) := fun x _ => row_outputs A framed ys x

def bodyMachine (A : Producer) (framed : Bool) : BitMachine.Machine :=
  BitMachineComposition.composition AppendOrdinaryPrep.swap.machine
    (FeatureContextMap.machine (rowMachine A framed) false)

def bodyResult (A : Producer) (framed : Bool) (xs ys : List (List Bool)) :=
  xs.flatMap (rowResult A framed ys)

def bodyClock (A : Producer) (framed : Bool) (xs ys : List (List Bool)) :=
  AppendOrdinaryPrep.swap.coefficient*((input xs ys).length+1)^AppendOrdinaryPrep.swap.degree+
  2*(packet (SourceListEncoding.encode ys) (SourceListEncoding.encode xs)).length+2+
  FeatureContextMap.sumClock (rowMachine A framed) false (SourceListEncoding.encode ys) xs
    (rowResult A framed ys) (rowClock A framed ys) (outerRun A framed xs ys)

theorem body_outputs (A : Producer) (framed : Bool) (xs ys : List (List Bool)) :
    (bodyMachine A framed).OutputsWithin (input xs ys)
      (bodyResult A framed xs ys) (bodyClock A framed xs ys) := by
  have hs := AppendOrdinaryPrep.swap.outputs (input xs ys)
  rw [show AppendOrdinaryPrep.swap.result (input xs ys) =
    packet (SourceListEncoding.encode ys) (SourceListEncoding.encode xs)
    from AppendOrdinaryPrep.swap_packet _ _] at hs
  exact BitMachineComposition.composition_outputsWithin _ _ hs
    (FeatureContextMap.outputs (rowMachine A framed) false
      (SourceListEncoding.encode ys) xs (rowResult A framed ys)
      (rowClock A framed ys) (outerRun A framed xs ys))

#print axioms body_outputs
end
end CurrentAdditive.AppendNestedMap
