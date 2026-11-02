import CurrentAdditive.FeatureMapContract
import CurrentAdditive.GaussSearchClock

/-! Exact scalar definitions copied with the physical owner's permission.
The final bridge identifies these recurrences with FeatureMapClock; no
physical run or desired output is assumed by this arithmetic layer. -/
noncomputable section
namespace CurrentAdditive.ContextMapClockModel
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussListContext FeatureMapPairLoader FeatureMapInvoke

def callbackCap (M : BitMachine.Machine) (framed : Bool)
    (context word output answer : List Bool) (T : Nat) : Nat :=
  word.length+1+FeatureMapAppend.coreBudget M framed context word output answer T

def cycleCap (M : BitMachine.Machine) (framed : Bool)
    (context header : List Bool) (f : List Bool → List Bool) (b : List Bool → Nat)
    (pre : List (List Bool)) (w : List Bool) (suf : List (List Bool)) : Nat :=
  StatefulListScheduler.getterBudget pre w suf+
    (callbackCap M framed context w
      (header++FeatureMapSourceScheduler.joined (FeatureMapContract.piece framed f) pre)
      (f w) (b w)+1)+1+
    ((SourceListEncoding.fields suf).length+(packet context w).length+11)+1

def sumCap (M : BitMachine.Machine) (framed : Bool)
    (context header : List Bool) (f : List Bool → List Bool) (b : List Bool → Nat)
    (pre : List (List Bool)) (suf : List (List Bool)) : Nat :=
  match suf with
  | [] => 1
  | w::tail => 1+cycleCap M framed context header f b pre w tail+
      sumCap M framed context header f b (pre++[w]) tail
end CurrentAdditive.ContextMapClockModel
