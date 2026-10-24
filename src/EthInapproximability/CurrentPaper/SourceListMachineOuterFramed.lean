import EthInapproximability.CurrentPaper.SourceListMachineOuterRun
import EthInapproximability.CurrentPaper.SourceListMachineWriter
import EthInapproximability.CurrentPaper.BitMachineComposition

/-! Physical per-item output framing, composed with the actual list loop. -/

namespace EthInapproximability.CurrentPaper.SourceListMachineOuterFramed

open BitMachine BitMachineEncoding EncodedCommunication

variable (M : Machine)

def framedOutput (f : List Bool → List Bool) (x : List Bool) : List Bool :=
  natField (f x).length ++ f x

noncomputable def framedBound (f : List Bool → List Bool) (bound : List Bool → Nat)
    (x : List Bool) : Nat :=
  bound x + 2*(f x).length+2 +
    (UnaryBinaryEncoding.coefficient+7)*((f x).length+1)^2

noncomputable def itemMachine : Machine :=
  BitMachineComposition.composition M
    (SourceListMachineWriter.framingMachine true)

noncomputable def machine : Machine :=
  SourceListMachineOuter.machine (itemMachine M)

theorem framed_item (f : List Bool → List Bool) (bound : List Bool → Nat)
    (x : List Bool) (hM : M.OutputsWithin x (f x) (bound x)) :
    (itemMachine M).OutputsWithin x (framedOutput f x) (framedBound f bound x) := by
  have hw := SourceListMachineWriter.outputs true (f x)
  have hc := BitMachineComposition.composition_outputsWithin M
    (SourceListMachineWriter.framingMachine true) hM hw
  simpa only [itemMachine, framedOutput, framedBound,
    SourceListMachineWriter.result, Bool.true_eq, ↓reduceIte] using hc

theorem joined_framed (xs : List (List Bool)) (f : List Bool → List Bool) :
    SourceListMachineOuter.joined xs (framedOutput f) =
      SourceListEncoding.fields (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change (natField (f x).length ++ f x) ++
          SourceListMachineOuter.joined xs (framedOutput f) =
        (natField (f x).length ++ f x) ++ SourceListEncoding.fields (xs.map f)
      rw [ih]

theorem outputsWithin (xs : List (List Bool)) (f : List Bool → List Bool)
    (bound : List Bool → Nat)
    (hM : ∀ x ∈ xs, M.OutputsWithin x (f x) (bound x)) :
    (machine M).OutputsWithin (SourceListEncoding.encode xs)
      (SourceListEncoding.encode (xs.map f))
      (SourceListMachineOuter.canonicalBound (itemMachine M) xs
        (framedOutput f) (framedBound f bound)) := by
  have hi : ∀ x ∈ xs, (itemMachine M).OutputsWithin x
      (framedOutput f x) (framedBound f bound x) := by
    intro x hx
    exact framed_item M f bound x (hM x hx)
  have ho := SourceListMachineOuter.canonical_outputsWithin (itemMachine M)
    xs (framedOutput f) (framedBound f bound) hi
  simpa only [machine, SourceListEncoding.encode, List.length_map,
    joined_framed] using ho

end EthInapproximability.CurrentPaper.SourceListMachineOuterFramed
