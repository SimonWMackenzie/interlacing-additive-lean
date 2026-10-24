import EthInapproximability.CurrentPaper.SourceListMachineOuterRun
import EthInapproximability.CurrentPaper.SourceListMachineWriter
import EthInapproximability.CurrentPaper.BitMachineComposition

/-! A fixed TM2 vector serializer assembled from any physical coefficient
machine. Its input is a V2 list of per-column work packets; its output is
the V2 list of the coefficient machine's actual output words. Constructing
those work packets from the Gauss state is a separate controller obligation.
-/

namespace CurrentAdditive.GaussVectorOuterWriter

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

variable (M : BitMachine.Machine)

noncomputable def framedMachine : BitMachine.Machine :=
  BitMachineComposition.composition M
    (SourceListMachineWriter.framingMachine true)

noncomputable def machine : BitMachine.Machine :=
  SourceListMachineOuter.machine (framedMachine M)

noncomputable def itemClock (F : List Bool → List Bool) (bound : List Bool → Nat)
    (x : List Bool) : Nat :=
  bound x + 2 * (F x).length + 2 +
    (EthInapproximability.CurrentPaper.UnaryBinaryEncoding.coefficient + 7) *
      ((F x).length + 1) ^ 2

theorem framed_outputs (F : List Bool → List Bool)
    (bound : List Bool → Nat) (x : List Bool)
    (hM : M.OutputsWithin x (F x) (bound x)) :
    (framedMachine M).OutputsWithin x
      (SourceListMachineWriter.result true (F x))
      (itemClock F bound x) := by
  exact BitMachineComposition.composition_outputsWithin M
    (SourceListMachineWriter.framingMachine true) hM
    (SourceListMachineWriter.outputs true (F x))

theorem joined_framed (xs : List (List Bool))
    (F : List Bool → List Bool) :
    SourceListMachineOuter.joined xs
      (fun x => SourceListMachineWriter.result true (F x)) =
      SourceListEncoding.fields (xs.map F) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [SourceListMachineOuter.joined_cons, List.map_cons,
        SourceListEncoding.fields]
      rw [ih]
      simp [SourceListMachineWriter.result, List.append_assoc]

theorem outputs_prepared (xs : List (List Bool))
    (F : List Bool → List Bool) (bound : List Bool → Nat)
    (hM : ∀ x ∈ xs, M.OutputsWithin x (F x) (bound x)) :
    (machine M).OutputsWithin (SourceListEncoding.encode xs)
      (SourceListEncoding.encode (xs.map F))
      (SourceListMachineOuter.canonicalBound (framedMachine M) xs
        (fun x => SourceListMachineWriter.result true (F x))
        (itemClock F bound)) := by
  have hitem : ∀ x ∈ xs,
      (framedMachine M).OutputsWithin x
        (SourceListMachineWriter.result true (F x))
        (itemClock F bound x) := by
    intro x hx
    exact framed_outputs M F bound x (hM x hx)
  have h := SourceListMachineOuter.canonical_outputsWithin
    (framedMachine M) xs
    (fun x => SourceListMachineWriter.result true (F x))
    (itemClock F bound) hitem
  simpa [machine, SourceListEncoding.encode, joined_framed] using h

noncomputable def uniformItemClock (Q P : Nat) : Nat :=
  P + 2 * Q + 2 +
    (EthInapproximability.CurrentPaper.UnaryBinaryEncoding.coefficient + 7) *
      (Q + 1) ^ 2

noncomputable def uniformItemCost (L Q P : Nat) : Nat :=
  let N := framedMachine M
  let T := uniformItemClock Q P
  let R := 3 * Q + 1
  20 * (L + 1) * (L + 1) + T + 4 * L + R +
    N.stackCount * (L + T * N.pushBound + 1) + 9

noncomputable def preparedClock (count L Q P : Nat) : Nat :=
  let R := 3 * Q + 1
  5 * count.bits.length + 7 +
    (count * uniformItemCost M L Q P +
      count * (4 * count.bits.length + 7)) +
    (4 * count.bits.length + (natField count).length + count * R + 9)

theorem canonicalBound_le_preparedClock (xs : List (List Bool))
    (F : List Bool → List Bool) (bound : List Bool → Nat)
    (L Q P : Nat)
    (hin : ∀ x ∈ xs, x.length ≤ L)
    (hout : ∀ x ∈ xs, (F x).length ≤ Q)
    (htime : ∀ x ∈ xs, bound x ≤ P) :
    SourceListMachineOuter.canonicalBound (framedMachine M) xs
      (fun x => SourceListMachineWriter.result true (F x))
      (itemClock F bound) ≤
    preparedClock M xs.length L Q P := by
  let N := framedMachine M
  let R := 3 * Q + 1
  let T := uniformItemClock Q P
  have hresult : ∀ x ∈ xs,
      (SourceListMachineWriter.result true (F x)).length ≤ R := by
    intro x hx
    have h := SourceListMachineWriter.result_length true (F x)
    have hQ := hout x hx
    dsimp [R]
    omega
  have hcost : ∀ x ∈ xs,
      SourceListMachineWork.itemCost N x
        (SourceListMachineWriter.result true (F x))
        (itemClock F bound x) ≤ uniformItemCost M L Q P := by
    intro x hx
    have hT : itemClock F bound x ≤ T := by
      have hP := htime x hx
      have hQ := hout x hx
      have hq1 : (F x).length + 1 ≤ Q + 1 := by omega
      have hs : ((F x).length + 1) ^ 2 ≤ (Q + 1) ^ 2 :=
        Nat.pow_le_pow_left hq1 2
      have hm := Nat.mul_le_mul_left
        (EthInapproximability.CurrentPaper.UnaryBinaryEncoding.coefficient + 7) hs
      dsimp [itemClock, T, uniformItemClock]
      omega
    exact SourceListMachineWork.itemCost_le_envelope N x
      (SourceListMachineWriter.result true (F x))
      (itemClock F bound x) L R T
      (hin x hx) (hresult x hx) hT
  have hb := SourceListMachineOuter.canonicalBound_le_count N xs
    (fun x => SourceListMachineWriter.result true (F x))
    (itemClock F bound) (uniformItemCost M L Q P) R hcost hresult
  simpa [preparedClock, R, N] using hb

theorem outputs_prepared_uniform (xs : List (List Bool))
    (F : List Bool → List Bool) (bound : List Bool → Nat)
    (L Q P : Nat)
    (hM : ∀ x ∈ xs, M.OutputsWithin x (F x) (bound x))
    (hin : ∀ x ∈ xs, x.length ≤ L)
    (hout : ∀ x ∈ xs, (F x).length ≤ Q)
    (htime : ∀ x ∈ xs, bound x ≤ P) :
    (machine M).OutputsWithin (SourceListEncoding.encode xs)
      (SourceListEncoding.encode (xs.map F))
      (preparedClock M xs.length L Q P) := by
  apply BitMachine.outputsWithin_mono _
    (outputs_prepared M xs F bound hM)
  exact canonicalBound_le_preparedClock M xs F bound L Q P
    hin hout htime

#print axioms outputs_prepared
#print axioms outputs_prepared_uniform

end CurrentAdditive.GaussVectorOuterWriter
