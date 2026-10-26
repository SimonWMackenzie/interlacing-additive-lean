import CurrentAdditive.V40LawProductEntry
import CurrentAdditive.V40LawListClock

set_option autoImplicit false
namespace CurrentAdditive.V40LawProductList
noncomputable section
open EthInapproximability.CurrentPaper
open CodeDCodec
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

abbrev Job := ℕ × (ℚ × ℚ)

def inputItems (jobs : List Job) : List (List Bool) :=
  jobs.map (fun j => V40LawProductEntry.input j.1 j.2.1 j.2.2)

def alphabet (jobs : List Job) : Array (ℕ × ℚ) :=
  (jobs.map (fun j => (j.1,j.2.1*j.2.2))).toArray

def itemResult (word : List Bool) : List Bool :=
  match BitMachineBankCodec.decode 2 word with
  | none => []
  | some S => V40LawPacket.packet (S 0) (RationalCanonicalCallback.productResult (S 1))

theorem itemResult_input (index : ℕ) (x y : ℚ) :
    itemResult (V40LawProductEntry.input index x y)=CodeDTargetV2.alphabetEntry (index,x*y) := by
  simp only [itemResult,V40LawProductEntry.input,V40LawPacket.packet_decode]
  simp only [V40LawPacket.bank,show (1:Fin 2)≠0 by decide,↓reduceIte]
  rw [RationalCanonicalCallback.product_result_pair _ _
    (CodeDCanonicalSource.rawOfRat_valid x) (CodeDCanonicalSource.rawOfRat_valid y),
    CodeDCanonicalSource.rawOfRat_value,CodeDCanonicalSource.rawOfRat_value]
  rfl

def coefficient : ℕ:=V40LawProductEntry.outputs.choose

def itemBound (word : List Bool) : ℕ:=coefficient*(word.length+3)^97

def machine : BitMachine.Machine:=SourceListMachineOuterFramed.machine V40LawProductEntry.machine

def clock (jobs : List Job) : ℕ:=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine V40LawProductEntry.machine) (inputItems jobs)
    (SourceListMachineOuterFramed.framedOutput itemResult)
    (SourceListMachineOuterFramed.framedBound itemResult itemBound)

theorem item_outputs (jobs : List Job) : ∀ x∈inputItems jobs,
    V40LawProductEntry.machine.OutputsWithin x (itemResult x) (itemBound x) := by
  intro x hx
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hx
  rw [itemResult_input]
  exact V40LawProductEntry.outputs.choose_spec _ _ _

/-- The whole output list has exactly the original positions and labels,
including repeats, with the exact canonical product at each position. -/
theorem outputs (jobs : List Job) :
    machine.OutputsWithin (SourceListEncoding.encode (inputItems jobs))
      (CodeDTargetV2.alphabetBytes (alphabet jobs)) (clock jobs) := by
  have h:=SourceListMachineOuterFramed.outputsWithin V40LawProductEntry.machine
    (inputItems jobs) itemResult itemBound (item_outputs jobs)
  have he : (inputItems jobs).map itemResult=
      (alphabet jobs).toList.map CodeDTargetV2.alphabetEntry := by
    simp only [inputItems,alphabet,List.toList_toArray,List.map_map]
    apply List.map_congr_left
    intro j _
    exact itemResult_input _ _ _
  rw [he] at h
  exact h

theorem itemBound_le (word : List Bool) :
    itemBound word≤(coefficient*3^97)*(word.length+1)^97 := by
  have hp:word.length+3≤3*(word.length+1) := by omega
  have h:=Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left hp 97)
  simpa only [itemBound,mul_pow,Nat.mul_assoc] using h

theorem clock_le (jobs : List Job) :
    clock jobs≤RatioMappedListPolynomial.clockCap V40LawProductEntry.machine
      (coefficient*3^97) 97 (SourceListEncoding.encode (inputItems jobs)).length := by
  exact V40LawListClock.clock_le_on V40LawProductEntry.machine itemResult itemBound
    (coefficient*3^97) 97 (inputItems jobs) (item_outputs jobs) itemBound_le

/-- A single fixed physical list serializer and one byte polynomial, with
no supplied result, run, law or value-only equality hypothesis. -/
theorem outputs_polynomial : ∃ C d : ℕ, ∀ jobs : List Job,
    machine.OutputsWithin (SourceListEncoding.encode (inputItems jobs))
      (CodeDTargetV2.alphabetBytes (alphabet jobs))
      (C*((SourceListEncoding.encode (inputItems jobs)).length+1)^d) := by
  obtain ⟨C,d,hC⟩:=RatioMappedListPolynomial.clockCap_poly V40LawProductEntry.machine
    (coefficient*3^97) 97
  exact ⟨C,d,fun jobs => BitMachine.outputsWithin_mono _ (outputs jobs)
    ((clock_le jobs).trans (hC _))⟩

theorem positions (jobs : List Job) : (alphabet jobs).toList.map Prod.fst=jobs.map Prod.fst := by
  simp [alphabet,List.map_map]

#print axioms outputs
#print axioms outputs_polynomial
#print axioms positions
end
end CurrentAdditive.V40LawProductList
