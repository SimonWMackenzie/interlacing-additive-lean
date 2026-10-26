import CurrentAdditive.RatioUpdaterItemPolynomial

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
noncomputable section
namespace CurrentAdditive.RatioMappedListPolynomial
open EthInapproximability.CurrentPaper EntryClockPoly
open RatioUpdaterItemPolynomial

def outputCap (M : BitMachine.Machine) (C d n : Nat) := n+C*(n+1)^d*M.pushBound
def timeCap (M : BitMachine.Machine) (C d n : Nat) :=
  C*(n+1)^d+2*outputCap M C d n+2+
    (UnaryBinaryEncoding.coefficient+7)*(outputCap M C d n+1)^2
def frameCap (M : BitMachine.Machine) (C d n : Nat) := 3*outputCap M C d n+1
def itemEnvelope (M : BitMachine.Machine) (C d n : Nat) :=
  20*(n+1)*(n+1)+timeCap M C d n+4*n+frameCap M C d n+
    (SourceListMachineOuterFramed.itemMachine M).stackCount*
      (n+timeCap M C d n*(SourceListMachineOuterFramed.itemMachine M).pushBound+1)+9
def clockCap (M : BitMachine.Machine) (C d n : Nat) :=
  n*(itemEnvelope M C d n+4*n+7+frameCap M C d n)+11*n+17

theorem clockCap_poly (M : BitMachine.Machine) (C d : Nat) :
    PolyIn (fun n : Nat => n) (clockCap M C d) := by
  unfold clockCap itemEnvelope timeCap frameCap outputCap
  solve_update_poly

theorem clock_le (M : BitMachine.Machine) (f : List Bool → List Bool)
    (T : List Bool → Nat) (C d : Nat)
    (hM : ∀ x,M.OutputsWithin x (f x) (T x))
    (hT : ∀ x,T x ≤ C*(x.length+1)^d) (xs : List (List Bool)) :
    SourceListMachineOuter.canonicalBound (SourceListMachineOuterFramed.itemMachine M) xs
      (SourceListMachineOuterFramed.framedOutput f)
      (SourceListMachineOuterFramed.framedBound f T) ≤
      clockCap M C d (SourceListEncoding.encode xs).length := by
  let n := (SourceListEncoding.encode xs).length
  have hn := GaussRowCount.rows_le_input xs
  have hword (x : List Bool) (hx : x ∈ xs) : x.length ≤ n :=
    RatioListClockBounds.word_le_packet xs x hx
  have htime (x : List Bool) (hx : x ∈ xs) : T x ≤ C*(n+1)^d :=
    (hT x).trans (by gcongr; exact hword x hx)
  have hout (x : List Bool) (hx : x ∈ xs) : (f x).length ≤ outputCap M C d n := by
    have ho := BitMachine.output_length_bound M (hM x)
    exact ho.trans (by unfold outputCap; gcongr <;> first | exact hword x hx | exact htime x hx)
  have hfout (x : List Bool) (hx : x ∈ xs) :
      (SourceListMachineOuterFramed.framedOutput f x).length ≤ frameCap M C d n := by
    have hf := EncodedGraph.natField_length_upper (f x).length
    have ho := hout x hx
    unfold SourceListMachineOuterFramed.framedOutput frameCap
    simp only [List.length_append]
    omega
  have hftime (x : List Bool) (hx : x ∈ xs) :
      SourceListMachineOuterFramed.framedBound f T x ≤ timeCap M C d n := by
    unfold SourceListMachineOuterFramed.framedBound timeCap
    gcongr <;> first | exact htime x hx | exact hout x hx
  have hi (x : List Bool) (hx : x ∈ xs) :
      SourceListMachineWork.itemCost (SourceListMachineOuterFramed.itemMachine M) x
        (SourceListMachineOuterFramed.framedOutput f x)
        (SourceListMachineOuterFramed.framedBound f T x) ≤ itemEnvelope M C d n :=
    SourceListMachineWork.itemCost_le_envelope _ _ _ _ n (frameCap M C d n)
      (timeCap M C d n) (hword x hx) (hfout x hx) (hftime x hx)
  have hb := SourceListMachineOuter.canonicalBound_le_source
    (SourceListMachineOuterFramed.itemMachine M) xs
    (SourceListMachineOuterFramed.framedOutput f)
    (SourceListMachineOuterFramed.framedBound f T) n id id (itemEnvelope M C d) (frameCap M C d)
    hn ((UnaryBinaryEncoding.bits_length_le xs.length).trans hn) hi hfout
  exact hb

theorem mapped_clock_poly (M : BitMachine.Machine) (f : List Bool → List Bool)
    (T : List Bool → Nat) (hM : ∀ x,M.OutputsWithin x (f x) (T x))
    (hT : PolyIn byteSize T) :
    PolyIn (fun xs : List (List Bool) => (SourceListEncoding.encode xs).length)
      (fun xs => SourceListMachineOuter.canonicalBound (SourceListMachineOuterFramed.itemMachine M) xs
        (SourceListMachineOuterFramed.framedOutput f)
        (SourceListMachineOuterFramed.framedBound f T)) := by
  obtain ⟨C,d,hC⟩ := hT
  apply PolyIn.mono (fun xs => clock_le M f T C d hM hC xs)
  exact (clockCap_poly M C d).comap
    (fun xs => (SourceListEncoding.encode xs).length) (fun _ => le_rfl)

theorem arithmetic_list_poly :
    PolyIn (fun xs => (SourceListEncoding.encode xs).length) CodeDUpdateFinalPairList.clock :=
  mapped_clock_poly _ _ _ CodeDUpdateFinalPairJoin.outputs arithmetic_item_poly

theorem entry_list_poly :
    PolyIn (fun xs => (SourceListEncoding.encode xs).length) CodeDUpdatedEntryList.clock :=
  mapped_clock_poly _ _ _ CodeDUpdatedEntryJoin.outputs entry_item_poly

#print axioms arithmetic_list_poly
#print axioms entry_list_poly
end CurrentAdditive.RatioMappedListPolynomial
