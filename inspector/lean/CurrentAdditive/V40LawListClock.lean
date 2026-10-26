import CurrentAdditive.RatioMappedListPolynomial
set_option autoImplicit false
namespace CurrentAdditive.V40LawListClock
open EthInapproximability.CurrentPaper RatioMappedListPolynomial
noncomputable section
theorem clock_le_on (M : BitMachine.Machine) (f : List Bool → List Bool)
    (T : List Bool → Nat) (C d : Nat)
    (xs : List (List Bool)) (hM : ∀ x ∈ xs,M.OutputsWithin x (f x) (T x))
    (hT : ∀ x,T x ≤ C*(x.length+1)^d) :
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
    have ho := BitMachine.output_length_bound M (hM x hx)
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

end
end CurrentAdditive.V40LawListClock
