import CurrentAdditive.V40IndexedLawLoop
import CurrentAdditive.V40SourceClockBounds

namespace CurrentAdditive.V40IndexedLawPolynomial
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication BitMachineBankCodec
open V40SourceContextSpec V40SourceLocal V40IndexedLawLoop V40SourceClockBounds
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

theorem body_polynomial : HasPolynomialEnvelope body := by
  apply serialise_polynomial
  intro i
  fin_cases i
  · exact append_polynomial (constant_polynomial _) (project_polynomial _)
  · exact project_polynomial _
  · exact project_polynomial _
  · exact project_polynomial _
  · apply append_polynomial (project_polynomial _)
    apply compose_polynomial
    · apply compose_polynomial
      · apply serialise_polynomial
        intro k
        fin_cases k
        · exact project_polynomial _
        · exact scalar_polynomial _ _ _ _ denTerm_pure
      · exact physical_polynomial _
    · exact physical_polynomial _

theorem withFuel_polynomial : HasPolynomialEnvelope withFuel := by
  apply serialise_polynomial
  intro i
  fin_cases i
  · apply serialise_polynomial
    intro k
    fin_cases k
    · exact constant_polynomial _
    · exact project_polynomial _
    · exact project_polynomial _
    · exact project_polynomial _
    · exact compose_polynomial (project_polynomial _) unary_field_polynomial
  · exact project_polynomial _

theorem input_lengths (s n : Nat) :
    n ≤ (input s n).length ∧ s ≤ (input s n).length ∧ count s n ≤ (input s n).length := by
  constructor
  · simpa only [List.length_replicate,Matrix.cons_val_zero] using
      word_length_le_encode (![(List.replicate n true),(List.replicate s true),
        (List.replicate (count s n) true)]) (0:Fin 3)
  constructor
  · simpa [input] using
      word_length_le_encode (![(List.replicate n true),(List.replicate s true),
        (List.replicate (count s n) true)]) (1:Fin 3)
  · simpa [input] using
      word_length_le_encode (![(List.replicate n true),(List.replicate s true),
        (List.replicate (count s n) true)]) (2:Fin 3)

theorem denominator_le (s n j : Nat) : denominator s n j ≤ 8*s*(n+s) := by
  have hv : vertexFlag s n j ≤ 1 := by unfold vertexFlag; split <;> omega
  have ha : auxiliaryFlag s n j ≤ 1 := by unfold auxiliaryFlag; split <;> omega
  unfold denominator auxiliaryCount
  have h0 : n*vertexFlag s n j ≤ n := by nlinarith
  have h1 : (s-3)*auxiliaryFlag s n j ≤ s := by nlinarith [Nat.sub_le s 3]
  nlinarith

theorem entry_input_length (s n j : Nat) (hj : j ≤ count s n) :
    (encode ![List.replicate j true,List.replicate (denominator s n j) true]).length+1 ≤
      40*((input s n).length+1)^2 := by
  obtain ⟨hn,hs,hc⟩:=input_lengths s n
  have hd:=denominator_le s n j
  rw [encode_length]
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,List.length_replicate]
  have hsn : s*(n+s) ≤ 2*((input s n).length)^2 := by
    have hmul:=Nat.mul_le_mul hs (show n+s ≤ 2*(input s n).length by omega)
    nlinarith
  nlinarith

theorem entry_length_polynomial : ∃ C d, ∀ s n (hs : 4 ≤ s) (hn : 0 < n) j,
    j<count s n →
    (CodeDTargetV2.alphabetEntry (j,((denominator s n j:Nat):ℚ)⁻¹)).length ≤
      C*((input s n).length+1)^d := by
  obtain ⟨C,d,h⟩:=physical_polynomial V40SeedProducer.entry
  refine ⟨C*40^d,2*d,?_⟩
  intro s n hs hn j hj
  have hd:=denominator_pos s n hs hn ⟨j,hj⟩
  let w:=encode ![List.replicate j true,List.replicate (denominator s n j) true]
  have he:=h w
  have hr:=V40SeedProducer.entry_result j (denominator s n j) hd
  have hl : (CodeDTargetV2.alphabetEntry (j,((denominator s n j:Nat):ℚ)⁻¹)).length ≤
      C*(w.length+1)^d := by
    change _+(V40SeedProducer.entry.result w).length ≤ _ at he
    rw [show V40SeedProducer.entry.result w=_ from hr] at he
    omega
  refine hl.trans ?_
  calc
    _ ≤ C*(40*((input s n).length+1)^2)^d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left (entry_input_length s n j (by omega)) d)
    _ = (C*40^d)*((input s n).length+1)^(2*d) := by rw [mul_pow,←pow_mul]; ring

theorem state_length_of_entries (s n j E : Nat) (hj : j ≤ count s n)
    (he : ∀ i<j, (CodeDTargetV2.alphabetEntry (i,((denominator s n i:Nat):ℚ)⁻¹)).length ≤ E) :
    (state s n j).length+1 ≤ 40*((input s n).length+1)*(E+1) := by
  obtain ⟨hn,hs,hc⟩:=input_lengths s n
  have ht := SourceListEncoding.totalLength_map_le (List.range j)
    (fun i => CodeDTargetV2.alphabetEntry (i,((denominator s n i:Nat):ℚ)⁻¹)) E
    (by intro i hi; exact he i (List.mem_range.mp hi))
  have hf:=SourceListEncoding.fields_length (entries s n j)
  have hnat:=EncodedGraph.natField_length_upper (count s n)
  change SourceListEncoding.totalLength (entries s n j) ≤ _ at ht
  simp only [List.length_range] at ht
  have hel : (entries s n j).length=j := by simp [entries]
  rw [hel] at hf
  have ha : (accumulator s n j).length ≤ 2*count s n+1+3*(j*E)+j := by
    simp only [accumulator,List.length_append]
    nlinarith
  rw [state,encode_length]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.succ_zero_eq_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ,List.length_replicate,Nat.add_zero]
  nlinarith

theorem state_length_polynomial : ∃ C d, ∀ s n (hs : 4 ≤ s) (hn : 0 < n) j,
    j ≤ count s n → (state s n j).length+1 ≤ C*((input s n).length+1)^d := by
  obtain ⟨C,d,h⟩:=entry_length_polynomial
  refine ⟨40*(C+1),d+1,?_⟩
  intro s n hs hn j hj
  have hz : 1 ≤ ((input s n).length+1)^d:=one_le_pow₀ (by omega)
  have hb:=state_length_of_entries s n j (C*((input s n).length+1)^d) hj
    (by intro i hi; exact h s n hs hn i (by omega))
  calc
    _ ≤ 40*((input s n).length+1)*(C*((input s n).length+1)^d+1):=hb
    _ ≤ (40*(C+1))*((input s n).length+1)^(d+1):=by rw [pow_succ]; nlinarith

#print axioms state_length_polynomial
#print axioms body_polynomial
end
end CurrentAdditive.V40IndexedLawPolynomial
