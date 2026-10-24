import CurrentAdditive.GaussConcreteGridPolynomialBound
import CurrentAdditive.GaussInitialByteDimensions

namespace CurrentAdditive.GaussConcreteGridInputBytes
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open EthInapproximability.CurrentPaper

theorem sum_finRange {n : Nat} (f : Fin n → Nat) :
    ((List.finRange n).map f).sum=∑ i,f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.finRange_succ,List.map_cons,List.map_map,List.sum_cons,
      Function.comp_def,Fin.sum_univ_succ]
    rw [ih]

theorem lengths_le_fields (words : List (List Bool)) :
    (words.map List.length).sum≤(SourceListEncoding.fields words).length := by
  induction words with
  | nil => simp [SourceListEncoding.fields]
  | cons word words ih =>
    simp only [List.map_cons,List.sum_cons,SourceListEncoding.fields,List.length_append]
    omega

theorem lengths_le_encode (words : List (List Bool)) :
    (words.map List.length).sum≤(SourceListEncoding.encode words).length := by
  have h := lengths_le_fields words
  simp only [SourceListEncoding.encode,List.length_append]
  omega

theorem cell_sum_le_matrix {m k : Nat} (B : Fin m → Fin k → ℚ) :
    (∑ i : Fin m,∑ j : Fin k,
      (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B i j))).length)≤
      (GaussPhysical.encodeTypedMatrix B).length := by
  have hc (i : Fin m) := lengths_le_encode (GaussTypedGetterBridge.cellWords B i)
  simp only [GaussTypedGetterBridge.cellWords,List.map_map,Function.comp_def,
    sum_finRange] at hc
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin m) (_ : i∈Finset.univ) => hc i)
  have ho := lengths_le_encode (GaussTypedGetterBridge.rowWords B)
  apply hs.trans
  rw [GaussTypedGetterBridge.encodeTypedMatrix_eq]
  simpa only [GaussTypedGetterBridge.rowWords,GaussTypedGetterBridge.cellWords,
    List.map_map,Function.comp_def,sum_finRange] using ho

/-- Every quantity used to bound the physical cell/row/grid execution is
bounded by the original serialized matrix, including the sum of all rational
cell bytes. The positive-row premise is forced by a typed pivot row. -/
theorem dataCap_le_bytes {m k : Nat} (B : Fin m → Fin k → ℚ) (hm : 0 < m) :
    GaussConcreteCellEntry.dataCap B≤4*(GaussPhysical.encodeTypedMatrix B).length+1 := by
  have hr := GaussInitialByteDimensions.rows_le_initial_bytes B
  have hc := GaussInitialByteDimensions.columns_le_initial_bytes B hm
  have hs := cell_sum_le_matrix B
  unfold GaussConcreteCellEntry.dataCap
  omega

theorem dataCap_bound {m k : Nat} (B : Fin m → Fin k → ℚ) (hm : 0 < m) :
    GaussConcreteCellEntry.dataCap B+1≤4*((GaussPhysical.encodeTypedMatrix B).length+1) := by
  have h := dataCap_le_bytes B hm
  omega

/-- The same fixed grid instruction table has a polynomial bound in the
original matrix bytes. Constants are selected before every matrix, dimension,
pivot, and cursor. No intermediate bank-size or output-size premise remains. -/
theorem uniform_grid_original_bytes : ∃ C e : Nat,
    ∀ {m k : Nat} (B : Fin m → Fin k → ℚ)
      (r pivot : Fin m) (c : Fin k), B pivot c≠0 →
    ∃ t≤C*((GaussPhysical.encodeTypedMatrix B).length+1)^e,
      ∃ v : GaussConcreteGrid.Control,
      ((BitMachineEncoding.advance GaussConcreteGrid.program)^[t])
        (⟨some GaussConcreteGrid.start,GaussConcreteGrid.control,
          (GaussConcreteGrid.initialData B r pivot c).contents⟩ :
            Turing.TM2.Cfg (fun _ : GaussConcreteGrid.Stack => Bool)
              GaussConcreteGrid.Label GaussConcreteGrid.Control) =
        ⟨none,v,Function.update (GaussConcreteGrid.initialData B r pivot c).contents
          (.inr .output) (GaussPhysical.encodeTypedMatrix
            (SequentialTotality.clearTyped (SequentialTotality.swapTyped B r pivot) r c))⟩ := by
  obtain ⟨C,e,hC⟩ := GaussConcreteGridPolynomialBound.uniform_physical_grid
  refine ⟨C*4^e,e,?_⟩
  intro m k B r pivot c hn
  obtain ⟨t,ht,v,he⟩ := hC B r pivot c hn
  have hb := Nat.pow_le_pow_left (dataCap_bound B (by have h:=r.isLt; omega)) e
  have hp : C*(GaussConcreteCellEntry.dataCap B+1)^e≤
      (C*4^e)*((GaussPhysical.encodeTypedMatrix B).length+1)^e := by
    calc
      _ ≤ C*(4*((GaussPhysical.encodeTypedMatrix B).length+1))^e := Nat.mul_le_mul_left C hb
      _ = _ := by rw [mul_pow]; ring
  exact ⟨t,ht.trans hp,v,he⟩

#print axioms cell_sum_le_matrix
#print axioms uniform_grid_original_bytes
end
end CurrentAdditive.GaussConcreteGridInputBytes
