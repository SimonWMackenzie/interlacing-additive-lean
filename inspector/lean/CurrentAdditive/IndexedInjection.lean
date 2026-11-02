import CurrentAdditive.IndexedConstructor

namespace CurrentAdditive.IndexedLaw

open SequentialCode SequentialSourceCode SequentialFeatureCoverage IndependentSupport
  SequentialArrayBridge SequentialCompressionTotality

theorem independent_source_word_injective {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (out : Array (α × ℚ)) (hn : 0 < n)
    (hind : ColumnIndependent (featureRows n φ out)) :
    Function.Injective (fun j : Fin out.size => out[j].1) := by
  have hcount : columnCount (featureRows n φ out) = out.size :=
    featureRows_columnCount n φ out hn
  have hli := (columnIndependent_iff_linearIndependent (featureRows n φ out)).mp hind
  intro j k heq
  let j' : Fin (columnCount (featureRows n φ out)) := ⟨j.val, by omega⟩
  let k' : Fin (columnCount (featureRows n φ out)) := ⟨k.val, by omega⟩
  have hcol : (fun i : Fin (featureRows n φ out).size =>
        matrixOfArray (featureRows n φ out) i j') =
      (fun i : Fin (featureRows n φ out).size =>
        matrixOfArray (featureRows n φ out) i k') := by
    funext i
    have hi : i.val < n := by simpa [featureRows] using i.isLt
    have heq' : out[j.val].1 = out[k.val].1 := by
      simpa only [Fin.getElem_fin] using heq
    simp [matrixOfArray, cell, featureRows, j', k', j.isLt, k.isLt, hi, heq']
  have hjk := hli.injective hcol
  apply Fin.ext
  exact congrArg (fun x : Fin (columnCount (featureRows n φ out)) => x.val) hjk

/-- Different retained source labels are different original index tuples.
They may still decode to the same tuple of application-level values. -/
theorem construct_word_injective {m : Nat} (D : Nat) (μ : Fin m → ℚ)
    (q : Nat) :
    Function.Injective (fun j : Fin (construct D μ q).size =>
      (construct D μ q)[j].1) := by
  cases q with
  | zero =>
      have hout : construct D μ 0 = #[(Fin.elim0, 1)] := by
        simp [construct, LabelTrace.sequentialPreprocessed, sequentialIndependent]
      intro i j _
      apply Fin.ext
      have hsize : (construct D μ 0).size = 1 := by rw [hout]; rfl
      have hi : i.val < 1 := lt_of_lt_of_eq i.isLt hsize
      have hj : j.val < 1 := lt_of_lt_of_eq j.isLt hsize
      omega
  | succ q =>
      exact independent_source_word_injective _ _ _
        (generatedFeatures_pos _ _ _)
        (construct_independent D μ q)

theorem decode_injective {m : Nat} (D : Nat) (μ : Fin m → ℚ)
    (hmass : ∑ i, μ i = 1) (q : Nat) :
    Function.Injective (decode D μ hmass q) := by
  intro j k heq
  apply construct_word_injective D μ q
  funext i
  have h := congrArg (fun w : Fin q → Fin m => (w i).val) heq
  exact h

def tupleEmbedding {m : Nat} (D : Nat) (μ : Fin m → ℚ)
    (hmass : ∑ i, μ i = 1) (q : Nat) :
    Fin (construct D μ q).size ↪ (Fin q → Fin m) where
  toFun := decode D μ hmass q
  inj' := decode_injective D μ hmass q

end CurrentAdditive.IndexedLaw
