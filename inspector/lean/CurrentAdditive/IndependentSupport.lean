import CurrentAdditive.SequentialFeatureCoverage
import CurrentAdditive.SequentialDimensionPolynomialProduction

namespace CurrentAdditive.IndependentSupport
open SequentialTotality MaterializedGauss SequentialCode SequentialArrayBridge
  SequentialSourceCode SequentialFeatureCoverage SequentialAppendMoments

private theorem no_free_has_pivot {m k : Nat}
    (ps : List (Fin m × Fin k))
    (h : typedFree ps = none) (j : Fin k) :
    j ∈ ps.map Prod.snd := by
  have hn := List.find?_eq_none.mp h j (List.mem_finRange j)
  simpa [typedFree] using hn

private theorem pivot_columns_kernel_zero {m k : Nat}
    (B : Fin m → Fin k → ℚ) (ps : List (Fin m × Fin k))
    (hcover : ∀ j : Fin k, j ∈ ps.map Prod.snd)
    (hunit : ∀ p ∈ ps, ∀ i : Fin m,
      B i p.2 = if i = p.1 then 1 else 0)
    (hnodup : (ps.map Prod.fst).Nodup)
    (x : Fin k → ℚ) (hkernel : ∀ i, rowDot B x i = 0) :
    ∀ j, x j = 0 := by
  have hpsnodup : ps.Nodup := hnodup.of_map
  have hinj := (List.nodup_map_iff_inj_on hpsnodup).mp hnodup
  intro j
  obtain ⟨p, hp, hpj⟩ := List.mem_map.mp (hcover j)
  have hcol : ∀ i : Fin k, B p.1 i = if i = j then 1 else 0 := by
    intro i
    by_cases hij : i = j
    · subst i
      simpa [hpj] using hunit p hp p.1
    · obtain ⟨q, hq, hqi⟩ := List.mem_map.mp (hcover i)
      have hrow : p.1 ≠ q.1 := by
        intro heq
        have hpq : p = q := hinj p hp q hq heq
        apply hij
        calc
          i = q.2 := hqi.symm
          _ = p.2 := by rw [hpq]
          _ = j := hpj
      simpa [hqi, hij, hrow] using hunit q hq p.1
  have hz := hkernel p.1
  simp [rowDot, hcol] at hz
  exact hz

private theorem materialized_no_free_kernel_zero {m k : Nat}
    (A : Fin m → Fin k → ℚ)
    (hfree : typedFree (echelonTyped A 0 0 k).2 = none)
    (x : Fin k → ℚ) (hkernel : ∀ i, rowDot A x i = 0) :
    ∀ j, x j = 0 := by
  let out := echelonTyped A 0 0 k
  have hbelow : BelowZero A 0 0 := by
    intro i j _ hj
    omega
  have hunit := echelonTyped_pivot_units A 0 0 k (by simp) hbelow
  have hnodup := echelonTyped_pivot_rows_nodup A 0 0 k
  have hkernelOut := (echelonTyped_kernel_iff A 0 0 k x).mpr hkernel
  exact pivot_columns_kernel_zero out.1 out.2
    (fun j => no_free_has_pivot out.2 hfree j)
    hunit hnodup x hkernelOut

/-- A free column suffices for the existing deterministic Gauss candidate,
even when the matrix has no more columns than rows. -/
theorem typedDependence_total_of_free {m k : Nat}
    (A : Fin m → Fin k → ℚ) (f : Fin k)
    (hf : typedFree (echelonTyped A 0 0 k).2 = some f) :
    ∃ x, typedDependence A = some x ∧
      (∃ j : Fin k, x j ≠ 0) ∧
      ∀ i, rowDot A x i = 0 := by
  let B := (echelonTyped A 0 0 k).1
  let ps := (echelonTyped A 0 0 k).2
  have hfree := typedFree_spec ps f hf
  have hbelow : BelowZero A 0 0 := by
    intro i j _ hj
    omega
  have hstair := (echelonTyped_staircase A 0 0 k (by simp) hbelow).1
  have hunit := echelonTyped_pivot_units A 0 0 k (by simp) hbelow
  have hrows := echelonTyped_pivot_rows A 0 0 k (by omega)
  have hnodup := echelonTyped_pivot_rows_nodup A 0 0 k
  have hred : typedCandidate B ps f f ≠ 0 ∧
      ∀ i, rowDot B (typedCandidate B ps f) i = 0 := by
    apply typedCandidate_reduced_kernel B ps f hfree
    · simpa [B, ps] using hunit
    · intro i hi j
      exact hstair i j (by simpa [ps] using hi) (by omega)
    · intro i hi
      have h := hrows.2 i (by omega) (by simpa [ps] using hi)
      simpa [ps] using h
    · simpa [ps] using hnodup
  refine ⟨typedCandidate B ps f, ?_, ⟨f, hred.1⟩, ?_⟩
  · simp [typedDependence, B, ps, hf]
  · exact (echelonTyped_kernel_iff A 0 0 k (typedCandidate B ps f)).mp hred.2

/-- The relation produced by a free column uses only that column and the
recorded pivot columns. There are at most `m` pivots, so this is the exact
`basis plus one` shape required by the manuscript, before coefficient bounds. -/
theorem typedCandidate_support_basis_plus_one {m k : Nat}
    (B : Fin m → Fin k → ℚ)
    (ps : List (Fin m × Fin k)) (f j : Fin k)
    (hjf : j ≠ f) (hjp : j ∉ ps.map Prod.snd) :
    typedCandidate B ps f j = 0 := by
  unfold typedCandidate
  have hsum : (∑ p ∈ ps.toFinset,
      if j = p.2 then B p.1 f else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hpmem : p ∈ ps := by simpa using hp
    have hne : j ≠ p.2 := by
      intro heq
      apply hjp
      exact List.mem_map.mpr ⟨p, hpmem, heq.symm⟩
    simp [hne]
  simp [hjf, hsum]

theorem echelon_pivot_count_le_rows {m k : Nat}
    (A : Fin m → Fin k → ℚ) :
    (echelonTyped A 0 0 k).2.length ≤ m := by
  simpa using (echelonTyped_pivot_rows A 0 0 k (by omega)).1

def LabelsRetained {α : Type*}
    (before after : Array (α × ℚ)) : Prop :=
  ∀ entry ∈ after, ∃ old ∈ before, old.1 = entry.1

private theorem selectedSource_labels {α : Type*}
    (source : Array (α × ℚ)) (updated : Array ℚ)
    (indices : List Nat) :
    LabelsRetained source
      ((indices.filterMap (fun i =>
        (source[i]?).map (fun entry => (entry.1, updated[i]?.getD 0)))).toArray) := by
  intro entry hentry
  have hm : entry ∈ indices.filterMap (fun i =>
      (source[i]?).map (fun old => (old.1, updated[i]?.getD 0))) := by
    simpa [Array.mem_def] using hentry
  obtain ⟨i, hi, hmap⟩ := List.mem_filterMap.mp hm
  cases hx : source[i]? with
  | none => simp [hx] at hmap
  | some old =>
      have hbound : i < source.size := by
        by_contra hnot
        have hnone : source[i]? = none := by simp [Nat.not_lt.mp hnot]
        rw [hnone] at hx
        cases hx
      have hget : source[i] = old := by simpa [hbound] using hx
      have hold : old ∈ source :=
        (Array.mem_iff_getElem).2 ⟨i, hbound, hget⟩
      refine ⟨old, hold, ?_⟩
      have heq : (old.1, updated[i]?.getD 0) = entry := by
        simpa [hx] using hmap
      cases heq
      rfl

theorem compressSourceOnce_labels {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ))
    (h : SequentialSourceCode.compressSourceOnceMaterialized n φ source = some out) :
    LabelsRetained source out := by
  unfold SequentialSourceCode.compressSourceOnceMaterialized at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · split at h
          · cases h
            exact selectedSource_labels source _ _
          · cases h
        · cases h
      · cases h

private theorem listRangeSum (n : Nat) (g : Nat → ℚ) :
    ((List.range n).map g).sum = ∑ j ∈ Finset.range n, g j := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- A free Gauss column yields a checked array certificate at every size. -/
theorem certifiedMaterializedDependence_total_of_free
    (a : Array (Array ℚ)) (f : Fin (columnCount a))
    (hf : typedFree
      (echelonTyped (matrixOfArray a) 0 0 (columnCount a)).2 = some f) :
    ∃ cert, certifiedMaterializedDependence a = some cert := by
  obtain ⟨v, hv, ⟨j, hj⟩, hkernel⟩ :=
    typedDependence_total_of_free (matrixOfArray a) f hf
  let x := Array.ofFn v
  have htyped : typedArrayDependence a = some x := by
    simp [typedArrayDependence, x, hv]
  have hsize : x.size = columnCount a := by simp [x]
  have hnonzero : ∃ j ∈ List.range x.size, x[j]?.getD 0 ≠ 0 := by
    refine ⟨j.val, ?_, ?_⟩
    · simpa [x] using (List.mem_range.mpr j.isLt)
    · simpa [x] using hj
  have hrows : ∀ i ∈ List.range a.size,
      ((List.range x.size).map
        (fun j => cell a i j * (x[j]?.getD 0))).sum = 0 := by
    intro i hi
    let fi : Fin a.size := ⟨i, List.mem_range.mp hi⟩
    have hz := hkernel fi
    dsimp only [x] at *
    simp only [Array.size_ofFn] at *
    change ((List.range (columnCount a)).map
      (fun j => cell a i j * ((Array.ofFn v)[j]?.getD 0))).sum = 0
    rw [listRangeSum]
    unfold rowDot matrixOfArray at hz
    rw [Finset.sum_fin_eq_sum_range] at hz
    dsimp [fi] at hz
    calc
      (∑ j ∈ Finset.range (columnCount a),
          cell a i j * ((Array.ofFn v)[j]?.getD 0)) =
          ∑ j ∈ Finset.range (columnCount a),
            (if h : j < columnCount a then cell a i j * v ⟨j, h⟩ else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              have hjk := Finset.mem_range.mp hj
              simp [hjk]
      _ = 0 := hz
  have hcheck : dependenceCheck a x = true :=
    (dependence_spec a x).2 ⟨hsize, hnonzero, hrows⟩
  refine ⟨⟨x, hcheck⟩, ?_⟩
  simpa [certifiedMaterializedDependence_eq,
    certifiedTypedDependence, htyped, hcheck]

/-- Semantic independence of the actual rational feature columns. -/
def ColumnIndependent (a : Array (Array ℚ)) : Prop :=
  ∀ x : Fin (columnCount a) → ℚ,
    (∀ i, rowDot (matrixOfArray a) x i = 0) → ∀ j, x j = 0

theorem columnIndependent_iff_linearIndependent
    (a : Array (Array ℚ)) :
    ColumnIndependent a ↔
      LinearIndependent ℚ (fun j : Fin (columnCount a) =>
        fun i : Fin a.size => matrixOfArray a i j) := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h x hx
    apply h x
    intro i
    have hi := congrArg (fun f : Fin a.size → ℚ => f i) hx
    simpa [rowDot, Finset.sum_apply, mul_comm] using hi
  · intro h x hx
    apply h x
    funext i
    simpa [rowDot, Finset.sum_apply, mul_comm] using hx i

/-- The first-free-column scan is a complete finite independence test. -/
theorem no_free_column_independent (a : Array (Array ℚ))
    (hfree : typedFree
      (echelonTyped (matrixOfArray a) 0 0 (columnCount a)).2 = none) :
    ColumnIndependent a := by
  intro x hx
  exact materialized_no_free_kernel_zero (matrixOfArray a) hfree x hx

theorem no_free_column_size_le (a : Array (Array ℚ))
    (hfree : typedFree
      (echelonTyped (matrixOfArray a) 0 0 (columnCount a)).2 = none) :
    columnCount a ≤ a.size := by
  by_contra hgt
  have hmore : a.size < columnCount a := by omega
  obtain ⟨f, hf⟩ := typedFree_exists
    (echelonTyped (matrixOfArray a) 0 0 (columnCount a)).2
    (echelonTyped_free_column (matrixOfArray a) hmore)
  rw [hfree] at hf
  cases hf

/-- The executable free-column scan on the current, retained support. -/
def sourceFreeColumn {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) :
    Option (Fin (columnCount (featureRows n φ source))) :=
  typedFree (echelonMaterialized
    (matrixOfArray (featureRows n φ source)) 0 0
    (columnCount (featureRows n φ source))).2

theorem sourceFreeColumn_some_certificate {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (f)
    (hf : sourceFreeColumn n φ source = some f) :
    ∃ cert, certifiedMaterializedDependence (featureRows n φ source) = some cert := by
  apply certifiedMaterializedDependence_total_of_free _ f
  simpa [sourceFreeColumn, echelonMaterialized_eq] using hf

theorem sourceFreeColumn_none_independent {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ))
    (hf : sourceFreeColumn n φ source = none) :
    ColumnIndependent (featureRows n φ source) := by
  apply no_free_column_independent
  simpa [sourceFreeColumn, echelonMaterialized_eq] using hf

theorem sourceFreeColumn_none_size_le {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (hn : 0 < n)
    (hf : sourceFreeColumn n φ source = none) :
    source.size ≤ n := by
  have hf' : typedFree
      (echelonTyped
        (matrixOfArray (featureRows n φ source)) 0 0
        (columnCount (featureRows n φ source))).2 = none := by
    simpa [sourceFreeColumn, echelonMaterialized_eq] using hf
  have hbound := no_free_column_size_le (featureRows n φ source) hf'
  rw [SequentialCompressionTotality.featureRows_columnCount n φ source hn] at hbound
  simpa [featureRows] using hbound

/-- The old checked elimination step is total whenever the new scan finds
a dependence, including below the feature-count threshold. -/
theorem compressSourceOnce_total_of_free {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ))
    (hn : 0 < n)
    (hconstant : ∃ j : Fin n, ∀ x, φ x j = 1)
    (hfree : ∃ f, sourceFreeColumn n φ source = some f)
    (hpositive : SequentialSourceCode.SourcePositive source) :
    ∃ out, SequentialSourceCode.compressSourceOnceMaterialized n φ source = some out := by
  let matrix := featureRows n φ source
  let weights := source.map Prod.snd
  obtain ⟨f, hf⟩ := hfree
  obtain ⟨cert, hcert⟩ := sourceFreeColumn_some_certificate n φ source f hf
  have hsize : weights.size = columnCount matrix := by
    simp [weights, matrix, SequentialCompressionTotality.featureRows_columnCount n φ source hn]
  have hweights : weights.all (fun w => decide (0 < w)) = true :=
    SequentialSourceCode.sourcePositive_weights source hpositive
  have hw : ∀ i < weights.size, 0 < weights[i]?.getD 0 := by
    intro i hi
    have hp := (Array.all_eq_true.mp hweights) i hi
    simpa [hi] using hp
  have hsum : cert.val.toList.sum = 0 :=
    SequentialElimination.zero_sum_of_constant_row matrix cert.val
      cert.property (by simpa [matrix] using
        SequentialSourceCode.featureRows_constant_row n φ source hconstant)
  obtain ⟨updated, hupdated, hupdatedsize, hnonneg, hsame, hshrink⟩ :=
    SequentialElimination.eliminateWeights_total matrix weights cert.val
      hsize hw cert.property hsum
  let indices := SequentialCode.positiveIndices updated
  let out := (indices.filterMap (fun i =>
    (source[i]?).map (fun entry => (entry.1, updated[i]?.getD 0)))).toArray
  have hsourcecheck : sourceMomentsCheck n φ source out = true := by
    exact SequentialZeroDeletion.sourceMomentsCheck_after_positiveIndices
      n φ source updated hnonneg (by simpa [matrix, weights] using hsame)
  refine ⟨out, ?_⟩
  simp [SequentialSourceCode.compressSourceOnceMaterialized, matrix, weights,
    hcert, hupdated, hnonneg, hsame,
    hsourcecheck, indices, out]
  constructor
  · intro i hi
    simpa using (Array.all_eq_true.mp hpositive) i hi
  · simpa [weights] using hshrink

/-- Literal finite support-elimination loop. It stops on a Gauss independence
certificate, rather than merely when support size reaches feature count. -/
def compressUntilIndependent {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (fuel : Nat) :
    Option (Array (α × ℚ)) :=
  match fuel with
  | 0 =>
    match sourceFreeColumn n φ source with
    | none => some source
    | some _ => none
  | fuel + 1 =>
    match sourceFreeColumn n φ source with
    | none => some source
    | some _ => do
      let next ← SequentialSourceCode.compressSourceOnceMaterialized n φ source
      compressUntilIndependent n φ next fuel

theorem compressUntilIndependent_independent {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel : Nat)
    (h : compressUntilIndependent n φ source fuel = some out) :
    ColumnIndependent (featureRows n φ out) := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [hf] at h
          cases h
          exact sourceFreeColumn_none_independent n φ out hf
      | some f => simp [hf] at h
  | succ fuel ih =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [hf] at h
          cases h
          exact sourceFreeColumn_none_independent n φ out hf
      | some f =>
          cases hs : SequentialSourceCode.compressSourceOnceMaterialized n φ source with
          | none => simp [hf, hs] at h
          | some next =>
              simp [hf, hs] at h
              exact ih next h

theorem compressUntilIndependent_size_le {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel : Nat) (hn : 0 < n)
    (h : compressUntilIndependent n φ source fuel = some out) :
    out.size ≤ n := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [hf] at h
          cases h
          exact sourceFreeColumn_none_size_le n φ out hn hf
      | some f => simp [hf] at h
  | succ fuel ih =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [hf] at h
          cases h
          exact sourceFreeColumn_none_size_le n φ out hn hf
      | some f =>
          cases hs : SequentialSourceCode.compressSourceOnceMaterialized n φ source with
          | none => simp [hf, hs] at h
          | some next =>
              simp [hf, hs] at h
              exact ih next h

theorem compressUntilIndependent_moments {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel : Nat)
    (h : compressUntilIndependent n φ source fuel = some out) :
    sourceMass source = sourceMass out ∧
      ∀ j : Fin n, sourceMoment φ source j = sourceMoment φ out j := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none => simp [hf] at h; cases h; exact ⟨rfl, fun _ => rfl⟩
      | some f => simp [hf] at h
  | succ fuel ih =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none => simp [hf] at h; cases h; exact ⟨rfl, fun _ => rfl⟩
      | some f =>
          cases hs : SequentialSourceCode.compressSourceOnceMaterialized n φ source with
          | none => simp [hf, hs] at h
          | some next =>
              simp [hf, hs] at h
              have hfirst := SequentialSourceCode.compressSourceOnceMaterialized_moments
                n φ source next hs
              have hrest := ih next h
              exact ⟨hfirst.1.trans hrest.1,
                fun j => (hfirst.2 j).trans (hrest.2 j)⟩

theorem compressUntilIndependent_positive {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel : Nat)
    (hpositive : SequentialSourceCode.SourcePositive source)
    (h : compressUntilIndependent n φ source fuel = some out) :
    SequentialSourceCode.SourcePositive out := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none => simp [hf] at h; cases h; exact hpositive
      | some f => simp [hf] at h
  | succ fuel ih =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none => simp [hf] at h; cases h; exact hpositive
      | some f =>
          cases hs : SequentialSourceCode.compressSourceOnceMaterialized n φ source with
          | none => simp [hf, hs] at h
          | some next =>
              simp [hf, hs] at h
              have hnext := SequentialSourceCode.compressSourceOnceMaterialized_positive
                n φ source next hs
              exact ih next hnext h

theorem compressUntilIndependent_labels {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel : Nat)
    (h : compressUntilIndependent n φ source fuel = some out) :
    LabelsRetained source out := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [hf] at h
          cases h
          intro entry he
          exact ⟨entry, he, rfl⟩
      | some f => simp [hf] at h
  | succ fuel ih =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [hf] at h
          cases h
          intro entry he
          exact ⟨entry, he, rfl⟩
      | some f =>
          cases hs : SequentialSourceCode.compressSourceOnceMaterialized n φ source with
          | none => simp [hf, hs] at h
          | some next =>
              simp [hf, hs] at h
              have hfirst := compressSourceOnce_labels n φ source next hs
              have hrest := ih next h
              intro entry he
              obtain ⟨mid, hmid, hmidlabel⟩ := hrest entry he
              obtain ⟨old, hold, holdlabel⟩ := hfirst mid hmid
              exact ⟨old, hold, holdlabel.trans hmidlabel⟩

/-- Source-size fuel suffices because every dependent step strictly removes
at least one positive-weight position. -/
theorem compressUntilIndependent_total {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n)
    (hconstant : ∃ j : Fin n, ∀ x, φ x j = 1)
    (source : Array (α × ℚ))
    (hpositive : SequentialSourceCode.SourcePositive source)
    (fuel : Nat) (hfuel : source.size ≤ fuel) :
    ∃ out, compressUntilIndependent n φ source fuel = some out := by
  induction fuel generalizing source with
  | zero =>
      have hsourceEmpty : source.size = 0 := by omega
      have hcolumns : columnCount (featureRows n φ source) = 0 := by
        simpa [hsourceEmpty] using
          SequentialCompressionTotality.featureRows_columnCount n φ source hn
      cases hf : sourceFreeColumn n φ source with
      | none => exact ⟨source, by simp [compressUntilIndependent, hf]⟩
      | some f =>
          have f0 : Fin 0 := hcolumns ▸ f
          exact Fin.elim0 f0
  | succ fuel ih =>
      cases hf : sourceFreeColumn n φ source with
      | none => exact ⟨source, by simp [compressUntilIndependent, hf]⟩
      | some f =>
          obtain ⟨next, hnext⟩ := compressSourceOnce_total_of_free n φ source
            hn hconstant ⟨f, hf⟩ hpositive
          have hsmaller := SequentialSourceCode.compressSourceOnceMaterialized_size_lt
            n φ source next hnext
          have hnextpos := SequentialSourceCode.compressSourceOnceMaterialized_positive
            n φ source next hnext
          obtain ⟨out, hout⟩ := ih next hnextpos (by omega)
          exact ⟨out, by simp [compressUntilIndependent, hf, hnext, hout]⟩

/-- The stagewise Code D constructor with the manuscript's literal stopping
condition at each appended coordinate. -/
def sequentialIndependent {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) :
    (q : Nat) → Option (Array ((Fin q → Y) × ℚ))
  | 0 => some #[(Fin.elim0, 1)]
  | q + 1 => do
      let prev ← sequentialIndependent D alphabet q
      let extended := appendSource prev alphabet
      let featuresAt := generatedFeatures (q + 1) D (alphabet.map Prod.fst)
      let n := featuresAt.size
      let features : (Fin (q + 1) → Y) → Fin n → ℚ :=
        fun v j => generatedFeatureValue v featuresAt[j]
      compressUntilIndependent n features extended extended.size

theorem sequentialIndependent_total {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabet : SourcePositive alphabet) :
    ∀ q, ∃ out, sequentialIndependent D alphabet q = some out ∧
      SourcePositive out := by
  intro q
  induction q with
  | zero =>
      refine ⟨#[(Fin.elim0, 1)], ?_, ?_⟩
      · rfl
      · simp [SourcePositive]
  | succ q ih =>
      obtain ⟨prev, hprev, hprevpos⟩ := ih
      let extended := appendSource prev alphabet
      let featuresAt := generatedFeatures (q + 1) D (alphabet.map Prod.fst)
      let n := featuresAt.size
      let features : (Fin (q + 1) → Y) → Fin n → ℚ :=
        fun v j => generatedFeatureValue v featuresAt[j]
      have hextended : SourcePositive extended :=
        appendSource_positive prev alphabet hprevpos halphabet
      have hn : 0 < n := generatedFeatures_pos (q + 1) D (alphabet.map Prod.fst)
      have hconstant : ∃ j : Fin n, ∀ x, features x j = 1 := by
        simpa [features, n, featuresAt] using
          (generatedFeatures_constant (q + 1) D (alphabet.map Prod.fst))
      obtain ⟨out, hout⟩ :=
        compressUntilIndependent_total n features hn hconstant
          extended hextended extended.size (Nat.le_refl _)
      refine ⟨out, ?_, ?_⟩
      · simpa [sequentialIndependent, hprev, extended, featuresAt, n, features]
          using hout
      · exact compressUntilIndependent_positive n features extended out
          extended.size hextended hout

theorem sequentialIndependent_mass {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabet : sourceMass alphabet = 1) :
    ∀ q out, sequentialIndependent D alphabet q = some out →
      sourceMass out = 1 := by
  intro q
  induction q with
  | zero =>
      intro out hout
      simp only [sequentialIndependent] at hout
      cases hout
      simp [sourceMass]
  | succ q ih =>
      intro out hout
      simp only [sequentialIndependent] at hout
      cases hprev : sequentialIndependent D alphabet q with
      | none => simp [hprev] at hout
      | some prev =>
          simp [hprev] at hout
          have hm := compressUntilIndependent_moments _ _ _ _ _ hout
          rw [← hm.1, sourceMass_appendSource, ih prev hprev, halphabet]
          ring

theorem sequentialIndependent_size_le_features {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (q : Nat) (out : Array ((Fin (q + 1) → Y) × ℚ))
    (h : sequentialIndependent D alphabet (q + 1) = some out) :
    out.size ≤ (generatedFeatures (q + 1) D
      (alphabet.map Prod.fst)).size := by
  simp only [sequentialIndependent] at h
  cases hprev : sequentialIndependent D alphabet q with
  | none => simp [hprev] at h
  | some prev =>
      simp [hprev] at h
      exact compressUntilIndependent_size_le _ _ _ _ _
        (generatedFeatures_pos (q + 1) D (alphabet.map Prod.fst)) h

theorem sequentialIndependent_stage_labels {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (q : Nat) (prev : Array ((Fin q → Y) × ℚ))
    (out : Array ((Fin (q + 1) → Y) × ℚ))
    (hprev : sequentialIndependent D alphabet q = some prev)
    (h : sequentialIndependent D alphabet (q + 1) = some out) :
    LabelsRetained (appendSource prev alphabet) out := by
  simp only [sequentialIndependent] at h
  simp [hprev] at h
  exact compressUntilIndependent_labels _ _ _ _ _ h

theorem sequentialIndependent_columns_independent {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (q : Nat) (out : Array ((Fin (q + 1) → Y) × ℚ))
    (h : sequentialIndependent D alphabet (q + 1) = some out) :
    ColumnIndependent (featureRows
      (generatedFeatures (q + 1) D (alphabet.map Prod.fst)).size
      (fun v j => generatedFeatureValue v
        (generatedFeatures (q + 1) D (alphabet.map Prod.fst))[j]) out) := by
  simp only [sequentialIndependent] at h
  cases hprev : sequentialIndependent D alphabet q with
  | none => simp [hprev] at h
  | some prev =>
      simp [hprev] at h
      exact compressUntilIndependent_independent _ _ _ _ _ h

theorem compression_preserves_generated_feature {Y : Type*}
    [DecidableEq Y] {q D : Nat} (alphabet : Array Y)
    (source out : Array ((Fin q → Y) × ℚ))
    (hcompress :
      compressUntilIndependent
        (generatedFeatures q D alphabet).size
        (fun v j => generatedFeatureValue v
          (generatedFeatures q D alphabet)[j])
        source source.size = some out)
    (c : List (Nat × Y))
    (hc : c ∈ (generatedFeatures q D alphabet).toList) :
    weightedSum source (fun v => generatedFeatureValue v c) =
      weightedSum out (fun v => generatedFeatureValue v c) := by
  let F := generatedFeatures q D alphabet
  have hmem : c ∈ F := by simpa [F] using hc
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hmem
  let j : Fin F.size := ⟨i, hi⟩
  have hm := (compressUntilIndependent_moments
    F.size (fun v j => generatedFeatureValue v F[j])
      source out source.size (by simpa [F] using hcompress)).2 j
  simpa [sourceMoment_eq_weightedSum, F, j, hget] using hm

theorem sequentialIndependent_generated_moments {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabet : sourceMass alphabet = 1) :
    ∀ q out, sequentialIndependent D alphabet q = some out →
      ∀ c ∈ (generatedFeatures q D (alphabet.map Prod.fst)).toList,
        weightedSum out (fun v => generatedFeatureValue v c) =
          featureTarget alphabet c := by
  intro q
  induction q with
  | zero =>
      intro out hout c hc
      simp only [sequentialIndependent] at hout
      cases hout
      simp [generatedFeatures] at hc
      rcases hc with rfl
      simp [weightedSum, generatedFeatureValue, featureTarget]
  | succ q ih =>
      intro out hout c hc
      simp only [sequentialIndependent] at hout
      cases hprev : sequentialIndependent D alphabet q with
      | none => simp [hprev] at hout
      | some prev =>
          simp [hprev] at hout
          let A := alphabet.map Prod.fst
          let oldFeatures := generatedFeatures q D A
          let newFeatures := generatedFeatures (q + 1) D A
          let extended := appendSource prev alphabet
          have hcase : c ∈ oldFeatures.toList ∨
              ∃ old ∈ oldFeatures.toList, old.length < D ∧
                ∃ y ∈ A.toList, c = (q, y) :: old := by
            rw [generatedFeatures_succ] at hc
            exact extendFeatures_mem_cases q D A oldFeatures c
              (by simpa [newFeatures, oldFeatures, A] using hc)
          have hbefore : weightedSum extended
              (fun v => generatedFeatureValue v c) =
              featureTarget alphabet c := by
            rcases hcase with hold | ⟨old, hold, hlength, y, hy, rfl⟩
            · rw [weightedSum_append_old_feature prev alphabet c
                (by exact generatedFeatures_valid q D A c hold) halphabet]
              exact ih prev hprev c (by simpa [A] using hold)
            · rw [weightedSum_append_new_feature prev alphabet old
                (by exact generatedFeatures_valid q D A old hold) y]
              rw [ih prev hprev old (by simpa [A] using hold)]
              simp [featureTarget_cons, alphabetPointMass]
              ring
          have hpreserve : weightedSum extended
              (fun v => generatedFeatureValue v c) =
              weightedSum out (fun v => generatedFeatureValue v c) := by
            apply compression_preserves_generated_feature A extended out
            · simpa [A, extended, newFeatures] using hout
            · simpa [A] using hc
          exact hpreserve.symm.trans hbefore

theorem sequentialIndependent_pattern_moment {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabet : sourceMass alphabet = 1)
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hout : sequentialIndependent D alphabet q = some out)
    (p : Fin q → Option Y)
    [∀ v : Fin q → Y, Decidable (PatternMatches p v)]
    (hvalues : ∀ i y, p i = some y →
      y ∈ (alphabet.map Prod.fst).toList)
    (hsize : patternSize p ≤ D) :
    weightedSum out (fun v => if PatternMatches p v then 1 else 0) =
      patternTarget alphabet p := by
  classical
  let c := patternFeature q p
  have hlength : c.length ≤ D := by
    rw [show c.length = patternSize p from
      patternFeature_length_eq_size q p]
    exact hsize
  have hmem := patternFeature_mem_generated D
    (alphabet.map Prod.fst) q p hvalues hlength
  calc
    weightedSum out (fun v => if PatternMatches p v then 1 else 0) =
        weightedSum out (fun v => generatedFeatureValue v c) := by
          congr 1
          funext v
          exact (patternFeature_indicator q p v).symm
    _ = featureTarget alphabet c :=
      sequentialIndependent_generated_moments D alphabet halphabet
        q out hout c hmem
    _ = patternTarget alphabet p := featureTarget_patternFeature alphabet q p

theorem sequentialIndependent_size_polynomial {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (q : Nat) (out : Array ((Fin (q + 1) → Y) × ℚ))
    (h : sequentialIndependent D alphabet (q + 1) = some out) :
    out.size ≤ (1 + (q + 1) * alphabet.size) ^ D := by
  have hfeature :=
    SequentialDimensionPolynomialProduction.generatedFeatures_size_le_polynomial
      (q + 1) D (alphabet.map Prod.fst)
  have hbound : (generatedFeatures (q + 1) D
      (alphabet.map Prod.fst)).size ≤
      (1 + (q + 1) * alphabet.size) ^ D := by
    simpa using hfeature
  exact (sequentialIndependent_size_le_features D alphabet q out h).trans hbound

#print axioms certifiedMaterializedDependence_total_of_free
#print axioms compressUntilIndependent_total
#print axioms compressUntilIndependent_independent
#print axioms compressUntilIndependent_labels
#print axioms sequentialIndependent_generated_moments
#print axioms sequentialIndependent_pattern_moment
#print axioms sequentialIndependent_size_polynomial

end CurrentAdditive.IndependentSupport
