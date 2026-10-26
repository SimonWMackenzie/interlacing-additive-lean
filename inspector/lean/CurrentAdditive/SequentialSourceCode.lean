import CurrentAdditive.MaterializedGauss
import CurrentAdditive.SequentialElimination
import CurrentAdditive.ZeroDeletion

/-!
A sequential labelled source using the materialized, proved-total rational
dependence finder. Every update remains checked against the input feature
matrix and the retained labelled source. Success and resource bounds are
separate theorems below or in later files.
-/

namespace CurrentAdditive.SequentialSourceCode

open SequentialCode SequentialArrayBridge SequentialTotality
  SequentialCompressionTotality MaterializedGauss

theorem featureRows_constant_row {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source : Array (α × ℚ))
    (hconstant : ∃ j : Fin n, ∀ x, φ x j = 1) :
    ∃ i, i < (featureRows n φ source).size ∧
      ∀ j, j < columnCount (featureRows n φ source) →
        cell (featureRows n φ source) i j = 1 := by
  obtain ⟨i, hi⟩ := hconstant
  refine ⟨i.val, ?_, ?_⟩
  · simp [featureRows, i.isLt]
  · intro j hj
    have hn : 0 < n := Nat.pos_of_ne_zero (by
      intro hz
      subst n
      exact Fin.elim0 i)
    have hj' : j < source.size := by
      simpa [featureRows_columnCount n φ source hn] using hj
    have hφ := hi (source[j].1)
    simpa [featureRows, cell, hj'] using hφ

private theorem extendFeatures_head {Y : Type*} (D j : Nat)
    (alphabet : Array Y) (features : Array (List (Nat × Y)))
    (hhead : features[0]? = some []) :
    (extendFeatures D alphabet j features)[0]? = some [] := by
  have hpos : 0 < features.size := by
    by_contra h
    have hz : features[0]? = none := by
      simp [Nat.not_lt.mp h]
    rw [hhead] at hz
    cases hz
  simpa [extendFeatures, Array.getElem?_append_left hpos] using hhead

private theorem foldl_extendFeatures_head {Y : Type*} (D : Nat)
    (alphabet : Array Y) (js : List Nat)
    (features : Array (List (Nat × Y)))
    (hhead : features[0]? = some []) :
    (js.foldl (fun current j => extendFeatures D alphabet j current)
      features)[0]? = some [] := by
  induction js generalizing features with
  | nil => simpa using hhead
  | cons j rest ih =>
      simp only [List.foldl_cons]
      exact ih _ (extendFeatures_head D j alphabet features hhead)

theorem generatedFeatures_head_empty {Y : Type*} (q D : Nat)
    (alphabet : Array Y) :
    (generatedFeatures q D alphabet)[0]? = some [] := by
  unfold generatedFeatures
  exact foldl_extendFeatures_head D alphabet (List.range q) #[[]] (by simp)

theorem generatedFeatures_pos {Y : Type*} (q D : Nat)
    (alphabet : Array Y) :
    0 < (generatedFeatures q D alphabet).size := by
  have h := generatedFeatures_head_empty q D alphabet
  by_contra hn
  have hz : (generatedFeatures q D alphabet)[0]? = none := by
    simp [Nat.not_lt.mp hn]
  rw [h] at hz
  cases hz

theorem generatedFeatures_constant {Y : Type*} [DecidableEq Y]
    (q D : Nat) (alphabet : Array Y) :
    ∃ j : Fin (generatedFeatures q D alphabet).size,
      ∀ v : Fin q → Y,
        generatedFeatureValue v (generatedFeatures q D alphabet)[j] = 1 := by
  let F := generatedFeatures q D alphabet
  have hpos : 0 < F.size := generatedFeatures_pos q D alphabet
  refine ⟨⟨0, hpos⟩, ?_⟩
  intro v
  have hhead : F[0] = ([] : List (Nat × Y)) := by
    have h := generatedFeatures_head_empty q D alphabet
    change F[0]? = some [] at h
    rw [Array.getElem?_eq_getElem hpos] at h
    exact Option.some.inj h
  simp [F, hhead, generatedFeatureValue]

private theorem filterMap_length_le {α β : Type*} (f : α → Option β)
    (l : List α) : (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.filterMap_cons]
      cases f x <;> simp_all <;> omega

/-- The exact deletion routine keeps only entries whose updated weights are
strictly positive, even if several indices decode to the same label. -/
theorem selectedSource_positive {α : Type*}
    (source : Array (α × ℚ)) (updated : Array ℚ) :
    ((positiveIndices updated).filterMap (fun i =>
      (source[i]?).map (fun entry =>
        (entry.1, updated[i]?.getD 0)))).toArray.all
          (fun entry => decide (0 < entry.2)) = true := by
  rw [Array.all_eq_true_iff_forall_mem]
  intro entry hentry
  have hlist : entry ∈ (positiveIndices updated).filterMap (fun i =>
      (source[i]?).map (fun e => (e.1, updated[i]?.getD 0))) := by
    simpa using hentry
  obtain ⟨i, hi, hmap⟩ := List.mem_filterMap.mp hlist
  have hpos : 0 < updated[i]?.getD 0 := by
    change i ∈ (List.range updated.size).filter
      (fun i => decide (0 < updated[i]?.getD 0)) at hi
    simpa using (List.mem_filter.mp hi).2
  cases hsource : source[i]? with
  | none => simp [hsource] at hmap
  | some e =>
      simp [hsource] at hmap
      subst entry
      simpa using hpos

def SourcePositive {α : Type*} (source : Array (α × ℚ)) : Prop :=
  source.all (fun entry => decide (0 < entry.2)) = true

theorem sourcePositive_weights {α : Type*}
    (source : Array (α × ℚ)) (hpositive : SourcePositive source) :
    (source.map Prod.snd).all (fun w => decide (0 < w)) = true := by
  apply Array.all_eq_true.mpr
  intro i hi
  have hi' : i < source.size := by simpa using hi
  have hp := (Array.all_eq_true.mp hpositive) i hi'
  simpa [SourcePositive] using hp

theorem appendSource_positive {Y : Type*} {q : Nat}
    (source : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ))
    (hsource : SourcePositive source)
    (halphabet : SourcePositive alphabet) :
    SourcePositive (appendSource source alphabet) := by
  have hsourceMem : ∀ x ∈ source.toList, 0 < x.2 := by
    intro x hx
    have h := (Array.all_eq_true_iff_forall_mem.mp hsource) x (by simpa using hx)
    simpa [SourcePositive] using h
  have halphaMem : ∀ y ∈ alphabet.toList, 0 < y.2 := by
    intro y hy
    have h := (Array.all_eq_true_iff_forall_mem.mp halphabet) y (by simpa using hy)
    simpa [SourcePositive] using h
  have hchunk (x : (Fin q → Y) × ℚ) (hx : 0 < x.2) :
      SourcePositive (alphabet.map (fun y =>
        (appendWord x.1 y.1, x.2 * y.2))) := by
    rw [SourcePositive, Array.all_map, Array.all_eq_true]
    intro i hi
    have hy : 0 < alphabet[i].2 := halphaMem alphabet[i] (by
      simpa using (Array.getElem_mem hi))
    simp [mul_pos hx hy]
  have hfold (l : List ((Fin q → Y) × ℚ))
      (hl : ∀ x ∈ l, 0 < x.2)
      (acc : Array ((Fin (q + 1) → Y) × ℚ))
      (hacc : SourcePositive acc) :
      SourcePositive (l.foldl (fun out x =>
        out ++ alphabet.map (fun y =>
          (appendWord x.1 y.1, x.2 * y.2))) acc) := by
    induction l generalizing acc with
    | nil => simpa using hacc
    | cons x xs ih =>
        have hx : 0 < x.2 := hl x (by simp)
        have hxs : ∀ y ∈ xs, 0 < y.2 := by
          intro y hy
          exact hl y (by simp [hy])
        have hnew : SourcePositive (acc ++ alphabet.map
            (fun y => (appendWord x.1 y.1, x.2 * y.2))) := by
          change (acc ++ alphabet.map
            (fun y => (appendWord x.1 y.1, x.2 * y.2))).all
              (fun entry => decide (0 < entry.2)) = true
          rw [Array.all_append]
          have hc : (alphabet.map (fun y =>
              (appendWord x.1 y.1, x.2 * y.2))).all
                (fun entry => decide (0 < entry.2)) = true := hchunk x hx
          change acc.all (fun entry => decide (0 < entry.2)) = true at hacc
          rw [hacc, hc]
          rfl
        simpa [List.foldl_cons] using ih hxs _ hnew
  unfold appendSource
  rw [← Array.foldl_toList]
  exact hfold source.toList hsourceMem #[] (by simp [SourcePositive])

def compressSourceOnceMaterialized {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) : Option (Array (α × ℚ)) :=
  let matrix := featureRows n φ source
  let weights := source.map Prod.snd
  match certifiedMaterializedDependence matrix with
  | none => none
  | some cert =>
    match eliminateWeights weights cert.val with
    | none => none
    | some updated =>
      let indices := positiveIndices updated
      if weights.all (fun w => decide (0 < w)) &&
          updated.all (fun w => decide (0 ≤ w)) &&
          sameMoments matrix weights updated then
        if indices.length < source.size then
          let out := (indices.filterMap (fun i =>
            (source[i]?).map (fun entry => (entry.1, updated[i]?.getD 0)))).toArray
          if sourceMomentsCheck n φ source out then some out else none
        else none
      else none

theorem compressSourceOnceMaterialized_positive {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ))
    (h : compressSourceOnceMaterialized n φ source = some out) :
    SourcePositive out := by
  unfold compressSourceOnceMaterialized at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · split at h
          · cases h
            exact selectedSource_positive source _
          · cases h
        · cases h
      · cases h

/-- A positive overfull labelled source always takes one checked support
reduction step when its feature list includes the constant function. -/
theorem compressSourceOnceMaterialized_total {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ))
    (hn : 0 < n)
    (hconstant : ∃ j : Fin n, ∀ x, φ x j = 1)
    (hover : n < source.size)
    (hpositive : SourcePositive source) :
    ∃ out, compressSourceOnceMaterialized n φ source = some out := by
  let matrix := featureRows n φ source
  let weights := source.map Prod.snd
  have hmatrixOver : matrix.size < columnCount matrix := by
    dsimp [matrix]
    rw [featureRows_columnCount n φ source hn]
    simpa [featureRows] using hover
  obtain ⟨cert, hcert⟩ :=
    certifiedMaterializedDependence_total matrix hmatrixOver
  have hsize : weights.size = columnCount matrix := by
    simp [weights, matrix, featureRows_columnCount n φ source hn]
  have hweights : weights.all (fun w => decide (0 < w)) = true :=
    sourcePositive_weights source hpositive
  have hw : ∀ i < weights.size, 0 < weights[i]?.getD 0 := by
    intro i hi
    have hp := (Array.all_eq_true.mp hweights) i hi
    simpa [hi] using hp
  have hsum : cert.val.toList.sum = 0 :=
    SequentialElimination.zero_sum_of_constant_row matrix cert.val
      cert.property (by simpa [matrix] using
        featureRows_constant_row n φ source hconstant)
  obtain ⟨updated, hupdated, hupdatedsize, hnonneg, hsame, hshrink⟩ :=
    SequentialElimination.eliminateWeights_total matrix weights cert.val
      hsize hw cert.property hsum
  let indices := positiveIndices updated
  let out := (indices.filterMap (fun i =>
    (source[i]?).map (fun entry => (entry.1, updated[i]?.getD 0)))).toArray
  have hsourcecheck : sourceMomentsCheck n φ source out = true := by
    exact SequentialZeroDeletion.sourceMomentsCheck_after_positiveIndices
      n φ source updated hnonneg (by simpa [matrix, weights] using hsame)
  refine ⟨out, ?_⟩
  simp [compressSourceOnceMaterialized, matrix, weights,
    hcert, hupdated, hnonneg, hsame,
    hsourcecheck, indices, out]
  constructor
  · intro i hi
    simpa using (Array.all_eq_true.mp hpositive) i hi
  · simpa [weights] using hshrink

theorem compressSourceOnceMaterialized_size_lt {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source out : Array (α × ℚ))
    (h : compressSourceOnceMaterialized n φ source = some out) :
    out.size < source.size := by
  unfold compressSourceOnceMaterialized at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · split at h
          · cases h
            exact lt_of_le_of_lt
              (by simpa using (filterMap_length_le _ _))
              (by assumption)
          · cases h
        · cases h
      · cases h

theorem compressSourceOnceMaterialized_moments {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source out : Array (α × ℚ))
    (h : compressSourceOnceMaterialized n φ source = some out) :
    sourceMass source = sourceMass out ∧
      ∀ j : Fin n, sourceMoment φ source j = sourceMoment φ out j := by
  unfold compressSourceOnceMaterialized at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · split at h
          · cases h
            exact (sourceMomentsCheck_spec n φ source _).mp (by assumption)
          · cases h
        · cases h
      · cases h

def compressSourceFuelMaterialized {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (fuel : Nat) :
    Option (Array (α × ℚ)) :=
  match fuel with
  | 0 => if source.size ≤ n then some source else none
  | fuel + 1 =>
    if source.size ≤ n then some source else do
      let next ← compressSourceOnceMaterialized n φ source
      compressSourceFuelMaterialized n φ next fuel

theorem compressSourceFuelMaterialized_size_le {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (fuel : Nat) (out : Array (α × ℚ))
    (h : compressSourceFuelMaterialized n φ source fuel = some out) :
    out.size ≤ n := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressSourceFuelMaterialized] at h
      split_ifs at h with hs
      · cases h; exact hs
  | succ fuel ih =>
      simp only [compressSourceFuelMaterialized] at h
      split_ifs at h with hs
      · cases h; exact hs
      · cases hstep : compressSourceOnceMaterialized n φ source with
        | none => simp [hstep] at h
        | some next =>
            simp [hstep] at h
            exact ih next h

theorem compressSourceFuelMaterialized_moments {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel : Nat)
    (h : compressSourceFuelMaterialized n φ source fuel = some out) :
    sourceMass source = sourceMass out ∧
      ∀ j : Fin n, sourceMoment φ source j = sourceMoment φ out j := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressSourceFuelMaterialized] at h
      split_ifs at h
      cases h
      exact ⟨rfl, fun _ => rfl⟩
  | succ fuel ih =>
      simp only [compressSourceFuelMaterialized] at h
      split_ifs at h
      · cases h
        exact ⟨rfl, fun _ => rfl⟩
      · cases hstep : compressSourceOnceMaterialized n φ source with
        | none => simp [hstep] at h
        | some next =>
            simp [hstep] at h
            have hfirst := compressSourceOnceMaterialized_moments n φ source next hstep
            have hrest := ih next h
            exact ⟨hfirst.1.trans hrest.1,
              fun j => (hfirst.2 j).trans (hrest.2 j)⟩

theorem compressSourceFuelMaterialized_positive {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel : Nat)
    (hpositive : SourcePositive source)
    (h : compressSourceFuelMaterialized n φ source fuel = some out) :
    SourcePositive out := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressSourceFuelMaterialized] at h
      split_ifs at h
      cases h
      exact hpositive
  | succ fuel ih =>
      simp only [compressSourceFuelMaterialized] at h
      split_ifs at h
      · cases h
        exact hpositive
      · cases hstep : compressSourceOnceMaterialized n φ source with
        | none => simp [hstep] at h
        | some next =>
            simp [hstep] at h
            have hnextpos := compressSourceOnceMaterialized_positive n φ source next hstep
            exact ih next hnextpos h

/-- Once a checked one-step elimination is total on overfull positive
sources, the explicit source-size fuel is sufficient for every iteration. -/
theorem compressSourceFuelMaterialized_total_of_step {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (hstep : ∀ s : Array (α × ℚ), SourcePositive s → n < s.size →
      ∃ next, compressSourceOnceMaterialized n φ s = some next)
    (source : Array (α × ℚ)) (hpositive : SourcePositive source)
    (fuel : Nat) (hfuel : source.size ≤ fuel) :
    ∃ out, compressSourceFuelMaterialized n φ source fuel = some out := by
  induction fuel generalizing source with
  | zero =>
      have hs : source.size ≤ n := by omega
      exact ⟨source, by simp [compressSourceFuelMaterialized, hs]⟩
  | succ fuel ih =>
      by_cases hs : source.size ≤ n
      · exact ⟨source, by simp [compressSourceFuelMaterialized, hs]⟩
      · obtain ⟨next, hnext⟩ := hstep source hpositive (by omega)
        have hsmaller := compressSourceOnceMaterialized_size_lt n φ source next hnext
        have hnextpos := compressSourceOnceMaterialized_positive n φ source next hnext
        obtain ⟨out, hout⟩ := ih next hnextpos (by omega)
        refine ⟨out, ?_⟩
        simp [compressSourceFuelMaterialized, hs, hnext, hout]

theorem compressSourceFuelMaterialized_total {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n)
    (hconstant : ∃ j : Fin n, ∀ x, φ x j = 1)
    (source : Array (α × ℚ)) (hpositive : SourcePositive source)
    (fuel : Nat) (hfuel : source.size ≤ fuel) :
    ∃ out, compressSourceFuelMaterialized n φ source fuel = some out := by
  apply compressSourceFuelMaterialized_total_of_step n φ _ source hpositive fuel hfuel
  intro s hs hover
  exact compressSourceOnceMaterialized_total n φ s hn hconstant hover hs

def sequentialMaterialized {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) :
    (q : Nat) → Option (Array ((Fin q → Y) × ℚ))
  | 0 => some #[(Fin.elim0, 1)]
  | q + 1 => do
    let prev ← sequentialMaterialized D alphabet q
    let extended := appendSource prev alphabet
    let featuresAt := generatedFeatures (q + 1) D (alphabet.map Prod.fst)
    let n := featuresAt.size
    let features : (Fin (q + 1) → Y) → Fin n → ℚ :=
      fun v j => generatedFeatureValue v featuresAt[j]
    compressSourceFuelMaterialized n features extended extended.size

/-- Positive rational alphabet weights make every stage of the materialized
sequential constructor succeed. The rational source is still indexed, so
duplicate decoded words remain distinct entries. -/
theorem sequentialMaterialized_total {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabet : SourcePositive alphabet) :
    ∀ q, ∃ out, sequentialMaterialized D alphabet q = some out ∧
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
        compressSourceFuelMaterialized_total n features hn hconstant
          extended hextended extended.size (Nat.le_refl _)
      refine ⟨out, ?_, ?_⟩
      · simpa [sequentialMaterialized, hprev, extended, featuresAt, n, features]
          using hout
      · exact compressSourceFuelMaterialized_positive n features extended out
          extended.size hextended hout

theorem sequentialMaterialized_size_le_features {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (q : Nat) (out : Array ((Fin (q + 1) → Y) × ℚ))
    (h : sequentialMaterialized D alphabet (q + 1) = some out) :
    out.size ≤ (generatedFeatures (q + 1) D
      (alphabet.map Prod.fst)).size := by
  simp only [sequentialMaterialized] at h
  cases hprev : sequentialMaterialized D alphabet q with
  | none => simp [hprev] at h
  | some prev =>
      simp [hprev] at h
      exact compressSourceFuelMaterialized_size_le _ _ _ _ _ h

theorem sequentialMaterialized_exists_bounded {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabet : SourcePositive alphabet) (q : Nat) :
    ∃ out, sequentialMaterialized D alphabet q = some out ∧
      SourcePositive out ∧
      out.size ≤ (generatedFeatures q D (alphabet.map Prod.fst)).size := by
  obtain ⟨out, hout, hpos⟩ := sequentialMaterialized_total D alphabet halphabet q
  refine ⟨out, hout, hpos, ?_⟩
  cases q with
  | zero =>
      simp [sequentialMaterialized] at hout
      cases hout
      simp [generatedFeatures]
  | succ q =>
      exact sequentialMaterialized_size_le_features D alphabet q out hout

#print axioms compressSourceOnceMaterialized_size_lt
#print axioms compressSourceOnceMaterialized_moments
#print axioms compressSourceFuelMaterialized_size_le
#print axioms compressSourceFuelMaterialized_moments
#print axioms sequentialMaterialized_size_le_features
#print axioms compressSourceOnceMaterialized_total
#print axioms compressSourceFuelMaterialized_total
#print axioms sequentialMaterialized_total
#print axioms sequentialMaterialized_exists_bounded

end CurrentAdditive.SequentialSourceCode
