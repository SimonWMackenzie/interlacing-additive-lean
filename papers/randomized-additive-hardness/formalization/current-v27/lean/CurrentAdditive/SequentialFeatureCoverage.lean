import CurrentAdditive.SequentialAppendMoments

/-!
Coverage and coordinate validity of the literal generated cylinder array.
Arrays may repeat entries when the alphabet array repeats labels; membership
and moments remain indexed and do not quotient those repeats.
-/

namespace CurrentAdditive.SequentialFeatureCoverage

open SequentialCode SequentialSourceCode SequentialAppendMoments

def FeatureValid (q : Nat) {Y : Type*} (c : List (Nat × Y)) : Prop :=
  ∀ p ∈ c, p.1 < q

theorem generatedFeatures_succ {Y : Type*} (q D : Nat)
    (alphabet : Array Y) :
    generatedFeatures (q + 1) D alphabet =
      extendFeatures D alphabet q (generatedFeatures q D alphabet) := by
  simp [generatedFeatures, List.range_succ, List.foldl_append]

private theorem fold_append_all {α β : Type*}
    (xs : List α) (out : Array β) (f : α → Array β)
    (P : β → Prop)
    (hout : ∀ b ∈ out.toList, P b)
    (hf : ∀ x ∈ xs, ∀ b ∈ (f x).toList, P b) :
    ∀ b ∈ (xs.foldl (fun acc x => acc ++ f x) out).toList, P b := by
  induction xs generalizing out with
  | nil => simpa using hout
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih (out ++ f x)
      · intro b hb
        rw [Array.toList_append] at hb
        rcases List.mem_append.mp hb with h | h
        · exact hout b h
        · exact hf x (by simp) b h
      · intro a ha b hb
        exact hf a (by simp [ha]) b hb

private theorem fold_append_contains_start {α β : Type*}
    (xs : List α) (out : Array β) (f : α → Array β)
    {b : β} (hb : b ∈ out.toList) :
    b ∈ (xs.foldl (fun acc x => acc ++ f x) out).toList := by
  induction xs generalizing out with
  | nil => simpa using hb
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih (out ++ f x)
      rw [Array.toList_append]
      exact List.mem_append_left _ hb

private theorem fold_append_contains_piece {α β : Type*}
    (xs : List α) (out : Array β) (f : α → Array β)
    {x : α} {b : β} (hx : x ∈ xs) (hb : b ∈ (f x).toList) :
    b ∈ (xs.foldl (fun acc z => acc ++ f z) out).toList := by
  induction xs generalizing out with
  | nil => cases hx
  | cons z xs ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hx with h | h
      · subst z
        apply fold_append_contains_start xs (out ++ f x) f
        rw [Array.toList_append]
        exact List.mem_append_right _ hb
      · exact ih (out ++ f z) h

theorem extendFeatures_mem_old {Y : Type*} (q D : Nat)
    (alphabet : Array Y) (features : Array (List (Nat × Y)))
    (c : List (Nat × Y)) (hc : c ∈ features.toList) :
    c ∈ (extendFeatures D alphabet q features).toList := by
  unfold extendFeatures
  rw [Array.toList_append]
  exact List.mem_append_left _ hc

theorem extendFeatures_mem_new {Y : Type*} (q D : Nat)
    (alphabet : Array Y) (features : Array (List (Nat × Y)))
    (c : List (Nat × Y)) (hc : c ∈ features.toList)
    (hlen : c.length < D) (y : Y) (hy : y ∈ alphabet.toList) :
    (q, y) :: c ∈ (extendFeatures D alphabet q features).toList := by
  let selected := features.filter (fun c => decide (c.length < D))
  have hselected : c ∈ selected.toList := by
    simp [selected, hc, hlen]
  have hpiece : (q, y) :: c ∈
      (alphabet.map (fun z => (q, z) :: c)).toList := by
    rw [Array.toList_map]
    exact List.mem_map.mpr ⟨y, hy, rfl⟩
  have hfold := fold_append_contains_piece selected.toList #[]
    (fun c => alphabet.map (fun z => (q, z) :: c))
    hselected hpiece
  unfold extendFeatures
  rw [Array.toList_append]
  apply List.mem_append_right
  simpa [selected, ← Array.foldl_toList] using hfold

theorem extendFeatures_valid {Y : Type*} (q D : Nat)
    (alphabet : Array Y) (features : Array (List (Nat × Y)))
    (hfeatures : ∀ c ∈ features.toList, FeatureValid q c) :
    ∀ c ∈ (extendFeatures D alphabet q features).toList,
      FeatureValid (q + 1) c := by
  let old := features.filter (fun c => decide (c.length < D))
  have hfold : ∀ c ∈ old.toList, FeatureValid q c := by
    intro c hc
    apply hfeatures c
    simp [old] at hc
    simpa using hc.1
  have hnew : ∀ c ∈ old.toList,
      ∀ b ∈ (alphabet.map (fun y => (q, y) :: c)).toList,
        FeatureValid (q + 1) b := by
    intro c hc b hb
    rw [Array.toList_map] at hb
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · cases hp
      omega
    · exact Nat.lt_trans (hfold c hc p hp) (Nat.lt_succ_self q)
  intro c hc
  unfold extendFeatures at hc
  rw [Array.toList_append] at hc
  rcases List.mem_append.mp hc with hold | hnewmem
  · intro p hp
    exact Nat.lt_trans (hfeatures c hold p hp) (Nat.lt_succ_self q)
  · rw [← Array.foldl_toList] at hnewmem
    exact fold_append_all old.toList #[]
      (fun c => alphabet.map (fun y => (q, y) :: c))
      (FeatureValid (q + 1))
      (by simp) hnew c hnewmem

theorem generatedFeatures_valid {Y : Type*} (q D : Nat)
    (alphabet : Array Y) :
    ∀ c ∈ (generatedFeatures q D alphabet).toList, FeatureValid q c := by
  induction q with
  | zero =>
      simp [generatedFeatures, FeatureValid]
  | succ q ih =>
      rw [generatedFeatures_succ]
      exact extendFeatures_valid q D alphabet _ ih

theorem appendWord_eta {Y : Type*} {q : Nat}
    (w : Fin (q + 1) → Y) :
    appendWord (fun i : Fin q =>
      w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (w ⟨q, Nat.lt_succ_self q⟩) = w := by
  funext j
  by_cases hj : j.val < q
  · simp [appendWord, hj]
  · have hval : j.val = q := by omega
    have heq : j = ⟨q, Nat.lt_succ_self q⟩ := Fin.ext hval
    subst j
    simp [appendWord]

theorem weightedSum_append_old_feature {Y : Type*} [DecidableEq Y]
    {q : Nat} (source : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ))
    (c : List (Nat × Y)) (hc : FeatureValid q c)
    (halphabet : sourceMass alphabet = 1) :
    weightedSum (appendSource source alphabet)
      (fun w => generatedFeatureValue w c) =
      weightedSum source (fun v => generatedFeatureValue v c) := by
  have hfun : (fun w : Fin (q + 1) → Y => generatedFeatureValue w c) =
      (fun w => generatedFeatureValue
        (fun i : Fin q => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) c) := by
    funext w
    conv_lhs => rw [← appendWord_eta w]
    exact generatedFeatureValue_append_old _ _ c hc
  rw [hfun]
  exact weightedSum_appendSource_old source alphabet
    (fun v => generatedFeatureValue v c) halphabet

theorem weightedSum_append_new_feature {Y : Type*} [DecidableEq Y]
    {q : Nat} (source : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ))
    (c : List (Nat × Y)) (hc : FeatureValid q c) (y₀ : Y) :
    weightedSum (appendSource source alphabet)
      (fun w => generatedFeatureValue w ((q, y₀) :: c)) =
      weightedSum source (fun v => generatedFeatureValue v c) *
        weightedSum alphabet (fun y => if y = y₀ then 1 else 0) := by
  have hfun : (fun w : Fin (q + 1) → Y =>
      generatedFeatureValue w ((q, y₀) :: c)) =
      (fun w => generatedFeatureValue
        (fun i : Fin q => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) c *
        (if w ⟨q, Nat.lt_succ_self q⟩ = y₀ then 1 else 0)) := by
    funext w
    conv_lhs => rw [← appendWord_eta w]
    exact generatedFeatureValue_append_new _ _ y₀ c hc
  rw [hfun]
  exact weightedSum_appendSource_factor source alphabet
    (fun v => generatedFeatureValue v c)
    (fun y => if y = y₀ then 1 else 0)

def alphabetPointMass {Y : Type*} [DecidableEq Y]
    (alphabet : Array (Y × ℚ)) (y : Y) : ℚ :=
  weightedSum alphabet (fun z => if z = y then 1 else 0)

def featureTarget {Y : Type*} [DecidableEq Y]
    (alphabet : Array (Y × ℚ))
    (c : List (Nat × Y)) : ℚ :=
  (c.map (fun p => alphabetPointMass alphabet p.2)).prod

theorem featureTarget_cons {Y : Type*} [DecidableEq Y]
    (alphabet : Array (Y × ℚ)) (q : Nat) (y : Y)
    (c : List (Nat × Y)) :
    featureTarget alphabet ((q, y) :: c) =
      alphabetPointMass alphabet y * featureTarget alphabet c := by
  simp [featureTarget]

theorem extendFeatures_mem_cases {Y : Type*} (q D : Nat)
    (alphabet : Array Y) (features : Array (List (Nat × Y)))
    (c : List (Nat × Y))
    (hc : c ∈ (extendFeatures D alphabet q features).toList) :
    c ∈ features.toList ∨
      ∃ old ∈ features.toList, old.length < D ∧
        ∃ y ∈ alphabet.toList, c = (q, y) :: old := by
  let selected := features.filter (fun old => decide (old.length < D))
  have hnew : ∀ c ∈ selected.toList,
      ∀ b ∈ (alphabet.map (fun y => (q, y) :: c)).toList,
        ∃ old ∈ selected.toList,
          ∃ y ∈ alphabet.toList, b = (q, y) :: old := by
    intro old hold b hb
    rw [Array.toList_map] at hb
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    exact ⟨old, hold, y, hy, rfl⟩
  unfold extendFeatures at hc
  rw [Array.toList_append] at hc
  rcases List.mem_append.mp hc with hold | hc
  · exact Or.inl hold
  · rw [← Array.foldl_toList] at hc
    have h := fold_append_all selected.toList #[]
      (fun old => alphabet.map (fun y => (q, y) :: old))
      (fun b => ∃ old ∈ selected.toList,
        ∃ y ∈ alphabet.toList, b = (q, y) :: old)
      (by simp) hnew c hc
    obtain ⟨old, hold, y, hy, rfl⟩ := h
    have hfiltered : old ∈ features.toList ∧ old.length < D := by
      simpa [selected] using hold
    exact Or.inr ⟨old, hfiltered.1, hfiltered.2, y, hy, rfl⟩

theorem compression_preserves_generated_feature {Y : Type*}
    [DecidableEq Y] {q D : Nat} (alphabet : Array Y)
    (source out : Array ((Fin q → Y) × ℚ))
    (hcompress :
      compressSourceFuelMaterialized
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
  have hm := (compressSourceFuelMaterialized_moments
    F.size (fun v j => generatedFeatureValue v F[j])
      source out source.size (by simpa [F] using hcompress)).2 j
  simpa [sourceMoment_eq_weightedSum, F, j, hget] using hm

/-- Canonical list encoding of a partial coordinate assignment. The largest
coordinate is at the head when it is specified. -/
def patternFeature {Y : Type*} :
    (q : Nat) → (Fin q → Option Y) → List (Nat × Y)
  | 0, _ => []
  | q + 1, p =>
      let old : Fin q → Option Y :=
        fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      let c := patternFeature q old
      match p ⟨q, Nat.lt_succ_self q⟩ with
      | none => c
      | some y => (q, y) :: c

theorem patternFeature_mem_generated {Y : Type*}
    (D : Nat) (alphabet : Array Y) :
    ∀ q (p : Fin q → Option Y),
      (∀ i y, p i = some y → y ∈ alphabet.toList) →
      (patternFeature q p).length ≤ D →
      patternFeature q p ∈ (generatedFeatures q D alphabet).toList := by
  intro q
  induction q with
  | zero =>
      intro p hvalues hlen
      simp [patternFeature, generatedFeatures]
  | succ q ih =>
      intro p hvalues hlen
      let old : Fin q → Option Y :=
        fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      let c := patternFeature q old
      have hOldValues : ∀ i y, old i = some y → y ∈ alphabet.toList := by
        intro i y hi
        exact hvalues _ y hi
      cases hlast : p ⟨q, Nat.lt_succ_self q⟩ with
      | none =>
          have hc : c.length ≤ D := by
            simpa [patternFeature, c, old, hlast] using hlen
          have hmem := ih old hOldValues hc
          rw [generatedFeatures_succ]
          simpa [patternFeature, c, old, hlast] using
            (extendFeatures_mem_old q D alphabet _ c hmem)
      | some y =>
          have hc : c.length < D := by
            have hle : (c.length + 1) ≤ D := by
              simpa [patternFeature, c, old, hlast] using hlen
            omega
          have hmem := ih old hOldValues (Nat.le_of_lt hc)
          have hy : y ∈ alphabet.toList := hvalues _ y hlast
          rw [generatedFeatures_succ]
          simpa [patternFeature, c, old, hlast] using
            (extendFeatures_mem_new q D alphabet _ c hmem hc y hy)

theorem patternFeature_valid {Y : Type*} :
    ∀ q (p : Fin q → Option Y), FeatureValid q (patternFeature q p) := by
  intro q
  induction q with
  | zero =>
      intro p
      simp [patternFeature, FeatureValid]
  | succ q ih =>
      intro p
      let old : Fin q → Option Y :=
        fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      have hold := ih old
      cases hlast : p ⟨q, Nat.lt_succ_self q⟩ with
      | none =>
          intro a ha
          have ha' : a ∈ patternFeature q old := by
            simpa [patternFeature, old, hlast] using ha
          exact Nat.lt_trans (hold a ha') (Nat.lt_succ_self q)
      | some y =>
          intro a ha
          have ha' : a ∈ (q, y) :: patternFeature q old := by
            simpa [patternFeature, old, hlast] using ha
          rcases List.mem_cons.mp ha' with heq | htail
          · cases heq
            omega
          · exact Nat.lt_trans (hold a htail) (Nat.lt_succ_self q)

def PatternMatches {Y : Type*} {q : Nat}
    (p : Fin q → Option Y) (v : Fin q → Y) : Prop :=
  ∀ i, p i = none ∨ p i = some (v i)

theorem patternMatches_succ_iff {Y : Type*} {q : Nat}
    (p : Fin (q + 1) → Option Y) (v : Fin (q + 1) → Y) :
    PatternMatches p v ↔
      PatternMatches
        (fun i : Fin q => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
        (fun i : Fin q => v ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) ∧
      (p ⟨q, Nat.lt_succ_self q⟩ = none ∨
        p ⟨q, Nat.lt_succ_self q⟩ = some (v ⟨q, Nat.lt_succ_self q⟩)) := by
  constructor
  · intro h
    exact ⟨fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩,
      h ⟨q, Nat.lt_succ_self q⟩⟩
  · rintro ⟨hold, hlast⟩ i
    by_cases hi : i.val < q
    · have heq : i = ⟨i.val, Nat.lt_succ_of_lt hi⟩ := Fin.ext rfl
      rw [heq]
      exact hold ⟨i.val, hi⟩
    · have hval : i.val = q := by omega
      have heq : i = ⟨q, Nat.lt_succ_self q⟩ := Fin.ext hval
      rw [heq]
      exact hlast

def patternSize {Y : Type*} {q : Nat}
    (p : Fin q → Option Y) : Nat :=
  ∑ i : Fin q, if (p i).isSome then 1 else 0

theorem patternFeature_length_eq_size {Y : Type*} :
    ∀ q (p : Fin q → Option Y),
      (patternFeature q p).length = patternSize p := by
  intro q
  induction q with
  | zero =>
      intro p
      simp [patternFeature, patternSize]
  | succ q ih =>
      intro p
      let old : Fin q → Option Y :=
        fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      have hold := ih old
      cases hlast : p ⟨q, Nat.lt_succ_self q⟩ with
      | none =>
          unfold patternSize at hold ⊢
          rw [Fin.sum_univ_castSucc]
          simpa only [patternFeature, hlast, Fin.castSucc, Fin.last,
            Option.isSome_none, ite_false, add_zero] using hold
      | some y =>
          unfold patternSize at hold ⊢
          rw [Fin.sum_univ_castSucc]
          simpa only [patternFeature, hlast, Fin.castSucc, Fin.last,
            Option.isSome_some, ite_true, List.length_cons,
            Nat.succ_eq_add_one] using
            congrArg Nat.succ hold

theorem patternFeature_indicator {Y : Type*} [DecidableEq Y] :
    ∀ q (p : Fin q → Option Y) (v : Fin q → Y)
      [Decidable (PatternMatches p v)],
      generatedFeatureValue v (patternFeature q p) =
        if PatternMatches p v then 1 else 0 := by
  classical
  intro q
  induction q with
  | zero =>
      intro p v inst
      have hmatch : PatternMatches p v := by
        intro i
        exact Fin.elim0 i
      simp [patternFeature, generatedFeatureValue, hmatch]
  | succ q ih =>
      intro p v inst
      let oldp : Fin q → Option Y :=
        fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      let oldv : Fin q → Y :=
        fun i => v ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      let c := patternFeature q oldp
      have hvalid : FeatureValid q c := patternFeature_valid q oldp
      have hsplit := patternMatches_succ_iff p v
      cases hlast : p ⟨q, Nat.lt_succ_self q⟩ with
      | none =>
          have hvalue : generatedFeatureValue v (patternFeature (q + 1) p) =
              generatedFeatureValue oldv c := by
            conv_lhs => rw [← appendWord_eta v]
            simpa [patternFeature, oldp, oldv, c, hlast] using
              (generatedFeatureValue_append_old oldv
                (v ⟨q, Nat.lt_succ_self q⟩) c hvalid)
          rw [hvalue, ih oldp oldv]
          have hiff : PatternMatches p v ↔ PatternMatches oldp oldv := by
            simpa [oldp, oldv, hlast] using hsplit
          by_cases hm : PatternMatches oldp oldv <;> simp [hiff, hm]
      | some y =>
          have hvalue : generatedFeatureValue v (patternFeature (q + 1) p) =
              generatedFeatureValue oldv c *
                (if v ⟨q, Nat.lt_succ_self q⟩ = y then 1 else 0) := by
            conv_lhs => rw [← appendWord_eta v]
            simpa [patternFeature, oldp, oldv, c, hlast] using
              (generatedFeatureValue_append_new oldv
                (v ⟨q, Nat.lt_succ_self q⟩) y c hvalid)
          rw [hvalue, ih oldp oldv]
          have hiff : PatternMatches p v ↔
              PatternMatches oldp oldv ∧
                v ⟨q, Nat.lt_succ_self q⟩ = y := by
            simpa [oldp, oldv, hlast, eq_comm] using hsplit
          by_cases hm : PatternMatches oldp oldv <;>
            by_cases hy : v ⟨q, Nat.lt_succ_self q⟩ = y <;>
            simp [hiff, hm, hy]

def patternTarget {Y : Type*} [DecidableEq Y] {q : Nat}
    (alphabet : Array (Y × ℚ)) (p : Fin q → Option Y) : ℚ :=
  ∏ i : Fin q,
    match p i with
    | none => 1
    | some y => alphabetPointMass alphabet y

theorem featureTarget_patternFeature {Y : Type*} [DecidableEq Y]
    (alphabet : Array (Y × ℚ)) :
    ∀ q (p : Fin q → Option Y),
      featureTarget alphabet (patternFeature q p) =
        patternTarget alphabet p := by
  intro q
  induction q with
  | zero =>
      intro p
      simp [patternFeature, patternTarget, featureTarget]
  | succ q ih =>
      intro p
      let old : Fin q → Option Y :=
        fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      have hold := ih old
      cases hlast : p ⟨q, Nat.lt_succ_self q⟩ with
      | none =>
          unfold patternTarget at hold ⊢
          rw [Fin.prod_univ_castSucc]
          simpa only [patternFeature, hlast, Fin.castSucc, Fin.last,
            one_mul, mul_one] using hold
      | some y =>
          unfold patternTarget at hold ⊢
          rw [Fin.prod_univ_castSucc]
          simp only [patternFeature, hlast, featureTarget_cons,
            Fin.castSucc, Fin.last]
          rw [hold]
          have hprod :
              (∏ i : Fin q,
                match old i with
                | none => (1 : ℚ)
                | some z => alphabetPointMass alphabet z) =
              (∏ i : Fin q,
                match p (Fin.castAdd 1 i) with
                | none => (1 : ℚ)
                | some z => alphabetPointMass alphabet z) := by
            apply Finset.prod_congr rfl
            intro i hi
            rfl
          rw [hprod]
          ring

/-- Every cylinder actually listed by the executable feature enumerator has
its exact independent-alphabet rational moment in the retained source. -/
theorem sequentialMaterialized_generated_moments {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabet : sourceMass alphabet = 1) :
    ∀ q out, sequentialMaterialized D alphabet q = some out →
      ∀ c ∈ (generatedFeatures q D (alphabet.map Prod.fst)).toList,
        weightedSum out (fun v => generatedFeatureValue v c) =
          featureTarget alphabet c := by
  intro q
  induction q with
  | zero =>
      intro out hout c hc
      simp only [sequentialMaterialized] at hout
      cases hout
      simp [generatedFeatures] at hc
      rcases hc with rfl
      simp [weightedSum, generatedFeatureValue, featureTarget]
  | succ q ih =>
      intro out hout c hc
      simp only [sequentialMaterialized] at hout
      cases hprev : sequentialMaterialized D alphabet q with
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
            · -- The induction hypothesis supplies the old-cylinder moment.
              rw [weightedSum_append_old_feature prev alphabet c
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

/-- Exact singleton probability for any partial assignment on at most `D`
coordinates, provided its symbols occur in the alphabet array. -/
theorem sequentialMaterialized_pattern_moment {Y : Type*}
    [DecidableEq Y] (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabet : sourceMass alphabet = 1)
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (hout : sequentialMaterialized D alphabet q = some out)
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
      sequentialMaterialized_generated_moments D alphabet halphabet
        q out hout c hmem
    _ = patternTarget alphabet p := featureTarget_patternFeature alphabet q p

#print axioms generatedFeatures_valid
#print axioms sequentialMaterialized_generated_moments
#print axioms patternFeature_mem_generated
#print axioms patternFeature_indicator
#print axioms featureTarget_patternFeature
#print axioms sequentialMaterialized_pattern_moment

end CurrentAdditive.SequentialFeatureCoverage
