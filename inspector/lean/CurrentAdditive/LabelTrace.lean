import CurrentAdditive.IndependentSupport
import CurrentAdditive.SequentialSourceResource

/-! Private v38 Code D label trace. A label is an array position, independently
of the value decoded at that position. -/

namespace CurrentAdditive.LabelTrace

open SequentialCode SequentialSourceCode IndependentSupport
  SequentialFeatureCoverage

/-- Every output position has its own original input position. The equality
concerns decoded words, while injectivity concerns their independent labels. -/
def Retained {α : Type*} (source out : Array (α × ℚ)) : Prop :=
  ∃ trace : Fin out.size ↪ Fin source.size,
    ∀ j, out[j].1 = source[trace j].1

private theorem positiveIndices_nodup (updated : Array ℚ) :
    (positiveIndices updated).Nodup := by
  exact List.nodup_range.filter _

private theorem positiveIndices_bound (updated : Array ℚ)
    (i : Nat) (hi : i ∈ positiveIndices updated) : i < updated.size := by
  exact List.mem_range.mp (List.mem_filter.mp hi).1

private theorem positiveIndices_mem_iff (updated : Array ℚ)
    (i : Nat) (hi : i < updated.size) :
    i ∈ positiveIndices updated ↔ 0 < updated[i]?.getD 0 := by
  simp [positiveIndices, hi]

private theorem selectedSource_map {α : Type*} [Inhabited α]
    (source : Array (α × ℚ)) (updated : Array ℚ)
    (hsize : updated.size = source.size) :
    (positiveIndices updated).filterMap (fun i =>
      (source[i]?).map (fun entry => (entry.1, updated[i]?.getD 0))) =
    (positiveIndices updated).map (fun i =>
      ((source[i]?.getD (default, 0)).1, updated[i]?.getD 0)) := by
  apply List.filterMap_eq_map_iff_forall_eq_some.mpr
  intro i hi
  have his : i < source.size := hsize ▸ positiveIndices_bound updated i hi
  simp [his]

/-- The deletion step preserves each selected array position as a distinct
label. The image is exactly the positions with positive updated weight. -/
theorem selectedSource_trace {α : Type*} [Inhabited α]
    (source : Array (α × ℚ)) (updated : Array ℚ)
    (hsize : updated.size = source.size) :
    let out := ((positiveIndices updated).filterMap (fun i =>
      (source[i]?).map (fun entry =>
        (entry.1, updated[i]?.getD 0)))).toArray
    ∃ trace : Fin out.size ↪ Fin source.size,
      (∀ j, out[j] =
        (source[trace j].1, updated[(trace j).val]?.getD 0)) ∧
      (∀ i : Fin source.size,
        (∃ j, trace j = i) ↔ 0 < updated[i.val]?.getD 0) := by
  let indices := positiveIndices updated
  let out := (indices.filterMap (fun i =>
      (source[i]?).map (fun entry =>
        (entry.1, updated[i]?.getD 0)))).toArray
  have hmap : indices.filterMap (fun i =>
      (source[i]?).map (fun entry =>
        (entry.1, updated[i]?.getD 0))) =
      indices.map (fun i =>
        ((source[i]?.getD (default, 0)).1, updated[i]?.getD 0)) :=
    selectedSource_map source updated hsize
  have hlen : out.size = indices.length := by simp [out, hmap]
  let trace : Fin out.size ↪ Fin source.size := {
    toFun := fun j => ⟨indices[j.val], by
      have hj : j.val < indices.length := by rw [← hlen]; exact j.isLt
      have hmem : indices[j.val] ∈ indices := List.getElem_mem hj
      exact hsize ▸ positiveIndices_bound updated _ hmem⟩
    inj' := by
      intro a b hab
      apply Fin.ext
      apply (positiveIndices_nodup updated).getElem_inj_iff.mp
      exact congrArg Fin.val hab
  }
  refine ⟨trace, ?_, ?_⟩
  · intro j
    have hj : j.val < indices.length := by rw [← hlen]; exact j.isLt
    have hs : (trace j).val < source.size := (trace j).isLt
    have hopt := congrArg (fun l : List (α × ℚ) => l[j.val]?) hmap
    have hsrc : indices[j.val] < source.size := by simpa [trace] using hs
    have hget : out[j.val]? = some
        (source[(trace j).val].1, updated[(trace j).val]?.getD 0) := by
      simpa [out, trace, hj, hsrc] using hopt
    have hval : out[j.val] =
        (source[(trace j).val].1, updated[(trace j).val]?.getD 0) := by
      rw [Array.getElem?_eq_getElem j.isLt] at hget
      exact Option.some.inj hget
    exact hval
  · intro i
    constructor
    · rintro ⟨j, hj⟩
      have hjbound : j.val < indices.length := by rw [← hlen]; exact j.isLt
      have hm : (trace j).val ∈ indices := by
        simpa [trace] using (List.getElem_mem hjbound : indices[j.val] ∈ indices)
      have hi : i.val < updated.size := by simpa only [hsize] using i.isLt
      have hp := (positiveIndices_mem_iff updated i.val hi).mp
        (by simpa [trace, hj] using hm)
      exact hp
    · intro hp
      have hi : i.val < updated.size := by simpa only [hsize] using i.isLt
      have hm : i.val ∈ indices :=
        (positiveIndices_mem_iff updated i.val hi).mpr hp
      obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hm
      have ho : k < out.size := by omega
      refine ⟨⟨k, ho⟩, ?_⟩
      apply Fin.ext
      simpa [trace] using hget

/-- Delete zero-mass alphabet positions before the positive-only executable
loop. This uses the same indexed deletion code as every later elimination. -/
def positiveLaw {Y : Type*} (alphabet : Array (Y × ℚ)) :
    Array (Y × ℚ) :=
  SequentialZeroDeletion.retainedSource alphabet (alphabet.map Prod.snd)

theorem positiveLaw_positive {Y : Type*}
    (alphabet : Array (Y × ℚ)) :
    SourcePositive (positiveLaw alphabet) := by
  exact SequentialSourceCode.selectedSource_positive alphabet
    (alphabet.map Prod.snd)

theorem positiveLaw_mass_moments {Y : Type*}
    (alphabet : Array (Y × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2)) = true)
    {n : Nat} (φ : Y → Fin n → ℚ) :
    sourceMass alphabet = sourceMass (positiveLaw alphabet) ∧
      ∀ j : Fin n,
        sourceMoment φ alphabet j = sourceMoment φ (positiveLaw alphabet) j := by
  have hw : (alphabet.map Prod.snd).all (fun w => decide (0 ≤ w)) = true := by
    simpa [Array.all_map] using hnonneg
  have hs : sameMoments (featureRows n φ alphabet)
      (alphabet.map Prod.snd) (alphabet.map Prod.snd) = true := by
    simp [sameMoments]
  have hc := SequentialZeroDeletion.retainedSource_moments n φ alphabet
    (alphabet.map Prod.snd) hw hs
  exact (sourceMomentsCheck_spec n φ alphabet (positiveLaw alphabet)).mp hc

theorem positiveLaw_nonempty {Y : Type*}
    (alphabet : Array (Y × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2)) = true)
    (hmass : sourceMass alphabet = 1) :
    0 < (positiveLaw alphabet).size := by
  have hm := (positiveLaw_mass_moments alphabet hnonneg
    (n := 0) (fun _ j => Fin.elim0 j)).1
  by_contra hn
  have hz : (positiveLaw alphabet).size = 0 := by omega
  have he : positiveLaw alphabet = #[] := Array.size_eq_zero_iff.mp hz
  have hm0 : sourceMass alphabet = 0 := by simpa [he, sourceMass] using hm
  rw [hm0] at hmass
  norm_num at hmass

theorem positiveLaw_trace {Y : Type*}
    (alphabet : Array (Y × ℚ))
    (hmass : sourceMass alphabet = 1) :
    ∃ trace : Fin (positiveLaw alphabet).size ↪ Fin alphabet.size,
      (∀ j, (positiveLaw alphabet)[j].1 = alphabet[trace j].1) ∧
      (∀ i : Fin alphabet.size,
        (∃ j, trace j = i) ↔ 0 < alphabet[i].2) := by
  classical
  have hnonempty : 0 < alphabet.size := by
    by_contra hn
    have hz : alphabet.size = 0 := by omega
    have he : alphabet = #[] := Array.size_eq_zero_iff.mp hz
    simp [he, sourceMass] at hmass
  letI : Inhabited Y := ⟨alphabet[0].1⟩
  have hs : (alphabet.map Prod.snd).size = alphabet.size := by simp
  obtain ⟨trace, hentry, himage⟩ :=
    selectedSource_trace alphabet (alphabet.map Prod.snd) hs
  refine ⟨trace, ?_, ?_⟩
  · intro j
    simpa [positiveLaw, SequentialZeroDeletion.retainedSource] using
      (congrArg (fun e : Y × ℚ => e.1) (hentry j))
  · intro i
    simpa [positiveLaw, i.isLt] using himage i

private theorem eliminateWeights_size {weights coeff updated : Array ℚ}
    (h : eliminateWeights weights coeff = some updated) :
    updated.size = weights.size := by
  unfold eliminateWeights at h
  cases hr : minimumRatio weights coeff with
  | none => simp [hr] at h
  | some ratio =>
      simp [hr] at h
      cases h
      simp

/-- A successful call of the old checked update has a concrete, injective
trace into precisely the strictly positive updated positions. -/
theorem compressOnce_trace {α : Type*} [Inhabited α]
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ))
    (h : compressSourceOnceMaterialized n φ source = some out) :
    ∃ updated : Array ℚ,
      ∃ trace : Fin out.size ↪ Fin source.size,
        (∀ j, out[j] =
          (source[trace j].1, updated[(trace j).val]?.getD 0)) ∧
        (∀ i : Fin source.size,
          (∃ j, trace j = i) ↔ 0 < updated[i.val]?.getD 0) := by
  unfold compressSourceOnceMaterialized at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i updated hupdated
      split at h
      · split at h
        · split at h
          · cases h
            have hs : updated.size = source.size := by
              simpa using eliminateWeights_size hupdated
            exact ⟨updated, selectedSource_trace source updated hs⟩
          · cases h
        · cases h
      · cases h

theorem compressOnce_retained {α : Type*} [Inhabited α]
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ))
    (h : compressSourceOnceMaterialized n φ source = some out) :
    Retained source out := by
  obtain ⟨updated, trace, hentry, _⟩ :=
    compressOnce_trace n φ source out h
  refine ⟨trace, ?_⟩
  intro j
  have hlabel := congrArg (fun e : α × ℚ => e.1) (hentry j)
  simpa using hlabel

private theorem retained_refl {α : Type*}
    (source : Array (α × ℚ)) : Retained source source := by
  exact ⟨Function.Embedding.refl _, fun _ => rfl⟩

private theorem retained_trans {α : Type*}
    (source mid out : Array (α × ℚ))
    (hfirst : Retained source mid) (hrest : Retained mid out) :
    Retained source out := by
  obtain ⟨first, hf⟩ := hfirst
  obtain ⟨rest, hr⟩ := hrest
  refine ⟨rest.trans first, ?_⟩
  intro j
  exact (hr j).trans (hf (rest j))

/-- The injection is composed through every actual recursive elimination;
it continues to distinguish original positions when decoded values repeat. -/
theorem compressUntilIndependent_trace {α : Type*} [Inhabited α]
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel : Nat)
    (h : compressUntilIndependent n φ source fuel = some out) :
    Retained source out := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [hf] at h
          cases h
          exact retained_refl out
      | some f => simp [hf] at h
  | succ fuel ih =>
      simp only [compressUntilIndependent] at h
      cases hf : sourceFreeColumn n φ source with
      | none =>
          simp [hf] at h
          cases h
          exact retained_refl out
      | some f =>
          cases hs : compressSourceOnceMaterialized n φ source with
          | none => simp [hf, hs] at h
          | some next =>
              simp [hf, hs] at h
              exact retained_trans source next out
                (compressOnce_retained n φ source next hs) (ih next h)

/-- At one Code D stage the retained labels inject into actual appended
candidate positions, before any decoded words are identified. -/
theorem sequentialIndependent_stage_trace {Y : Type*}
    [DecidableEq Y] [Inhabited Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (q : Nat) (prev : Array ((Fin q → Y) × ℚ))
    (out : Array ((Fin (q + 1) → Y) × ℚ))
    (hprev : sequentialIndependent D alphabet q = some prev)
    (h : sequentialIndependent D alphabet (q + 1) = some out) :
    Retained (appendSource prev alphabet) out := by
  simp only [sequentialIndependent] at h
  simp [hprev] at h
  exact compressUntilIndependent_trace _ _ _ _ _ h

/-- Every actual append-array position is uniquely its source-position times
the alphabet length plus an alphabet-position. -/
theorem append_position_arithmetic {Y : Type*} {q : Nat}
    (prev : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ))
    (hm : 0 < alphabet.size)
    (i : Fin (appendSource prev alphabet).size) :
    i.val / alphabet.size < prev.size ∧
    i.val % alphabet.size < alphabet.size ∧
    i.val = (i.val / alphabet.size) * alphabet.size +
      i.val % alphabet.size := by
  have hsize := SequentialSourceResource.appendSource_size prev alphabet
  have hi : i.val < prev.size * alphabet.size := by
    simpa [hsize] using i.isLt
  constructor
  · exact (Nat.div_lt_iff_lt_mul hm).2 hi
  constructor
  · exact Nat.mod_lt _ hm
  · simpa only [Nat.mul_comm alphabet.size (i.val / alphabet.size),
      Nat.add_comm] using (Nat.mod_add_div i.val alphabet.size).symm

/-- One deterministic zero-deletion pass followed by the frozen executable
positive-alphabet loop. -/
def sequentialPreprocessed {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (q : Nat) : Option (Array ((Fin q → Y) × ℚ)) :=
  sequentialIndependent D (positiveLaw alphabet) q

theorem sequentialPreprocessed_total {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ)) :
    ∀ q, ∃ out, sequentialPreprocessed D alphabet q = some out ∧
      SourcePositive out := by
  intro q
  exact sequentialIndependent_total D (positiveLaw alphabet)
    (positiveLaw_positive alphabet) q

theorem sequentialPreprocessed_mass {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2)) = true)
    (hmass : sourceMass alphabet = 1)
    (q : Nat) (out : Array ((Fin q → Y) × ℚ))
    (h : sequentialPreprocessed D alphabet q = some out) :
    sourceMass out = 1 := by
  have hp : sourceMass (positiveLaw alphabet) = 1 := by
    rw [← (positiveLaw_mass_moments alphabet hnonneg
      (n := 0) (fun _ j => Fin.elim0 j)).1]
    exact hmass
  exact sequentialIndependent_mass D (positiveLaw alphabet) hp q out h

theorem positiveLaw_pointMass {Y : Type*} [DecidableEq Y]
    (alphabet : Array (Y × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2)) = true)
    (y : Y) :
    alphabetPointMass alphabet y =
      alphabetPointMass (positiveLaw alphabet) y := by
  let φ : Y → Fin 1 → ℚ := fun z _ => if z = y then 1 else 0
  have hm := (positiveLaw_mass_moments alphabet hnonneg φ).2 (0 : Fin 1)
  simpa [alphabetPointMass, SequentialAppendMoments.weightedSum,
    sourceMoment, φ] using hm

theorem positiveLaw_patternTarget {Y : Type*} [DecidableEq Y]
    (alphabet : Array (Y × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2)) = true)
    {q : Nat} (p : Fin q → Option Y) :
    patternTarget alphabet p = patternTarget (positiveLaw alphabet) p := by
  unfold patternTarget
  apply Finset.prod_congr rfl
  intro i _
  cases hp : p i with
  | none => rfl
  | some y => exact positiveLaw_pointMass alphabet hnonneg y

private theorem foldArrayChunks_toList {A B : Type*}
    (xs : List A) (acc : Array B) (f : A → Array B) :
    (xs.foldl (fun out x => out ++ f x) acc).toList =
      acc.toList ++ xs.flatMap (fun x => (f x).toList) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      simp [List.append_assoc]

theorem appendSource_toList {Y : Type*} {q : Nat}
    (prev : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ)) :
    (appendSource prev alphabet).toList =
      prev.toList.flatMap (fun x =>
        alphabet.toList.map (fun y =>
          (appendWord x.1 y.1, x.2 * y.2))) := by
  unfold appendSource
  rw [← Array.foldl_toList]
  simpa [Array.toList_map] using
    (foldArrayChunks_toList prev.toList #[]
      (fun x => alphabet.map (fun y =>
        (appendWord x.1 y.1, x.2 * y.2))))

private theorem fixedChunks_length {A B C : Type*}
    (xs : List A) (ys : List B) (f : A → B → C) :
    (xs.flatMap (fun x => ys.map (f x))).length =
      xs.length * ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, ih, Nat.succ_mul, Nat.add_comm]

private theorem fixedChunks_get {A B C : Type*}
    (xs : List A) (ys : List B) (f : A → B → C)
    (r c : Nat) (hr : r < xs.length) (hc : c < ys.length) :
    (xs.flatMap (fun x => ys.map (f x)))[r * ys.length + c]'(by
      rw [fixedChunks_length]
      have hmul := Nat.mul_le_mul_right ys.length (Nat.succ_le_of_lt hr)
      simp only [Nat.succ_mul] at hmul
      omega) =
      f xs[r] ys[c] := by
  induction xs generalizing r with
  | nil => simp at hr
  | cons x xs ih =>
      cases r with
      | zero =>
          simp [List.flatMap_cons, List.getElem_append_left,
            hc]
      | succ r =>
          have hr' : r < xs.length := by simpa using hr
          have hidx : (r + 1) * ys.length + c =
              ys.length + (r * ys.length + c) := by
            simp only [Nat.succ_mul]
            omega
          simpa [List.flatMap_cons, hidx, ih r hr']

/-- The physical append array is row-major in the retained source position
and then the alphabet position. This equality holds even when decoded words
at different positions happen to be equal. -/
theorem appendSource_get {Y : Type*} {q : Nat}
    (prev : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ))
    (r : Fin prev.size) (c : Fin alphabet.size) :
    (appendSource prev alphabet)[r.val * alphabet.size + c.val]'(by
      rw [SequentialSourceResource.appendSource_size]
      have hmul := Nat.mul_le_mul_right alphabet.size (Nat.succ_le_of_lt r.isLt)
      simp only [Nat.succ_mul] at hmul
      omega) =
      (appendWord prev[r].1 alphabet[c].1,
        prev[r].2 * alphabet[c].2) := by
  have hr : r.val < prev.toList.length := by simpa using r.isLt
  have hc : c.val < alphabet.toList.length := by simpa using c.isLt
  have hlist := fixedChunks_get prev.toList alphabet.toList
    (fun x y => (appendWord x.1 y.1, x.2 * y.2))
    r.val c.val hr hc
  have harray : appendSource prev alphabet =
      (prev.toList.flatMap (fun x => alphabet.toList.map (fun y =>
        (appendWord x.1 y.1, x.2 * y.2)))).toArray := by
    apply Array.toList_inj.mp
    simpa using appendSource_toList prev alphabet
  simpa [harray] using hlist

end CurrentAdditive.LabelTrace
