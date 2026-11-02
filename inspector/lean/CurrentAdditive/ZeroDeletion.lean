import CurrentAdditive.SequentialElimination

namespace CurrentAdditive.SequentialZeroDeletion

open SequentialCode

private theorem array_map_sum_range {α : Type*} (source : Array α) (f : α → ℚ) :
    (source.toList.map f).sum =
      ((List.range source.size).map
        (fun i => (source[i]?).elim 0 f)).sum := by
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    have hi' : i < source.size := by simpa using hi
    simp [hi']

private theorem array_toList_range (a : Array ℚ) :
    a.toList = (List.range a.size).map (fun i => a[i]?.getD 0) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    have hi' : i < a.size := by simpa using hi
    simp [hi']

private theorem filterMap_sum {α β : Type*} (l : List α)
    (f : α → Option β) (g : β → ℚ) :
    ((l.filterMap f).map g).sum =
      (l.map (fun i => (f i).elim 0 g)).sum := by
  induction l with
  | nil => simp
  | cons i rest ih =>
      cases h : f i with
      | none => simp [h, ih]
      | some v => simp [h, ih]

private theorem filter_sum_eq {α : Type*} (l : List α) (p : α → Bool)
    (f : α → ℚ) (hzero : ∀ i ∈ l, p i = false → f i = 0) :
    ((l.filter p).map f).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons i rest ih =>
      have hrest : ∀ j ∈ rest, p j = false → f j = 0 := by
        intro j hj
        exact hzero j (List.mem_cons_of_mem i hj)
      by_cases hp : p i = true
      · simp [hp, ih hrest]
      · have hp' : p i = false := Bool.eq_false_iff.mpr hp
        simp [hp', hzero i (by simp) hp', ih hrest]

/-- Filtering strictly positive updated weights preserves every weighted
sum, because nonnegative weights outside the filter are exactly zero. -/
private theorem positive_filter_sum (updated : Array ℚ) (f : Nat → ℚ)
    (hnonneg : updated.all (fun w => decide (0 ≤ w)) = true) :
    (((positiveIndices updated).map
      (fun i => updated[i]?.getD 0 * f i)).sum) =
      (((List.range updated.size).map
        (fun i => updated[i]?.getD 0 * f i)).sum) := by
  unfold positiveIndices
  apply filter_sum_eq
  intro i hi hnotpos
  have hisize : i < updated.size := List.mem_range.mp hi
  have hge : 0 ≤ updated[i]?.getD 0 := by
    have h := (Array.all_eq_true.mp hnonneg) i hisize
    simpa [hisize] using h
  have hle : updated[i]?.getD 0 ≤ 0 := by
    have : ¬ 0 < updated[i]?.getD 0 := by simpa using hnotpos
    exact le_of_not_gt this
  simp [le_antisymm hle hge]

def retainedSource {α : Type*} (source : Array (α × ℚ))
    (updated : Array ℚ) : Array (α × ℚ) :=
  ((positiveIndices updated).filterMap (fun i =>
    (source[i]?).map (fun entry => (entry.1, updated[i]?.getD 0)))).toArray

private theorem retained_sum {α : Type*} (source : Array (α × ℚ))
    (updated : Array ℚ) (ψ : α → ℚ)
    (hnonneg : updated.all (fun w => decide (0 ≤ w)) = true) :
    ((retainedSource source updated).toList.map
      (fun e => e.2 * ψ e.1)).sum =
    ((List.range updated.size).map
      (fun i => updated[i]?.getD 0 *
        (source[i]?).elim 0 (fun e => ψ e.1))).sum := by
  unfold retainedSource
  rw [filterMap_sum]
  have hpoint (i : Nat) :
      (((source[i]?).map
          (fun entry => (entry.1, updated[i]?.getD 0))).elim 0
            (fun e => e.2 * ψ e.1)) =
        updated[i]?.getD 0 * (source[i]?).elim 0 (fun e => ψ e.1) := by
    cases h : source[i]? with
    | none => simp
    | some e => simp
  simp_rw [hpoint]
  exact positive_filter_sum updated
    (fun i => (source[i]?).elim 0 (fun e => ψ e.1)) hnonneg

private theorem source_weight_get {α : Type*} (source : Array (α × ℚ))
    (i : Nat) (hi : i < source.size) :
    (source.map Prod.snd)[i]?.getD 0 = (source[i]).2 := by
  simp [hi]

private theorem feature_cell {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source : Array (α × ℚ))
    (j i : Nat) (hj : j < n) (hi : i < source.size) :
    cell (featureRows n φ source) j i =
      φ (source[i]).1 ⟨j, hj⟩ := by
  simp [cell, featureRows, hj, hi]

private theorem full_sum_eq_mass {α : Type*} (source : Array (α × ℚ))
    (updated : Array ℚ) (hsize : updated.size = source.size) :
    ((List.range updated.size).map
      (fun i => updated[i]?.getD 0 *
        (source[i]?).elim 0 (fun _ => (1 : ℚ)))).sum =
      updated.toList.sum := by
  rw [array_toList_range]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < source.size := by rw [← hsize]; exact List.mem_range.mp hi
  simp [hi']

private theorem source_mass_eq_weights {α : Type*}
    (source : Array (α × ℚ)) :
    sourceMass source = (source.map Prod.snd).toList.sum := by
  simp [sourceMass]

private theorem source_moment_eq_row {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source : Array (α × ℚ))
    (j : Fin n) :
    sourceMoment φ source j =
      rowMoment (featureRows n φ source) (source.map Prod.snd) j.val := by
  rw [sourceMoment, array_map_sum_range]
  unfold rowMoment
  simp only [Array.size_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < source.size := List.mem_range.mp hi
  simp [hi', feature_cell n φ source j.val i j.isLt hi']
  ring

private theorem full_sum_eq_row {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source : Array (α × ℚ))
    (updated : Array ℚ) (j : Fin n)
    (hsize : updated.size = source.size) :
    ((List.range updated.size).map
      (fun i => updated[i]?.getD 0 *
        (source[i]?).elim 0 (fun e => φ e.1 j))).sum =
      rowMoment (featureRows n φ source) updated j.val := by
  unfold rowMoment
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < source.size := by rw [← hsize]; exact List.mem_range.mp hi
  simp [hi', feature_cell n φ source j.val i j.isLt hi', mul_comm]

/-- The exact indexed zero-deletion expression used by `compressSourceOnce`
passes the existing executable source-moment check. Equal decoded labels are
never identified: the proof sums over array positions. -/
theorem retainedSource_moments {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source : Array (α × ℚ))
    (updated : Array ℚ)
    (hnonneg : updated.all (fun w => decide (0 ≤ w)) = true)
    (hsame : sameMoments (featureRows n φ source)
      (source.map Prod.snd) updated = true) :
    sourceMomentsCheck n φ source (retainedSource source updated) = true := by
  obtain ⟨hsize, hmass, hrows⟩ :=
    (sameMoments_spec (featureRows n φ source)
      (source.map Prod.snd) updated).mp hsame
  have huSize : updated.size = source.size := by
    simpa using hsize.symm
  apply (sourceMomentsCheck_spec n φ source
    (retainedSource source updated)).2
  constructor
  · calc
      sourceMass source = (source.map Prod.snd).toList.sum :=
        source_mass_eq_weights source
      _ = updated.toList.sum := hmass
      _ = sourceMass (retainedSource source updated) := by
        rw [sourceMass]
        calc
          updated.toList.sum =
              ((List.range updated.size).map
                (fun i => updated[i]?.getD 0 *
                  (source[i]?).elim 0 (fun _ => (1 : ℚ)))).sum :=
                    (full_sum_eq_mass source updated huSize).symm
          _ = ((retainedSource source updated).toList.map
                (fun e => e.2 * (1 : ℚ))).sum :=
                    (retained_sum source updated (fun _ => 1) hnonneg).symm
          _ = ((retainedSource source updated).toList.map Prod.snd).sum := by
            congr 1
            apply List.map_congr_left
            intro e _
            ring
  · intro j
    calc
      sourceMoment φ source j =
          rowMoment (featureRows n φ source) (source.map Prod.snd) j.val :=
            source_moment_eq_row n φ source j
      _ = rowMoment (featureRows n φ source) updated j.val :=
            hrows j.val (List.mem_range.mpr (by simp [featureRows]))
      _ = ((List.range updated.size).map
            (fun i => updated[i]?.getD 0 *
              (source[i]?).elim 0 (fun e => φ e.1 j))).sum :=
                (full_sum_eq_row n φ source updated j huSize).symm
      _ = sourceMoment φ (retainedSource source updated) j := by
            simpa [sourceMoment] using
              (retained_sum source updated (fun x => φ x j) hnonneg).symm

theorem sourceMomentsCheck_after_positiveIndices {α : Type*} (n : Nat)
    (φ : α → Fin n → ℚ) (source : Array (α × ℚ))
    (updated : Array ℚ)
    (hnonneg : updated.all (fun w => decide (0 ≤ w)) = true)
    (hsame : sameMoments (featureRows n φ source)
      (source.map Prod.snd) updated = true) :
    sourceMomentsCheck n φ source
      (((positiveIndices updated).filterMap (fun i =>
        (source[i]?).map (fun entry =>
          (entry.1, updated[i]?.getD 0)))).toArray) = true := by
  exact retainedSource_moments n φ source updated hnonneg hsame

#print axioms retainedSource_moments
#print axioms sourceMomentsCheck_after_positiveIndices

end CurrentAdditive.SequentialZeroDeletion
