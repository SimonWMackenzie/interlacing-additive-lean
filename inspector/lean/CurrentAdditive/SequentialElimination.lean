import CurrentAdditive.SequentialCode

namespace CurrentAdditive.SequentialElimination

open SequentialCode
open Finset

private def ratioStep (w a : Nat → ℚ) (best : Option ℚ) (i : Nat) : Option ℚ :=
  if 0 < a i then
    match best with
    | none => some (w i / a i)
    | some previous => some (min previous (w i / a i))
  else best

private def IsMinimum (w a : Nat → ℚ) (seen : List Nat) (best : Option ℚ) : Prop :=
  match best with
  | none => ∀ i ∈ seen, ¬ 0 < a i
  | some t =>
      (∃ i ∈ seen, 0 < a i ∧ t = w i / a i) ∧
      (∀ i ∈ seen, 0 < a i → t ≤ w i / a i)

private theorem minimum_step (w a : Nat → ℚ) (seen : List Nat)
    (best : Option ℚ) (i : Nat)
    (h : IsMinimum w a seen best) :
    IsMinimum w a (seen ++ [i]) (ratioStep w a best i) := by
  cases best with
  | none =>
      have hnone : ∀ j ∈ seen, ¬ 0 < a j := h
      by_cases hi : 0 < a i
      · simp only [ratioStep, hi, ↓reduceIte, IsMinimum]
        constructor
        · exact ⟨i, by simp, hi, rfl⟩
        · intro j hj hjpos
          rcases List.mem_append.mp hj with hj | hj
          · exact False.elim ((hnone j hj) hjpos)
          · have : j = i := by simpa using hj
            subst j
            exact le_rfl
      · simp only [ratioStep, hi, ↓reduceIte, IsMinimum]
        intro j hj
        rcases List.mem_append.mp hj with hj | hj
        · exact hnone j hj
        · have : j = i := by simpa using hj
          subst j
          exact hi
  | some t =>
      obtain ⟨⟨k, hk, hak, htk⟩, hbound⟩ := h
      by_cases hi : 0 < a i
      · by_cases hle : t ≤ w i / a i
        · simp only [ratioStep, hi, ↓reduceIte, min_eq_left hle, IsMinimum]
          constructor
          · exact ⟨k, List.mem_append.mpr (Or.inl hk), hak, htk⟩
          · intro j hj hjpos
            rcases List.mem_append.mp hj with hj | hj
            · exact hbound j hj hjpos
            · have : j = i := by simpa using hj
              subst j
              exact hle
        · have hlt : w i / a i ≤ t := le_of_lt (lt_of_not_ge hle)
          simp only [ratioStep, hi, ↓reduceIte, min_eq_right hlt, IsMinimum]
          constructor
          · exact ⟨i, by simp, hi, rfl⟩
          · intro j hj hjpos
            rcases List.mem_append.mp hj with hj | hj
            · exact le_trans hlt (hbound j hj hjpos)
            · have : j = i := by simpa using hj
              subst j
              exact le_rfl
      · simp only [ratioStep, hi, ↓reduceIte, IsMinimum]
        constructor
        · exact ⟨k, List.mem_append.mpr (Or.inl hk), hak, htk⟩
        · intro j hj hjpos
          rcases List.mem_append.mp hj with hj | hj
          · exact hbound j hj hjpos
          · have : j = i := by simpa using hj
            subst j
            exact False.elim (hi hjpos)

private theorem fold_minimum (w a : Nat → ℚ) (seen todo : List Nat)
    (best : Option ℚ) (h : IsMinimum w a seen best) :
    IsMinimum w a (seen ++ todo) (todo.foldl (ratioStep w a) best) := by
  induction todo generalizing seen best with
  | nil => simpa using h
  | cons i rest ih =>
      simp only [List.foldl_cons]
      have hs := minimum_step w a seen best i h
      simpa only [List.append_assoc] using ih (seen ++ [i]) (ratioStep w a best i) hs

private theorem minimumRatio_isMinimum (weights coeff : Array ℚ) :
    IsMinimum (fun i => weights[i]?.getD 0) (fun i => coeff[i]?.getD 0)
      (List.range (min weights.size coeff.size))
      (minimumRatio weights coeff) := by
  unfold minimumRatio
  change IsMinimum _ _ _
    ((List.range (min weights.size coeff.size)).foldl
      (ratioStep (fun i => weights[i]?.getD 0)
        (fun i => coeff[i]?.getD 0)) none)
  simpa using fold_minimum
    (fun i => weights[i]?.getD 0) (fun i => coeff[i]?.getD 0)
    [] (List.range (min weights.size coeff.size)) none
    (by simp [IsMinimum])

private theorem rangeSum (n : Nat) (f : Nat → ℚ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem array_toList_range (a : Array ℚ) :
    a.toList = (List.range a.size).map (fun i => a[i]?.getD 0) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    have hi' : i < a.size := by simpa using hi
    simp [hi']

theorem minimumRatio_total (weights coeff : Array ℚ)
    (hsize : weights.size = coeff.size)
    (hpositive : ∀ i < weights.size, 0 < weights[i]?.getD 0)
    (hsum : coeff.toList.sum = 0)
    (hnonzero : ∃ i ∈ List.range coeff.size, coeff[i]?.getD 0 ≠ 0) :
    ∃ t, minimumRatio weights coeff = some t ∧ 0 < t ∧
      (∃ i ∈ List.range coeff.size,
        0 < coeff[i]?.getD 0 ∧ t = weights[i]?.getD 0 / coeff[i]?.getD 0) ∧
      (∀ i ∈ List.range coeff.size, 0 < coeff[i]?.getD 0 →
        t ≤ weights[i]?.getD 0 / coeff[i]?.getD 0) := by
  have hsum' :
      ∑ i ∈ Finset.range coeff.size, coeff[i]?.getD 0 = 0 := by
    rw [← rangeSum]
    simpa [array_toList_range] using hsum
  obtain ⟨i, hi, hcoeffpos⟩ :=
    exists_pos_of_sum_zero_of_exists_nonzero
      (fun i => coeff[i]?.getD 0) hsum'
      (by obtain ⟨j, hj, hjne⟩ := hnonzero
          exact ⟨j, Finset.mem_range.mpr (List.mem_range.mp hj), hjne⟩)
  have hir : i ∈ List.range coeff.size := List.mem_range.mpr (Finset.mem_range.mp hi)
  have hmin := minimumRatio_isMinimum weights coeff
  rw [hsize, Nat.min_self] at hmin
  cases ht : minimumRatio weights coeff with
  | none =>
      rw [ht] at hmin
      exact False.elim ((hmin i hir) hcoeffpos)
  | some t =>
      rw [ht] at hmin
      obtain ⟨⟨j, hj, hjpos, htj⟩, hbound⟩ := hmin
      have hjw : j < weights.size := by
        rw [hsize]
        exact List.mem_range.mp hj
      refine ⟨t, rfl, ?_, ⟨j, hj, hjpos, htj⟩, hbound⟩
      rw [htj]
      exact div_pos (hpositive j hjw) hjpos

private theorem sum_update (l : List Nat) (f g : Nat → ℚ) (t : ℚ) :
    (l.map (fun i => f i - t * g i)).sum =
      (l.map f).sum - t * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons i rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem zero_sum_of_constant_row (a : Array (Array ℚ)) (coeff : Array ℚ)
    (hdep : IsDependence a coeff)
    (hrow : ∃ i < a.size, ∀ j < columnCount a, cell a i j = 1) :
    coeff.toList.sum = 0 := by
  obtain ⟨hcoeffsize, _, hrows⟩ := (dependence_spec a coeff).mp hdep
  obtain ⟨i, hi, hone⟩ := hrow
  rw [array_toList_range]
  calc
    ((List.range coeff.size).map (fun j => coeff[j]?.getD 0)).sum =
        ((List.range coeff.size).map
          (fun j => cell a i j * (coeff[j]?.getD 0))).sum := by
          congr 1
          apply List.map_congr_left
          intro j hj
          have hj' : j < columnCount a := by
            rw [← hcoeffsize]
            exact List.mem_range.mp hj
          simp [hone j hj']
    _ = 0 := hrows i (List.mem_range.mpr hi)

theorem eliminateWeights_total
    (a : Array (Array ℚ)) (weights coeff : Array ℚ)
    (hsize : weights.size = columnCount a)
    (hw : ∀ i < weights.size, 0 < weights[i]?.getD 0)
    (hdep : IsDependence a coeff)
    (hsum : coeff.toList.sum = 0) :
    ∃ updated,
      eliminateWeights weights coeff = some updated ∧
      updated.size = weights.size ∧
      updated.all (fun w => decide (0 ≤ w)) = true ∧
      sameMoments a weights updated = true ∧
      (positiveIndices updated).length < weights.size := by
  obtain ⟨hcoeffsize, hnonzero, hrows⟩ := (dependence_spec a coeff).mp hdep
  have hsame : weights.size = coeff.size := hsize.trans hcoeffsize.symm
  obtain ⟨t, ht, htpos, ⟨i₀, hi₀, ha₀, hratio₀⟩, hratio⟩ :=
    minimumRatio_total weights coeff hsame hw hsum hnonzero
  let updated : Array ℚ := Array.ofFn (n := weights.size)
    (fun i => weights[i] - t * (coeff[i.val]?.getD 0))
  have hupdate : eliminateWeights weights coeff = some updated := by
    simp [eliminateWeights, ht, updated]
  have husize : updated.size = weights.size := by simp [updated]
  have hu (i : Nat) (hi : i < weights.size) :
      updated[i]?.getD 0 = weights[i]?.getD 0 - t * (coeff[i]?.getD 0) := by
    simp [updated, hi]
  have hnonneg (i : Nat) (hi : i < weights.size) :
      0 ≤ updated[i]?.getD 0 := by
    rw [hu i hi]
    by_cases hai : 0 < coeff[i]?.getD 0
    · have hi' : i ∈ List.range coeff.size := by
        apply List.mem_range.mpr
        rw [← hsame]
        exact hi
      have hle := hratio i hi' hai
      have hmul : t * (coeff[i]?.getD 0) ≤ weights[i]?.getD 0 := by
        calc
          t * (coeff[i]?.getD 0) ≤
              (weights[i]?.getD 0 / (coeff[i]?.getD 0)) * (coeff[i]?.getD 0) :=
                mul_le_mul_of_nonneg_right hle hai.le
          _ = weights[i]?.getD 0 := div_mul_cancel₀ _ hai.ne'
      exact sub_nonneg.mpr hmul
    · have hai' : coeff[i]?.getD 0 ≤ 0 := le_of_not_gt hai
      have hprod := mul_nonpos_of_nonneg_of_nonpos htpos.le hai'
      linarith [hw i hi]
  have hi₀' : i₀ < weights.size := by
    rw [hsame]
    exact List.mem_range.mp hi₀
  have hu₀ : updated[i₀]?.getD 0 = 0 := by
    rw [hu i₀ hi₀', hratio₀]
    rw [div_mul_cancel₀ _ ha₀.ne']
    ring
  have hall : updated.all (fun w => decide (0 ≤ w)) = true := by
    rw [Array.all_eq_true]
    intro i hi
    have hi' : i < weights.size := by simpa [husize] using hi
    simpa [show updated[i] = updated[i]?.getD 0 by simp [hi]] using hnonneg i hi'
  have hstrict : (positiveIndices updated).length < weights.size := by
    unfold positiveIndices
    rw [← husize]
    have hfilter := (List.length_filter_lt_length_iff_exists
      (l := List.range updated.size)
      (p := fun i => decide (0 < updated[i]?.getD 0))).mpr
      (show ∃ i ∈ List.range updated.size,
        ¬ decide (0 < updated[i]?.getD 0) from
          ⟨i₀, by simpa [husize] using (List.mem_range.mpr hi₀'), by simp [hu₀]⟩)
    simpa using hfilter
  refine ⟨updated, hupdate, husize, hall, ?_, hstrict⟩
  apply (sameMoments_spec a weights updated).2
  constructor
  · exact husize.symm
  constructor
  · rw [array_toList_range weights, array_toList_range updated, husize]
    have hrewrite :
        ((List.range weights.size).map (fun i => updated[i]?.getD 0)).sum =
          ((List.range weights.size).map
            (fun i => weights[i]?.getD 0 - t * (coeff[i]?.getD 0))).sum := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hu i (List.mem_range.mp hi)
    rw [hrewrite, sum_update]
    have hcoeffsum :
        ((List.range weights.size).map (fun i => coeff[i]?.getD 0)).sum = 0 := by
      rw [hsame, ← array_toList_range]
      exact hsum
    simp [hcoeffsum]
  · intro i hi
    unfold rowMoment
    have hrewrite :
        ((List.range updated.size).map
          (fun j => cell a i j * (updated[j]?.getD 0))).sum =
          ((List.range weights.size).map
            (fun j => cell a i j * (weights[j]?.getD 0) -
              t * (cell a i j * (coeff[j]?.getD 0)))).sum := by
      rw [husize]
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [hu j (List.mem_range.mp hj)]
      ring
    rw [hrewrite, sum_update]
    have hcoeffrow :
        ((List.range weights.size).map
          (fun j => cell a i j * (coeff[j]?.getD 0))).sum = 0 := by
      rw [hsame]
      exact hrows i hi
    simp [hcoeffrow]

theorem support_shrink_has_zero (updated : Array ℚ)
    (hnegative : updated.all (fun w => decide (0 ≤ w)) = true)
    (hshrink : (positiveIndices updated).length < updated.size) :
    ∃ i < updated.size, updated[i]?.getD 0 = 0 := by
  have hfilter :
      (List.filter (fun i => decide (0 < updated[i]?.getD 0))
        (List.range updated.size)).length < (List.range updated.size).length := by
    simpa [positiveIndices] using hshrink
  obtain ⟨i, hi, hnotpos⟩ :=
    (List.length_filter_lt_length_iff_exists.mp hfilter)
  have hisize : i < updated.size := List.mem_range.mp hi
  have hnonneg : 0 ≤ updated[i]?.getD 0 := by
    have := (Array.all_eq_true.mp hnegative) i hisize
    simpa [hisize] using this
  have hle : updated[i]?.getD 0 ≤ 0 := by
    simpa using hnotpos
  exact ⟨i, hisize, le_antisymm hle hnonneg⟩

#print axioms minimumRatio_total
#print axioms zero_sum_of_constant_row
#print axioms eliminateWeights_total
#print axioms support_shrink_has_zero

end CurrentAdditive.SequentialElimination
