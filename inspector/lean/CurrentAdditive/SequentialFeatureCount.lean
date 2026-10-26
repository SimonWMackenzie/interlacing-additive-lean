import CurrentAdditive.SequentialSourceResource

/-! Exact count of the literal cylinder-feature enumeration. -/

namespace CurrentAdditive.SequentialFeatureCount

open SequentialCode SequentialSourceResource

def lengthCount {Y : Type*} (features : Array (List (Nat × Y)))
    (k : Nat) : Nat :=
  features.toList.countP (fun c => decide (c.length = k))

private theorem fold_append_map_lengthCount {Y : Type*}
    (alphabet : Array Y) (j k : Nat)
    (xs : List (List (Nat × Y)))
    (out : Array (List (Nat × Y))) :
    lengthCount (xs.foldl
      (fun acc c => acc ++ alphabet.map (fun y => (j, y) :: c)) out) k =
    lengthCount out k +
      xs.countP (fun c => decide (c.length + 1 = k)) * alphabet.size := by
  induction xs generalizing out with
  | nil => simp [lengthCount]
  | cons c xs ih =>
      simp only [List.foldl_cons, List.countP_cons]
      rw [ih]
      have hmap : lengthCount (alphabet.map (fun y => (j, y) :: c)) k =
          (if c.length + 1 = k then alphabet.size else 0) := by
        unfold lengthCount
        simp only [Array.toList_map, List.countP_map]
        by_cases hc : c.length + 1 = k
        · simp [Function.comp_def, hc]
        · simp [Function.comp_def, hc]
      have happ : lengthCount (out ++ alphabet.map (fun y => (j, y) :: c)) k =
          lengthCount out k + lengthCount (alphabet.map (fun y => (j, y) :: c)) k := by
        simp [lengthCount, List.countP_append]
      rw [happ, hmap]
      by_cases hc : c.length + 1 = k
      · simp [hc]
        ring
      · simp [hc]

theorem extendFeatures_lengthCount {Y : Type*}
    (D : Nat) (alphabet : Array Y) (j k : Nat)
    (features : Array (List (Nat × Y))) :
    lengthCount (extendFeatures D alphabet j features) k =
      lengthCount features k +
        features.toList.countP (fun c =>
          decide (c.length + 1 = k) && decide (c.length < D)) * alphabet.size := by
  unfold extendFeatures
  have hfold : lengthCount
      (Array.foldl (fun out c => out ++ alphabet.map (fun y => (j, y) :: c)) #[]
        (features.filter (fun c => decide (c.length < D)))) k =
      lengthCount (#[ ] : Array (List (Nat × Y))) k +
        (features.filter (fun c => decide (c.length < D))).toList.countP
          (fun c => decide (c.length + 1 = k)) * alphabet.size := by
    rw [← Array.foldl_toList]
    exact fold_append_map_lengthCount alphabet j k _ _
  have happ : lengthCount (features ++
      Array.foldl (fun out c => out ++ alphabet.map (fun y => (j, y) :: c)) #[]
        (features.filter (fun c => decide (c.length < D)))) k =
      lengthCount features k +
        lengthCount (Array.foldl
          (fun out c => out ++ alphabet.map (fun y => (j, y) :: c)) #[]
          (features.filter (fun c => decide (c.length < D)))) k := by
    simp [lengthCount, List.countP_append]
  rw [happ, hfold]
  simp [lengthCount, List.countP_filter,
    Bool.and_comm]

theorem extendFeatures_lengthCount_zero {Y : Type*}
    (D : Nat) (alphabet : Array Y) (j : Nat)
    (features : Array (List (Nat × Y))) :
    lengthCount (extendFeatures D alphabet j features) 0 =
      lengthCount features 0 := by
  rw [extendFeatures_lengthCount]
  have hfalse : (fun c : List (Nat × Y) =>
      decide (c.length + 1 = 0) && decide (c.length < D)) =
      (fun _ => false) := by
    funext c
    have hne : c.length + 1 ≠ 0 := by omega
    simp
  rw [hfalse]
  simp

theorem extendFeatures_lengthCount_succ_le {Y : Type*}
    (D : Nat) (alphabet : Array Y) (j k : Nat)
    (features : Array (List (Nat × Y))) (hk : k + 1 ≤ D) :
    lengthCount (extendFeatures D alphabet j features) (k + 1) =
      lengthCount features (k + 1) +
        lengthCount features k * alphabet.size := by
  rw [extendFeatures_lengthCount]
  have hbool : (fun c : List (Nat × Y) =>
      decide (c.length + 1 = k + 1) && decide (c.length < D)) =
      (fun c => decide (c.length = k)) := by
    funext c
    by_cases heq : c.length = k
    · have hk' : k < D := by omega
      simp [heq, hk']
    · have hne : c.length + 1 ≠ k + 1 := by omega
      simp only [hne, decide_false, Bool.false_and, heq]
  rw [hbool]
  rfl

theorem extendFeatures_lengthCount_succ_gt {Y : Type*}
    (D : Nat) (alphabet : Array Y) (j k : Nat)
    (features : Array (List (Nat × Y))) (hk : D < k + 1) :
    lengthCount (extendFeatures D alphabet j features) (k + 1) =
      lengthCount features (k + 1) := by
  rw [extendFeatures_lengthCount]
  have hzero : features.toList.countP (fun c =>
      decide (c.length + 1 = k + 1) && decide (c.length < D)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro c hc htrue
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htrue
    omega
  rw [hzero]
  simp

theorem generatedFeatures_lengthCount {Y : Type*}
    (q D k : Nat) (alphabet : Array Y) :
    lengthCount (generatedFeatures q D alphabet) k =
      if k ≤ D then q.choose k * alphabet.size ^ k else 0 := by
  induction q generalizing k with
  | zero =>
      cases k with
      | zero => simp [generatedFeatures, lengthCount]
      | succ k => simp [generatedFeatures, lengthCount]
  | succ q ih =>
      rw [SequentialFeatureCoverage.generatedFeatures_succ]
      cases k with
      | zero =>
          rw [extendFeatures_lengthCount_zero, ih]
          simp
      | succ k =>
          by_cases hk : k + 1 ≤ D
          · rw [extendFeatures_lengthCount_succ_le D alphabet q k _ hk,
                ih (k + 1), ih k]
            have hkprev : k ≤ D := by omega
            simp only [if_pos hk, if_pos hkprev]
            rw [Nat.choose_succ_succ, pow_succ]
            ring
          · have hgt : D < k + 1 := by omega
            rw [extendFeatures_lengthCount_succ_gt D alphabet q k _ hgt,
              ih (k + 1)]
            simp [hk]

theorem generatedFeatures_length_le {Y : Type*}
    (q D : Nat) (alphabet : Array Y)
    (c : List (Nat × Y))
    (hc : c ∈ (generatedFeatures q D alphabet).toList) :
    c.length ≤ D := by
  by_contra hnot
  have hgt : D < c.length := by omega
  have hcount := generatedFeatures_lengthCount q D c.length alphabet
  have hzero : lengthCount (generatedFeatures q D alphabet) c.length = 0 := by
    simpa [hgt.not_ge] using hcount
  have hall := (List.countP_eq_zero.mp hzero) c hc
  simp at hall

private theorem list_length_eq_sum_count {α : Type*}
    (xs : List α) (length : α → Nat) (D : Nat)
    (hbound : ∀ x ∈ xs, length x ≤ D) :
    xs.length = ∑ k ∈ Finset.range (D + 1),
      xs.countP (fun x => decide (length x = k)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : length x ≤ D := hbound x (by simp)
      have htail : ∀ y ∈ xs, length y ≤ D := by
        intro y hy
        exact hbound y (by simp [hy])
      have hsum :
          (∑ k ∈ Finset.range (D + 1),
              (if length x = k then (1 : Nat) else 0)) = 1 := by
        rw [Finset.sum_ite_eq]
        simp [Finset.mem_range, hx]
      simp only [List.length_cons, List.countP_cons, decide_eq_true_eq]
      rw [Finset.sum_add_distrib]
      rw [← ih htail, hsum]

theorem generatedFeatures_size_exact {Y : Type*}
    (q D : Nat) (alphabet : Array Y) :
    (generatedFeatures q D alphabet).size =
      ∑ k ∈ Finset.range (D + 1), q.choose k * alphabet.size ^ k := by
  have hlength := list_length_eq_sum_count
    (generatedFeatures q D alphabet).toList List.length D
    (by
      intro c hc
      exact generatedFeatures_length_le q D alphabet c hc)
  calc
    (generatedFeatures q D alphabet).size =
        ∑ k ∈ Finset.range (D + 1),
          (generatedFeatures q D alphabet).toList.countP
            (fun x => decide (x.length = k)) := by
          simpa only [Array.length_toList] using hlength
    _ = ∑ k ∈ Finset.range (D + 1),
          q.choose k * alphabet.size ^ k := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkle : k ≤ D := by
            have := Finset.mem_range.mp hk
            omega
          simpa [lengthCount, hkle] using
            (generatedFeatures_lengthCount q D k alphabet)

theorem generatedFeatures_size_min {Y : Type*}
    (q D : Nat) (alphabet : Array Y) :
    (generatedFeatures q D alphabet).size =
      ∑ k ∈ Finset.range (min D q + 1),
        q.choose k * alphabet.size ^ k := by
  rw [generatedFeatures_size_exact]
  by_cases hDq : D ≤ q
  · rw [Nat.min_eq_left hDq]
  · have hqD : q ≤ D := by omega
    rw [Nat.min_eq_right hqD]
    have htail :
        (∑ k ∈ Finset.Ico (q + 1) (D + 1),
          q.choose k * alphabet.size ^ k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hqk : q < k := by
        have := (Finset.mem_Ico.mp hk).1
        omega
      simp [Nat.choose_eq_zero_of_lt hqk]
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun k => q.choose k * alphabet.size ^ k)
      (show q + 1 ≤ D + 1 by omega)
    rw [htail, add_zero] at hsplit
    exact hsplit.symm

#print axioms generatedFeatures_lengthCount
#print axioms generatedFeatures_length_le
#print axioms generatedFeatures_size_exact
#print axioms generatedFeatures_size_min

end CurrentAdditive.SequentialFeatureCount
