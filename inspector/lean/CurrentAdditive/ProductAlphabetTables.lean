import CurrentAdditive.AlphabetTableBuilders

/-! The literal Cartesian-product array for the inner and outer laws. -/

namespace CurrentAdditive.ExecutableCodeSource

open Paper2 SequentialCode SequentialSourceCode SequentialAppendMoments
  SequentialFeatureCoverage

private theorem fold_append_toList {α β : Type*}
    (xs : List α) (acc : Array β) (f : α → Array β) :
    (xs.foldl (fun out x => out ++ f x) acc).toList =
      acc.toList ++ xs.flatMap (fun x => (f x).toList) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih, Array.toList_append]
      simp [List.append_assoc]

theorem appendWeighted_toList {A B : Type*}
    (left : Array (A × ℚ)) (right : Array (B × ℚ)) :
    (appendWeighted left right).toList =
      left.toList.flatMap (fun x => right.toList.map
        (fun y => ((x.1, y.1), x.2 * y.2))) := by
  unfold appendWeighted
  rw [← Array.foldl_toList]
  simpa [Array.toList_map] using
    (fold_append_toList left.toList (#[] : Array ((A × B) × ℚ))
      (fun x => right.map (fun y => ((x.1, y.1), x.2 * y.2))))

theorem appendWeighted_mem {A B : Type*}
    (left : Array (A × ℚ)) (right : Array (B × ℚ))
    (x : A × ℚ) (y : B × ℚ)
    (hx : x ∈ left.toList) (hy : y ∈ right.toList) :
    ((x.1, y.1), x.2 * y.2) ∈ (appendWeighted left right).toList := by
  rw [appendWeighted_toList]
  apply List.mem_flatMap.mpr
  refine ⟨x, hx, ?_⟩
  exact List.mem_map.mpr ⟨y, hy, rfl⟩

theorem appendWeighted_positive {A B : Type*}
    (left : Array (A × ℚ)) (right : Array (B × ℚ))
    (hleft : SourcePositive left) (hright : SourcePositive right) :
    SourcePositive (appendWeighted left right) := by
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro entry hentry
  have hlist : entry ∈ (appendWeighted left right).toList := by simpa using hentry
  rw [appendWeighted_toList] at hlist
  obtain ⟨x, hx, hxmap⟩ := List.mem_flatMap.mp hlist
  obtain ⟨y, hy, heq⟩ := List.mem_map.mp hxmap
  subst entry
  have hxpos : 0 < x.2 := by
    have := (Array.all_eq_true_iff_forall_mem.mp hleft) x (by simpa using hx)
    simpa [SourcePositive] using this
  have hypos : 0 < y.2 := by
    have := (Array.all_eq_true_iff_forall_mem.mp hright) y (by simpa using hy)
    simpa [SourcePositive] using this
  simp [mul_pos hxpos hypos]

theorem appendWeighted_weightedSum {A B : Type*}
    (left : Array (A × ℚ)) (right : Array (B × ℚ))
    (f : A → ℚ) (g : B → ℚ) :
    weightedSum (appendWeighted left right)
      (fun p => f p.1 * g p.2) =
    weightedSum left f * weightedSum right g := by
  let step : Array ((A × B) × ℚ) → (A × ℚ) → Array ((A × B) × ℚ) :=
    fun acc x => acc ++ right.map (fun y => ((x.1, y.1), x.2 * y.2))
  have hfold (xs : List (A × ℚ)) (acc : Array ((A × B) × ℚ)) :
      weightedSum (xs.foldl step acc) (fun p => f p.1 * g p.2) =
        weightedSum acc (fun p => f p.1 * g p.2) +
          (xs.map (fun x =>
            (right.toList.map (fun y => x.2 * y.2 * (f x.1 * g y.1))).sum)).sum := by
    induction xs generalizing acc with
    | nil => simp
    | cons x xs ih =>
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [ih, weightedSum_append]
        have hchunk :
            weightedSum (right.map (fun y => ((x.1, y.1), x.2 * y.2)))
              (fun p => f p.1 * g p.2) =
              (right.toList.map (fun y => x.2 * y.2 * (f x.1 * g y.1))).sum := by
          simp [weightedSum, Array.toList_map, Function.comp_def]
        rw [hchunk]
        abel
  have hmain : weightedSum (appendWeighted left right)
        (fun p => f p.1 * g p.2) =
      (left.toList.map (fun x =>
        (right.toList.map (fun y => x.2 * y.2 * (f x.1 * g y.1))).sum)).sum := by
    unfold appendWeighted
    rw [← Array.foldl_toList]
    simpa [step, weightedSum] using hfold left.toList (#[] : Array ((A × B) × ℚ))
  rw [hmain]
  have hinner (x : A × ℚ) :
      (right.toList.map (fun y => x.2 * y.2 * (f x.1 * g y.1))).sum =
        (x.2 * f x.1) * weightedSum right g := by
    have hterm (y : B × ℚ) :
        x.2 * y.2 * (f x.1 * g y.1) =
          (x.2 * f x.1) * (y.2 * g y.1) := by ring
    simp_rw [hterm]
    rw [list_sum_map_mul_left]
    rfl
  simp_rw [hinner]
  rw [list_sum_map_mul_right]
  rfl

theorem appendWeighted_size {A B : Type*}
    (left : Array (A × ℚ)) (right : Array (B × ℚ)) :
    (appendWeighted left right).size = left.size * right.size := by
  let step : Array ((A × B) × ℚ) → (A × ℚ) → Array ((A × B) × ℚ) :=
    fun acc x => acc ++ right.map (fun y => ((x.1, y.1), x.2 * y.2))
  have hfold (xs : List (A × ℚ)) (acc : Array ((A × B) × ℚ)) :
      (xs.foldl step acc).size = acc.size + xs.length * right.size := by
    induction xs generalizing acc with
    | nil => simp
    | cons x xs ih =>
        simp only [List.foldl_cons, List.length_cons]
        rw [ih]
        simp [step, Nat.succ_mul]
        omega
  unfold appendWeighted
  rw [← Array.foldl_toList]
  simpa [step] using hfold left.toList #[]

/-- The entry array is executable; the law index is the existing Paper2
product law, whose definition is declared noncomputable upstream. -/
noncomputable def productTable {A B : Type}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (μA : PositiveRationalLaw A) (μB : PositiveRationalLaw B)
    (left : AlphabetTable A μA) (right : AlphabetTable B μB) :
    AlphabetTable (A × B) (μA.prod μB) where
  entries := appendWeighted left.entries right.entries
  positive := appendWeighted_positive left.entries right.entries
    left.positive right.positive
  normalized := by
    have h := appendWeighted_weightedSum left.entries right.entries
      (fun _ => 1) (fun _ => 1)
    have hm : sourceMass (appendWeighted left.entries right.entries) =
        sourceMass left.entries * sourceMass right.entries := by
      simpa [sourceMass_eq_weightedSum] using h
    rw [hm, left.normalized, right.normalized]
    norm_num
  covers := by
    intro p
    have hleft := left.covers p.1
    rw [Array.toList_map] at hleft
    obtain ⟨a, ha, hae⟩ := List.mem_map.mp hleft
    have hright := right.covers p.2
    rw [Array.toList_map] at hright
    obtain ⟨b, hb, hbe⟩ := List.mem_map.mp hright
    have hentry := appendWeighted_mem left.entries right.entries a b ha hb
    rw [Array.toList_map]
    apply List.mem_map.mpr
    refine ⟨((a.1, b.1), a.2 * b.2), hentry, ?_⟩
    exact Prod.ext hae hbe
  pointMass := by
    intro p
    have hfactor := appendWeighted_weightedSum left.entries right.entries
      (fun a => if a = p.1 then 1 else 0)
      (fun b => if b = p.2 then 1 else 0)
    have hindicator :
        (fun z : A × B => if z = p then (1 : ℚ) else 0) =
        (fun z => (if z.1 = p.1 then 1 else 0) *
          (if z.2 = p.2 then 1 else 0)) := by
      funext z
      by_cases h₁ : z.1 = p.1 <;> by_cases h₂ : z.2 = p.2 <;>
        simp [h₁, h₂, Prod.ext_iff]
    change weightedSum (appendWeighted left.entries right.entries)
      (fun z => if z = p then 1 else 0) = (μA.prod μB).weight p
    rw [hindicator, hfactor]
    change alphabetPointMass left.entries p.1 *
      alphabetPointMass right.entries p.2 = _
    rw [left.pointMass, right.pointMass]
    rfl

#print axioms appendWeighted_size
#print axioms productTable

#print axioms appendWeighted_toList
#print axioms appendWeighted_positive
#print axioms appendWeighted_weightedSum

end CurrentAdditive.ExecutableCodeSource
