import CurrentAdditive.DeterministicCodeDActualSourceSize
import Mathlib.Tactic

/-! The actual support-deletion step retains labels from its input array. -/

namespace CurrentAdditive.DeterministicSequentialLabelSupport

open CurrentAdditive.SequentialSourceCode
open CurrentAdditive.SequentialCode

def AllLabels {α : Type*} (P : α → Prop) (source : Array (α × ℚ)) : Prop :=
  ∀ entry ∈ source.toList, P entry.1

private theorem selectedLabels {α : Type*} (P : α → Prop)
    (source : Array (α × ℚ)) (updated : Array ℚ)
    (hsource : AllLabels P source) :
    AllLabels P
      ((positiveIndices updated).filterMap (fun i =>
        (source[i]?).map (fun entry =>
          (entry.1, updated[i]?.getD 0)))).toArray := by
  intro entry he
  have hlist : entry ∈ (positiveIndices updated).filterMap (fun i =>
      (source[i]?).map (fun e => (e.1, updated[i]?.getD 0))) := by
    simpa using he
  obtain ⟨i, hi, hmap⟩ := List.mem_filterMap.mp hlist
  cases hs : source[i]? with
  | none => simp [hs] at hmap
  | some old =>
      simp [hs] at hmap
      subst entry
      have his : i < source.size := by
        by_contra h
        have hn : source[i]? = none := by simp [Nat.not_lt.mp h]
        rw [hn] at hs
        cases hs
      have hget : source[i] = old := by
        simpa [Array.getElem?_eq_getElem his] using hs
      apply hsource old
      simpa [hget] using (Array.getElem_mem_toList his : source[i] ∈ source.toList)

theorem compressOnce_labels {α : Type*} (P : α → Prop)
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ))
    (hsource : AllLabels P source)
    (hrun : compressSourceOnceMaterialized n φ source = some out) :
    AllLabels P out := by
  unfold compressSourceOnceMaterialized at hrun
  dsimp only at hrun
  split at hrun
  · cases hrun
  · split at hrun
    · cases hrun
    · split at hrun
      · split at hrun
        · split at hrun
          · cases hrun
            exact selectedLabels P source _ hsource
          · cases hrun
        · cases hrun
      · cases hrun

theorem compressFuel_labels {α : Type*} (P : α → Prop)
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel : Nat)
    (hsource : AllLabels P source)
    (hrun : compressSourceFuelMaterialized n φ source fuel = some out) :
    AllLabels P out := by
  induction fuel generalizing source with
  | zero =>
      simp only [compressSourceFuelMaterialized] at hrun
      split_ifs at hrun
      cases hrun
      exact hsource
  | succ fuel ih =>
      simp only [compressSourceFuelMaterialized] at hrun
      split_ifs at hrun
      · cases hrun
        exact hsource
      · cases hstep : compressSourceOnceMaterialized n φ source with
        | none => simp [hstep] at hrun
        | some next =>
            simp [hstep] at hrun
            exact ih next (compressOnce_labels P n φ source next hsource hstep) hrun

def WordBound (q M : Nat) (v : Fin q → Nat) : Prop :=
  ∀ j : Fin q, v j < M

theorem appendWord_bound {q M : Nat} (v : Fin q → Nat) (y : Nat)
    (hv : WordBound q M v) (hy : y < M) :
    WordBound (q + 1) M (appendWord v y) := by
  intro j
  by_cases hj : j.val < q
  · simpa [appendWord, hj] using hv ⟨j.val, hj⟩
  · simpa [appendWord, hj] using hy

theorem appendSource_labels {q M : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (alphabet : Array (Nat × ℚ))
    (hs : AllLabels (WordBound q M) source)
    (ha : ∀ e ∈ alphabet.toList, e.1 < M) :
    AllLabels (WordBound (q + 1) M) (appendSource source alphabet) := by
  have hchunk (x : (Fin q → Nat) × ℚ)
      (hx : WordBound q M x.1) :
      AllLabels (WordBound (q + 1) M)
        (alphabet.map (fun y => (appendWord x.1 y.1, x.2 * y.2))) := by
    intro e he
    simp only [Array.toList_map] at he
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
    exact appendWord_bound x.1 y.1 hx (ha y hy)
  have hfold (l : List ((Fin q → Nat) × ℚ))
      (hl : ∀ x ∈ l, WordBound q M x.1)
      (acc : Array ((Fin (q + 1) → Nat) × ℚ))
      (hacc : AllLabels (WordBound (q + 1) M) acc) :
      AllLabels (WordBound (q + 1) M)
        (l.foldl (fun out x =>
          out ++ alphabet.map (fun y =>
            (appendWord x.1 y.1, x.2 * y.2))) acc) := by
    induction l generalizing acc with
    | nil => simpa using hacc
    | cons x xs ih =>
        have hx : WordBound q M x.1 := hl x (by simp)
        have hxs : ∀ y ∈ xs, WordBound q M y.1 := by
          intro y hy
          exact hl y (by simp [hy])
        have hnew : AllLabels (WordBound (q + 1) M)
            (acc ++ alphabet.map (fun y =>
              (appendWord x.1 y.1, x.2 * y.2))) := by
          intro e he
          simp only [Array.toList_append, List.mem_append] at he
          rcases he with he | he
          · exact hacc e he
          · exact hchunk x hx e he
        simpa [List.foldl_cons] using ih hxs _ hnew
  unfold appendSource
  rw [← Array.foldl_toList]
  exact hfold source.toList hs #[] (by intro e he; simp at he)

theorem sequentialMaterialized_labels (D : Nat)
    (alphabet : Array (Nat × ℚ)) (M : Nat)
    (ha : ∀ e ∈ alphabet.toList, e.1 < M) :
    ∀ q out, sequentialMaterialized D alphabet q = some out →
      AllLabels (WordBound q M) out := by
  intro q
  induction q with
  | zero =>
      intro out hrun
      simp only [sequentialMaterialized] at hrun
      cases hrun
      intro e he
      intro j
      exact Fin.elim0 j
  | succ q ih =>
      intro out hrun
      simp only [sequentialMaterialized] at hrun
      cases hprev : sequentialMaterialized D alphabet q with
      | none => simp [hprev] at hrun
      | some prev =>
          simp [hprev] at hrun
          exact compressFuel_labels (WordBound (q + 1) M) _ _ _ _ _
            (appendSource_labels prev alphabet (ih prev hprev) ha) hrun

#print axioms compressFuel_labels
#print axioms sequentialMaterialized_labels

end CurrentAdditive.DeterministicSequentialLabelSupport
