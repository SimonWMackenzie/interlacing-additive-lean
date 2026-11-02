import CurrentAdditive.SequentialSourceCode

/-!
Exact rational weighted sums for the indexed coordinate append. These are
algebraic identities of the literal array program; they do not identify
array positions with decoded labels.
-/

namespace CurrentAdditive.SequentialAppendMoments

open SequentialCode SequentialSourceCode

def weightedSum {α : Type*} (source : Array (α × ℚ))
    (f : α → ℚ) : ℚ :=
  (source.toList.map (fun x => x.2 * f x.1)).sum

theorem weightedSum_append {α : Type*} (left right : Array (α × ℚ))
    (f : α → ℚ) :
    weightedSum (left ++ right) f =
      weightedSum left f + weightedSum right f := by
  simp [weightedSum, Array.toList_append, List.map_append, List.sum_append]

theorem weightedSum_appendSource {Y : Type*} {q : Nat}
    (source : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ))
    (f : (Fin (q + 1) → Y) → ℚ) :
    weightedSum (appendSource source alphabet) f =
      (source.toList.map (fun x =>
        (alphabet.toList.map (fun y =>
          x.2 * y.2 * f (appendWord x.1 y.1))).sum)).sum := by
  let step : Array ((Fin (q + 1) → Y) × ℚ) →
      ((Fin q → Y) × ℚ) → Array ((Fin (q + 1) → Y) × ℚ) :=
    fun out x => out ++ alphabet.map (fun y =>
      (appendWord x.1 y.1, x.2 * y.2))
  have hfold (xs : List ((Fin q → Y) × ℚ))
      (out : Array ((Fin (q + 1) → Y) × ℚ)) :
      weightedSum (xs.foldl step out) f =
        weightedSum out f +
          (xs.map (fun x =>
            (alphabet.toList.map (fun y =>
              x.2 * y.2 * f (appendWord x.1 y.1))).sum)).sum := by
    induction xs generalizing out with
    | nil => simp
    | cons x xs ih =>
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [ih, weightedSum_append]
        have hchunk :
            weightedSum (alphabet.map (fun y =>
              (appendWord x.1 y.1, x.2 * y.2))) f =
              (alphabet.toList.map (fun y =>
                x.2 * y.2 * f (appendWord x.1 y.1))).sum := by
          simp [weightedSum, Array.toList_map, Function.comp_def]
        rw [hchunk]
        abel
  unfold appendSource
  rw [← Array.foldl_toList]
  simpa [step, weightedSum] using hfold source.toList #[]

theorem sourceMass_eq_weightedSum {α : Type*}
    (source : Array (α × ℚ)) :
    sourceMass source = weightedSum source (fun _ => 1) := by
  simp [sourceMass, weightedSum]

theorem sourceMoment_eq_weightedSum {α : Type*} {n : Nat}
    (source : Array (α × ℚ)) (φ : α → Fin n → ℚ) (j : Fin n) :
    sourceMoment φ source j = weightedSum source (fun x => φ x j) := rfl

theorem appendWord_old {Y : Type*} {q : Nat}
    (v : Fin q → Y) (y : Y) (i : Fin q) :
    appendWord v y ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = v i := by
  simp [appendWord, i.isLt]

theorem appendWord_last {Y : Type*} {q : Nat}
    (v : Fin q → Y) (y : Y) :
    appendWord v y ⟨q, Nat.lt_succ_self q⟩ = y := by
  simp [appendWord]

theorem list_sum_map_mul_left {α : Type*} (xs : List α)
    (h : α → ℚ) (c : ℚ) :
    (xs.map (fun x => c * h x)).sum = c * (xs.map h).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

theorem list_sum_map_mul_right {α : Type*} (xs : List α)
    (h : α → ℚ) (c : ℚ) :
    (xs.map (fun x => h x * c)).sum = (xs.map h).sum * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

theorem weightedSum_appendSource_factor {Y : Type*} {q : Nat}
    (source : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ))
    (f : (Fin q → Y) → ℚ) (g : Y → ℚ) :
    weightedSum (appendSource source alphabet)
      (fun w => f (fun i => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) *
        g (w ⟨q, Nat.lt_succ_self q⟩)) =
      weightedSum source f * weightedSum alphabet g := by
  rw [weightedSum_appendSource]
  have hinner (x : (Fin q → Y) × ℚ) :
      (alphabet.toList.map (fun y =>
        x.2 * y.2 *
          (f (fun i => appendWord x.1 y.1
            ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) *
            g (appendWord x.1 y.1 ⟨q, Nat.lt_succ_self q⟩)))).sum =
        (x.2 * f x.1) * weightedSum alphabet g := by
    have hfun (y : Y) :
        (fun i : Fin q => appendWord x.1 y
          ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) = x.1 := by
      funext i
      exact appendWord_old x.1 y i
    simp_rw [hfun, appendWord_last]
    have hterm (y : Y × ℚ) : x.2 * y.2 * (f x.1 * g y.1) =
        (x.2 * f x.1) * (y.2 * g y.1) := by ring
    simp_rw [hterm]
    rw [list_sum_map_mul_left]
    rfl
  simp_rw [hinner]
  rw [list_sum_map_mul_right]
  rfl

theorem sourceMass_appendSource {Y : Type*} {q : Nat}
    (source : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ)) :
    sourceMass (appendSource source alphabet) =
      sourceMass source * sourceMass alphabet := by
  rw [sourceMass_eq_weightedSum, sourceMass_eq_weightedSum,
    sourceMass_eq_weightedSum]
  simpa using weightedSum_appendSource_factor source alphabet
    (fun _ => 1) (fun _ => 1)

theorem weightedSum_appendSource_old {Y : Type*} {q : Nat}
    (source : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ))
    (f : (Fin q → Y) → ℚ)
    (halphabet : sourceMass alphabet = 1) :
    weightedSum (appendSource source alphabet)
      (fun w => f (fun i => w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) =
      weightedSum source f := by
  have h := weightedSum_appendSource_factor source alphabet f (fun _ => 1)
  simp only [mul_one] at h
  rw [← sourceMass_eq_weightedSum, halphabet, mul_one] at h
  exact h

theorem weightedSum_appendSource_new {Y : Type*} {q : Nat}
    (source : Array ((Fin q → Y) × ℚ))
    (alphabet : Array (Y × ℚ))
    (g : Y → ℚ)
    (hsource : sourceMass source = 1) :
    weightedSum (appendSource source alphabet)
      (fun w => g (w ⟨q, Nat.lt_succ_self q⟩)) =
      weightedSum alphabet g := by
  have h := weightedSum_appendSource_factor source alphabet (fun _ => 1) g
  simp only [one_mul] at h
  rw [← sourceMass_eq_weightedSum, hsource, one_mul] at h
  exact h

theorem sequentialMaterialized_mass {Y : Type*} [DecidableEq Y]
    (D : Nat) (alphabet : Array (Y × ℚ))
    (halphabet : sourceMass alphabet = 1) :
    ∀ q out, sequentialMaterialized D alphabet q = some out →
      sourceMass out = 1 := by
  intro q
  induction q with
  | zero =>
      intro out hout
      simp only [sequentialMaterialized] at hout
      cases hout
      simp [sourceMass]
  | succ q ih =>
      intro out hout
      simp only [sequentialMaterialized] at hout
      cases hprev : sequentialMaterialized D alphabet q with
      | none => simp [hprev] at hout
      | some prev =>
          simp [hprev] at hout
          have hm := compressSourceFuelMaterialized_moments _ _ _ _ _ hout
          rw [← hm.1, sourceMass_appendSource, ih prev hprev, halphabet]
          ring

private theorem featureAll_append_old {Y : Type*} [DecidableEq Y]
    {q : Nat} (v : Fin q → Y) (y : Y)
    (c : List (Nat × Y))
    (hc : ∀ p ∈ c, p.1 < q) :
    c.all (fun p =>
      if h : p.1 < q + 1 then
        decide (appendWord v y ⟨p.1, h⟩ = p.2)
      else false) =
    c.all (fun p =>
      if h : p.1 < q then decide (v ⟨p.1, h⟩ = p.2)
      else false) := by
  induction c with
  | nil => rfl
  | cons p ps ih =>
      have hp : p.1 < q := hc p (by simp)
      have hps : ∀ a ∈ ps, a.1 < q := by
        intro a ha
        exact hc a (by simp [ha])
      simp only [List.all_cons]
      have hhead :
          (if h : p.1 < q + 1 then
            decide (appendWord v y ⟨p.1, h⟩ = p.2) else false) =
          (if h : p.1 < q then decide (v ⟨p.1, h⟩ = p.2) else false) := by
        simp [hp, Nat.le_of_lt hp, appendWord]
      rw [hhead, ih hps]

theorem generatedFeatureValue_append_old {Y : Type*} [DecidableEq Y]
    {q : Nat} (v : Fin q → Y) (y : Y)
    (c : List (Nat × Y)) (hc : ∀ p ∈ c, p.1 < q) :
    generatedFeatureValue (appendWord v y) c =
      generatedFeatureValue v c := by
  simp only [generatedFeatureValue]
  rw [featureAll_append_old v y c hc]

theorem generatedFeatureValue_append_new {Y : Type*} [DecidableEq Y]
    {q : Nat} (v : Fin q → Y) (y y₀ : Y)
    (c : List (Nat × Y)) (hc : ∀ p ∈ c, p.1 < q) :
    generatedFeatureValue (appendWord v y) ((q, y₀) :: c) =
      generatedFeatureValue v c * (if y = y₀ then 1 else 0) := by
  simp only [generatedFeatureValue, List.all_cons]
  have hold := featureAll_append_old v y c hc
  simp only [appendWord_last] at *
  rw [hold]
  have hq : q < q + 1 := by omega
  simp only [dif_pos hq]
  by_cases hy : y = y₀
  · subst y₀
    have hdec : decide (y = y) = true := by simp
    rw [hdec]
    cases hbool : (c.all fun p =>
      if h : p.1 < q then decide (v ⟨p.1, h⟩ = p.2) else false) <;>
      simp
  · simp [hy]

#print axioms weightedSum_appendSource_factor
#print axioms sourceMass_appendSource
#print axioms sequentialMaterialized_mass
#print axioms generatedFeatureValue_append_old
#print axioms generatedFeatureValue_append_new

end CurrentAdditive.SequentialAppendMoments
