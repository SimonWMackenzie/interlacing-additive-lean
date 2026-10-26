import CurrentAdditive.SequentialElimination
import CurrentAdditive.MinimumRatioFoldSemanticJoin

/-! Positive scaling leaves the exact removal update unchanged. This permits
the actual rational Gauss relation to use a positively scaled integer relation
for denominator accounting without changing any retained weight. -/

namespace CurrentAdditive.RatioPositiveScaling

open SequentialCode

def scaled (s : ℚ) (coeff : Array ℚ) : Array ℚ := coeff.map (s * ·)

theorem scaled_get (s : ℚ) (coeff : Array ℚ) (i : Nat) :
    (scaled s coeff)[i]?.getD 0 = s * (coeff[i]?.getD 0) := by
  by_cases hi : i < coeff.size
  · simp [scaled, hi]
  · have hh : ¬ i < (scaled s coeff).size := by simpa [scaled] using hi
    simp [Array.getElem?_eq_none (Nat.le_of_not_gt hi),
      Array.getElem?_eq_none (Nat.le_of_not_gt hh)]

private def step (weights coeff : Array ℚ) (best : Option ℚ) (i : Nat) : Option ℚ :=
  if 0 < coeff[i]?.getD 0 then
    match best with
    | none => some (weights[i]?.getD 0 / coeff[i]?.getD 0)
    | some previous => some (min previous (weights[i]?.getD 0 / coeff[i]?.getD 0))
  else best

theorem step_scaled (weights coeff : Array ℚ) (s : ℚ) (hs : 0 < s)
    (best : Option ℚ) (i : Nat) :
    step weights (scaled s coeff) (best.map (· / s)) i =
      (step weights coeff best i).map (· / s) := by
  have hp : 0 < s * (coeff[i]?.getD 0) ↔ 0 < coeff[i]?.getD 0 :=
    mul_pos_iff_of_pos_left hs
  have hdiv : (weights[i]?.getD 0) / (s * (coeff[i]?.getD 0)) =
      ((weights[i]?.getD 0) / (coeff[i]?.getD 0)) / s := by ring
  unfold step
  rw [scaled_get]
  by_cases hc : 0 < coeff[i]?.getD 0
  · rw [if_pos (hp.mpr hc), if_pos hc]
    cases best with
    | none => simp [hdiv]
    | some p => simp [hdiv, min_div_div_right hs.le]
  · rw [if_neg (fun h => hc (hp.mp h)), if_neg hc]

theorem fold_scaled (weights coeff : Array ℚ) (s : ℚ) (hs : 0 < s)
    (xs : List Nat) (best : Option ℚ) :
    xs.foldl (step weights (scaled s coeff)) (best.map (· / s)) =
      (xs.foldl (step weights coeff) best).map (· / s) := by
  induction xs generalizing best with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons, step_scaled weights coeff s hs]
      exact ih _

theorem minimumRatio_scaled (weights coeff : Array ℚ) (s : ℚ) (hs : 0 < s) :
    minimumRatio weights (scaled s coeff) =
      (minimumRatio weights coeff).map (· / s) := by
  simpa only [minimumRatio, scaled, Array.size_map, step, Option.map_none]
    using fold_scaled weights coeff s hs
      (List.range (min weights.size coeff.size)) none

theorem eliminateWeights_scaled (weights coeff : Array ℚ) (s : ℚ) (hs : 0 < s) :
    eliminateWeights weights (scaled s coeff) = eliminateWeights weights coeff := by
  unfold eliminateWeights
  rw [minimumRatio_scaled weights coeff s hs]
  cases hm : minimumRatio weights coeff with
  | none => rfl
  | some t =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind]
      congr 1
      apply congrArg Array.ofFn
      funext i
      rw [scaled_get]
      congr 1
      field_simp

theorem scaled_eq_of_entrywise (coeff integer : Array ℚ) (s : ℚ)
    (hsize : integer.size = coeff.size)
    (hentry : ∀ i < coeff.size, integer[i]?.getD 0 = s * (coeff[i]?.getD 0)) :
    integer = scaled s coeff := by
  apply Array.ext
  · simpa [scaled] using hsize
  · intro i hi hj
    have hi' : i < coeff.size := by simpa [scaled] using hj
    have h := hentry i hi'
    simpa [hi, hi', scaled] using h

theorem eliminateWeights_integer_relation (weights coeff : Array ℚ)
    (D : Nat) (hD : 0 < D) (z : Fin coeff.size → ℤ)
    (hcoeff : ∀ i : Fin coeff.size,
      coeff[i.val]?.getD 0 = (z i : ℚ) / (D : ℚ)) :
    eliminateWeights weights coeff =
      eliminateWeights weights (Array.ofFn fun i => (z i : ℚ)) := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have he : Array.ofFn (fun i => (z i : ℚ)) = scaled (D : ℚ) coeff := by
    apply scaled_eq_of_entrywise
    · simp
    · intro i hi
      rw [show (Array.ofFn fun i => (z i : ℚ))[i]?.getD 0 =
        (z ⟨i, hi⟩ : ℚ) by simp [hi], hcoeff ⟨i, hi⟩]
      field_simp
  rw [he, eliminateWeights_scaled weights coeff (D : ℚ) hDq]

#print axioms minimumRatio_scaled
#print axioms eliminateWeights_scaled
#print axioms eliminateWeights_integer_relation

end CurrentAdditive.RatioPositiveScaling
