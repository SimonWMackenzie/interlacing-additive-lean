import CurrentAdditive.GaussPivotPrepSearch32

/-! The physical first-hit row and tag agree with the semantic Gauss pivot. -/

namespace CurrentAdditive.GaussPivotSemanticBridge

open EthInapproximability.CurrentPaper
open CurrentAdditive

def mask : List Bool → Nat → List Bool
  | [], _ => []
  | b :: bs, 0 => b :: mask bs 0
  | _ :: bs, r + 1 => false :: mask bs r

theorem selected_mask (flags : List Bool) (r : Nat) :
    GaussFlagSearch.selected flags r = (mask flags r).findIdx? id := by
  induction flags generalizing r with
  | nil => simp [mask, GaussFlagSearch.selected, GaussFlagSearch.firstHit]
  | cons b bs ih =>
      cases r with
      | zero =>
          cases b with
          | true => simp [mask, GaussFlagSearch.selected,
              GaussFlagSearch.firstHit, List.findIdx?_cons]
          | false =>
              simp only [mask, GaussFlagSearch.selected,
                GaussFlagSearch.firstHit, List.findIdx?_cons]
              rw [← ih]
              cases h : GaussFlagSearch.firstHit bs 0 with
              | mk hit idx =>
                  cases hit <;> simp [GaussFlagSearch.selected, h]
      | succ r =>
          simp only [mask, GaussFlagSearch.selected,
            GaussFlagSearch.firstHit, List.findIdx?_cons]
          rw [← ih]
          cases h : GaussFlagSearch.firstHit bs r with
          | mk hit idx =>
              cases hit <;> simp [GaussFlagSearch.selected, h]

theorem mask_finRange {m : Nat} (f : Fin m → Bool) (r : Nat) :
    mask ((List.finRange m).map f) r =
      (List.finRange m).map (fun i => decide (r ≤ i.val) && f i) := by
  induction m generalizing r with
  | zero => simp [mask]
  | succ m ih =>
      rw [List.finRange_succ]
      simp only [List.map_cons, List.map_map]
      cases r with
      | zero =>
          simp only [mask, Nat.zero_le, decide_true, Bool.true_and]
          congr 1
          simpa [Function.comp_def] using ih (fun i => f i.succ) 0
      | succ r =>
          simp only [mask]
          simp [Fin.val_zero]
          congr 1
          simpa [Function.comp_def, Fin.val_succ, Nat.succ_le_succ_iff]
            using ih (fun i => f i.succ) r

theorem selected_eq_findIdx {m : Nat} (f : Fin m → Bool) (r : Nat) :
    GaussFlagSearch.selected ((List.finRange m).map f) r =
      (List.finRange m).findIdx?
        (fun i => decide (r ≤ i.val) && f i) := by
  rw [selected_mask, mask_finRange, List.findIdx?_map]
  rfl

theorem finRange_find_value {m : Nat} (p : Fin m → Bool) :
    Option.map Fin.val ((List.finRange m).find? p) =
      (List.finRange m).findIdx? p := by
  rw [List.find?_eq_bind_findIdx?_getElem?]
  cases h : (List.finRange m).findIdx? p with
  | none => simp
  | some i =>
      have hi : i < m := by
        have hh := (List.findIdx?_eq_some_iff_getElem.mp h).choose
        simpa using hh
      have hi' : i < (List.finRange m).length := by simpa using hi
      simp [h, List.getElem?_eq_getElem hi', List.getElem_finRange]

theorem physical_selected_eq_pivot {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r : Nat) (c : Fin k) :
    let flags := (List.finRange m).map (fun i => decide (B i c ≠ 0))
    GaussFlagSearch.selected flags r =
      Option.map Fin.val (SequentialTotality.pivotTyped B r c) := by
  dsimp only
  rw [SequentialTotality.pivotTyped, finRange_find_value]
  rw [selected_eq_findIdx]
  congr 1
  funext i
  simp [Bool.and_eq_true, decide_eq_true_eq]

theorem firstHit_some {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r : Nat) (c : Fin k)
    (pivot : Fin m)
    (hp : SequentialTotality.pivotTyped B r c = some pivot) :
    GaussFlagSearch.firstHit
      ((List.finRange m).map (fun i => decide (B i c ≠ 0))) r =
      (true,pivot.val) := by
  have hs : GaussFlagSearch.selected
      ((List.finRange m).map (fun i => decide (B i c ≠ 0))) r =
      some pivot.val := by
    simpa only [hp, Option.map_some] using
      (physical_selected_eq_pivot B r c)
  cases h : GaussFlagSearch.firstHit
      ((List.finRange m).map (fun i => decide (B i c ≠ 0))) r with
  | mk found row =>
      cases found with
      | false =>
          simp only [GaussFlagSearch.selected, h,
            Bool.false_eq_true, ↓reduceIte] at hs
          cases hs
      | true =>
          have hrow : row = pivot.val := by
            simpa only [GaussFlagSearch.selected, h,
              ↓reduceIte,
              Option.some.injEq] using hs
          simpa only [h, Prod.mk.injEq, true_and] using hrow

theorem firstHit_none {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r : Nat) (c : Fin k)
    (hp : SequentialTotality.pivotTyped B r c = none) :
    (GaussFlagSearch.firstHit
      ((List.finRange m).map (fun i => decide (B i c ≠ 0))) r).1 = false := by
  have hs : GaussFlagSearch.selected
      ((List.finRange m).map (fun i => decide (B i c ≠ 0))) r =
      none := by
    simpa only [hp, Option.map_none] using
      (physical_selected_eq_pivot B r c)
  cases h : GaussFlagSearch.firstHit
      ((List.finRange m).map (fun i => decide (B i c ≠ 0))) r with
  | mk found row =>
      cases found with
      | false => simp [h]
      | true =>
          simp only [GaussFlagSearch.selected, h,
            ↓reduceIte] at hs
          cases hs

#print axioms physical_selected_eq_pivot
#print axioms firstHit_some
#print axioms firstHit_none

end CurrentAdditive.GaussPivotSemanticBridge
