import CurrentAdditive.EntryBits

namespace CurrentAdditive.EliminationEntryBounds

open CurrentAdditive.SequentialTotality CurrentAdditive.MaterializedGauss

structure CursorState (m k : ℕ) where
  B : Fin m → Fin k → ℚ
  r : ℕ
  c : ℕ

/-- One real transition of the eager materialized loop, including the scan
of a column with no pivot. Terminal states remain fixed. -/
def cursorStep {m k : ℕ} (s : CursorState m k) : CursorState m k :=
  if hr : s.r < m then
    if hc : s.c < k then
      let rf : Fin m := ⟨s.r, hr⟩
      let cf : Fin k := ⟨s.c, hc⟩
      match pivotTyped s.B s.r cf with
      | none => ⟨s.B, s.r, s.c + 1⟩
      | some i =>
        ⟨materialize (clearTyped (swapTyped s.B rf i) rf cf),
          s.r + 1, s.c + 1⟩
    else s
  else s

theorem materialized_terminal_row {m k : ℕ}
    (A : Fin m → Fin k → ℚ) (r c fuel : ℕ) (hr : ¬ r < m) :
    (echelonMaterialized A r c fuel).1 = A := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [echelonMaterialized, hr]

theorem materialized_terminal_col {m k : ℕ}
    (A : Fin m → Fin k → ℚ) (r c fuel : ℕ) (hc : ¬ c < k) :
    (echelonMaterialized A r c fuel).1 = A := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    by_cases hr : r < m
    · simp [echelonMaterialized, hr, hc]
    · simp [echelonMaterialized, hr]

theorem materialized_succ_cursor {m k : ℕ}
    (s : CursorState m k) (fuel : ℕ) :
    (echelonMaterialized s.B s.r s.c (fuel + 1)).1 =
      (echelonMaterialized (cursorStep s).B
        (cursorStep s).r (cursorStep s).c fuel).1 := by
  by_cases hr : s.r < m
  · by_cases hc : s.c < k
    · cases hp : pivotTyped s.B s.r ⟨s.c, hc⟩ with
      | none => simp [echelonMaterialized, cursorStep, hr, hc, hp]
      | some i => simp [echelonMaterialized, cursorStep, hr, hc, hp]
    · simp [echelonMaterialized, cursorStep, hr, hc,
        materialized_terminal_col s.B s.r s.c fuel hc]
  · simp [echelonMaterialized, cursorStep, hr,
      materialized_terminal_row s.B s.r s.c fuel hr]

def initialCursor {m k : ℕ} (A : Fin m → Fin k → ℚ) : CursorState m k :=
  ⟨A, 0, 0⟩

def cursorAfter {m k : ℕ} (A : Fin m → Fin k → ℚ) (t : ℕ) :
    CursorState m k :=
  (cursorStep^[t]) (initialCursor A)

theorem materialized_after_cursor {m k : ℕ}
    (s : CursorState m k) (t u : ℕ) :
    (echelonMaterialized ((cursorStep^[t]) s).B
      ((cursorStep^[t]) s).r ((cursorStep^[t]) s).c u).1 =
    (echelonMaterialized s.B s.r s.c (t + u)).1 := by
  induction t generalizing s with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply]
    rw [ih (cursorStep s)]
    have hh := materialized_succ_cursor s (t + u)
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hh.symm

theorem cursorAfter_eq_prefix {m k : ℕ}
    (A : Fin m → Fin k → ℚ) (t : ℕ) :
    (cursorAfter A t).B = (echelonMaterialized A 0 0 t).1 := by
  have hh := materialized_after_cursor (initialCursor A) t 0
  simpa [cursorAfter, initialCursor, echelonMaterialized] using hh

theorem every_actual_step_entry_bits {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (t : ℕ) (ht : t ≤ k) (i : Fin m) (j : Fin k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let B := (cursorAfter Aq t).B
    Nat.size (B i j).den ≤ (m + 3) * (m + 1) ^ 2 + 1 ∧
    Nat.size (B i j).num.natAbs ≤
      (m + 3) * (m + 1) ^ 2 + 1 := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  change Nat.size ((cursorAfter Aq t).B i j).den ≤
      (m + 3) * (m + 1) ^ 2 + 1 ∧
    Nat.size ((cursorAfter Aq t).B i j).num.natAbs ≤
      (m + 3) * (m + 1) ^ 2 + 1
  rw [cursorAfter_eq_prefix]
  exact materializedPrefix_entry_bits A h01 t ht i j

end CurrentAdditive.EliminationEntryBounds
