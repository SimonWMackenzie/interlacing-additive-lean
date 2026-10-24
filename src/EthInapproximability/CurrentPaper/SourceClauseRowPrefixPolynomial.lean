import EthInapproximability.CurrentPaper.SourceClauseAllSlotPolynomial

/-! Source-exact payload increments needed for the variable-row loop clock. -/

namespace EthInapproximability.CurrentPaper.SourceClauseCallbackRowPrefixPolynomial

open SourceClauseCallback.AllSlots
open SourceClauseCallbackAllSlotPolynomial

theorem listSaved_length_le {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (table : Fin (2 ^ q) → Bool)
    (ks : List (Fin (2 ^ q))) (saved : List Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H) :
    (listSaved hq row n r table ks saved).length ≤
      saved.length + ks.length * (slotByteCoefficient q * (H + 1)) := by
  induction ks generalizing saved with
  | nil => simp [listSaved]
  | cons k ks ih =>
      have hs := slotSaved_length_le hq row n r H k (table k) saved
        hn hr hrow
      have ht := ih (slotSaved hq row n r k (table k) saved)
      dsimp [listSaved]
      nlinarith

theorem listCount_length_le {q : ℕ}
    (table : Fin (2 ^ q) → Bool)
    (ks : List (Fin (2 ^ q))) (count : List Bool) :
    (listCount table ks count).length ≤
      count.length + ks.length * (3 * q + 5) := by
  induction ks generalizing count with
  | nil => simp [listCount]
  | cons k ks ih =>
      have hc := slotCount_length_le (q := q) (table k) count
      have ht := ih (slotCount (q := q) (table k) count)
      dsimp [listCount]
      nlinarith

theorem allSaved_length_le {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (table : Fin (2 ^ q) → Bool)
    (saved : List Bool) (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H) :
    (listSaved hq row n r table
      (List.ofFn (fun k : Fin (2 ^ q) => k)) saved).length ≤
      saved.length + (2 ^ q) * (slotByteCoefficient q * (H + 1)) := by
  simpa only [List.length_ofFn] using
    listSaved_length_le hq row n r H table
      (List.ofFn (fun k : Fin (2 ^ q) => k)) saved hn hr hrow

theorem allCount_length_le {q : ℕ}
    (table : Fin (2 ^ q) → Bool) (count : List Bool) :
    (listCount table (List.ofFn (fun k : Fin (2 ^ q) => k)) count).length ≤
      count.length + (2 ^ q) * (3 * q + 5) := by
  simpa only [List.length_ofFn] using
    listCount_length_le table
      (List.ofFn (fun k : Fin (2 ^ q) => k)) count

end EthInapproximability.CurrentPaper.SourceClauseCallbackRowPrefixPolynomial
