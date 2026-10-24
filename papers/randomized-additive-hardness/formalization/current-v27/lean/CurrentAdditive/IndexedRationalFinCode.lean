import CurrentAdditive.IndexedRationalListCode

/-! A complete indexed input table, with exact integer-weight semantics.
The emitted word identifies the index. Decoding indices to possibly equal
matrix labels is a separate deterministic map. -/

namespace Paper2.IndexedRationalFinCode

open scoped BigOperators
open Paper2.RecursiveSamplingProgram Paper2.GeneratorCode
open Paper2.RecursiveLabelCodecScratch Paper2.IndexedRationalListCode

private theorem total_eq_sum (xs : List (ℕ × List Bool)) :
    total xs = (xs.map Prod.fst).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [total, ih]

private theorem payoff_eq_sum (f : List Bool → ℝ)
    (xs : List (ℕ × List Bool)) :
    payoff f xs = (xs.map fun x => (x.1 : ℝ) * f x.2).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [payoff, ih]

/-- Preserve the position of every entry even when later labels coincide. -/
def entries (n : ℕ) (w : Fin n → ℕ) : List (ℕ × List Bool) :=
  List.ofFn (fun i : Fin n => (w i, (finCodec n).encode i))

theorem entries_positive {n : ℕ} {w : Fin n → ℕ}
    (hw : ∀ i, 0 < w i) :
    ∀ x ∈ entries n w, 0 < x.1 := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact hw i

theorem total_entries (n : ℕ) (w : Fin n → ℕ) :
    total (entries n w) = ∑ i, w i := by
  classical
  rw [total_eq_sum]
  simp [entries, List.sum_ofFn]

theorem payoff_entries (n : ℕ) (w : Fin n → ℕ)
    (f : List Bool → ℝ) :
    payoff f (entries n w) =
      ∑ i, (w i : ℝ) * f ((finCodec n).encode i) := by
  classical
  rw [payoff_eq_sum]
  simp [entries, List.sum_ofFn]

/-- A finite rational choice emitted as its concrete encoded position. -/
def code (n : ℕ) (w : Fin n → ℕ) : Code :=
  compile (entries n w)

theorem code_expect {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (f : List Bool → ℝ) :
    Program.expect (meaning (code n w)) f =
      (∑ i, (w i : ℝ) * f ((finCodec n).encode i)) / (∑ i, w i) := by
  have he : entries n w ≠ [] := by
    intro h
    have : (w ⟨0, hn⟩, (finCodec n).encode ⟨0, hn⟩) ∈ entries n w :=
      List.mem_ofFn.mpr ⟨⟨0, hn⟩, rfl⟩
    simp [h] at this
  simpa [code, payoff_entries, total_entries] using
    compile_expect he (entries_positive hw) f

#print axioms code_expect

end Paper2.IndexedRationalFinCode
