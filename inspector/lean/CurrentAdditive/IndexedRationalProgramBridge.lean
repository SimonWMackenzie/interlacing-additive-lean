import CurrentAdditive.IndexedRationalFinCode

/-! The same finite weighted choice as both a first-order code and a typed
program. This is the exact base equality required by `recursiveCodes_exact`. -/

namespace Paper2.IndexedRationalProgramBridge

open Paper2.RecursiveSamplingProgram Paper2.GeneratorCode
open Paper2.RecursiveLabelCodecScratch Paper2.IndexedRationalListCode

def massTotal {n : ℕ} : List (ℕ × Fin n) → ℕ
  | [] => 0
  | x :: xs => x.1 + massTotal xs

def encodeEntries {n : ℕ} (xs : List (ℕ × Fin n)) :
    List (ℕ × List Bool) :=
  xs.map (fun x => (x.1, (finCodec n).encode x.2))

theorem total_encodeEntries {n : ℕ} (xs : List (ℕ × Fin n)) :
    total (encodeEntries xs) = massTotal xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change x.1 + total (encodeEntries xs) = x.1 + massTotal xs
    rw [ih]

private theorem branch_meaning (N a : ℕ) (hN : 0 < N)
    (first second : Code) :
    meaning (.branch3 N a N first second (.emit [])) =
      .draw N hN (fun i => if i.val < a then meaning first else meaning second) := by
  cases N with
  | zero => omega
  | succ m =>
    simp only [meaning]
    congr 1
    funext i
    simp only [i.isLt, ↓reduceIte]

/-- The typed program mirrors the code's finite-choice branching. -/
def program {n : ℕ} (hn : 0 < n) : List (ℕ × Fin n) → Program (Fin n)
  | [] => .pure ⟨0, hn⟩
  | [x] => .pure x.2
  | x :: y :: ys =>
      if h : 0 < x.1 + massTotal (y :: ys) then
        .draw (x.1 + massTotal (y :: ys)) h
          (fun i => if i.val < x.1 then .pure x.2 else program hn (y :: ys))
      else .pure x.2

/-- Pointwise positivity makes the syntactic code denote exactly the encoded
typed program, with no conclusion-bearing certificate. -/
theorem compile_exact {n : ℕ} (hn : 0 < n)
    {xs : List (ℕ × Fin n)} (hne : xs ≠ [])
    (hp : ∀ x ∈ xs, 0 < x.1) :
    meaning (compile (encodeEntries xs)) =
      Program.map (finCodec n).encode (program hn xs) := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      have hx : 0 < x.1 := hp x (by simp)
      have htailp : ∀ z ∈ y :: ys, 0 < z.1 := by
        intro z hz
        exact hp z (by simp [hz])
      have ih' := ih (by simp) htailp
      have hpos : 0 < x.1 + massTotal (y :: ys) := by omega
      change meaning
          (IndexedRationalBaseCode.branchCode x.1
            (total (encodeEntries (y :: ys)))
            (.emit ((finCodec n).encode x.2))
            (compile (encodeEntries (y :: ys)))) =
        Program.map (finCodec n).encode (program hn (x :: y :: ys))
      rw [total_encodeEntries]
      simp only [IndexedRationalBaseCode.branchCode, program, dif_pos hpos]
      rw [branch_meaning _ _ hpos, Program.map_draw]
      congr 1
      funext i
      split_ifs with hfirst
      · rfl
      · simpa [encodeEntries] using ih'

def indices (n : ℕ) (w : Fin n → ℕ) : List (ℕ × Fin n) :=
  List.ofFn (fun i : Fin n => (w i, i))

theorem indices_positive {n : ℕ} {w : Fin n → ℕ}
    (hw : ∀ i, 0 < w i) :
    ∀ x ∈ indices n w, 0 < x.1 := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact hw i

theorem encode_indices (n : ℕ) (w : Fin n → ℕ) :
    encodeEntries (indices n w) = IndexedRationalFinCode.entries n w := by
  simp [encodeEntries, indices, IndexedRationalFinCode.entries,
    List.map_ofFn, Function.comp_def]

theorem code_exact {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) :
    meaning (IndexedRationalFinCode.code n w) =
      Program.map (finCodec n).encode (program hn (indices n w)) := by
  simpa [IndexedRationalFinCode.code, encode_indices] using
    compile_exact hn (by
      intro he
      have : (w ⟨0, hn⟩, (⟨0, hn⟩ : Fin n)) ∈ indices n w :=
        List.mem_ofFn.mpr ⟨⟨0, hn⟩, rfl⟩
      simp [he] at this) (indices_positive hw)

#print axioms code_exact

end Paper2.IndexedRationalProgramBridge
