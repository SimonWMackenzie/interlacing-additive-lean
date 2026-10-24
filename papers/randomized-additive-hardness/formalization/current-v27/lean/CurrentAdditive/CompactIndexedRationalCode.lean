import CurrentAdditive.CompactFinCodec
import CurrentAdditive.IndexedRationalProgramBridge

/-! Rebind the checked integer-mass compiler to the compact binary codec.
The typed source program and its rational law are unchanged. -/

namespace Paper2.CompactIndexedRationalCode

open Paper2.RecursiveSamplingProgram Paper2.GeneratorCode
open Paper2.RecursiveLabelCodecScratch Paper2.IndexedRationalListCode
open Paper2.IndexedRationalProgramBridge Paper2.CompactFinCodec

def encodeEntriesWith {n : ℕ} (c : PrefixCodec (Fin n))
    (xs : List (ℕ × Fin n)) : List (ℕ × List Bool) :=
  xs.map (fun x => (x.1, c.encode x.2))

theorem total_encodeEntriesWith {n : ℕ} (c : PrefixCodec (Fin n))
    (xs : List (ℕ × Fin n)) :
    total (encodeEntriesWith c xs) = massTotal xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change x.1 + total (encodeEntriesWith c xs) = x.1 + massTotal xs
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

theorem compileWith_exact {n : ℕ} (hn : 0 < n)
    (c : PrefixCodec (Fin n))
    {xs : List (ℕ × Fin n)} (hne : xs ≠ [])
    (hp : ∀ x ∈ xs, 0 < x.1) :
    meaning (compile (encodeEntriesWith c xs)) =
      Program.map c.encode (program hn xs) := by
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
          (Paper2.IndexedRationalBaseCode.branchCode x.1
            (total (encodeEntriesWith c (y :: ys)))
            (.emit (c.encode x.2))
            (compile (encodeEntriesWith c (y :: ys)))) =
        Program.map c.encode (program hn (x :: y :: ys))
      rw [total_encodeEntriesWith]
      simp only [Paper2.IndexedRationalBaseCode.branchCode,
        program, dif_pos hpos]
      rw [branch_meaning _ _ hpos, Program.map_draw]
      congr 1
      funext i
      split_ifs with hfirst
      · rfl
      · simpa [encodeEntriesWith] using ih'

/-- Computable finite source code on indexed positive integer masses. -/
def code {n : ℕ} (w : Fin n → ℕ) : Code :=
  compile (encodeEntriesWith (codec n) (indices n w))

theorem code_exact {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) :
    meaning (code w) =
      Program.map (codec n).encode (program hn (indices n w)) := by
  unfold code
  apply compileWith_exact hn (codec n)
  · intro he
    have : (w ⟨0, hn⟩, (⟨0, hn⟩ : Fin n)) ∈ indices n w :=
      List.mem_ofFn.mpr ⟨⟨0, hn⟩, rfl⟩
    simp [he] at this
  · exact indices_positive hw

#print axioms code_exact

end Paper2.CompactIndexedRationalCode
