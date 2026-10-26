import Paper2.OutputSkipperTrav
import Paper2.GeneratorResult
import Paper2.RecursiveSamplingReachability
import Paper2.GeneratorStateSize

/-! Output-skipper endpoints for the actual codes.

* `shape_seedRecursiveCodes`, `shape_seedSampleCode`: the actual recursive
  row/column codes and the columns-first sample code satisfy `Shape` (every
  branch is the tagged 256 layout or the rows 512 layout with item alphabet
  `4*s > 0`).
* `run_produces`: a successful capped run's output is a word the code can
  produce (no probability or oracle; from `run_eq` and `run_reaches`).
* `label_run`: one fixed program run on `[true]` consumes exactly one
  produced word and halts, leaving the residual output and syntax. -/

namespace Paper2.OutputSkipper

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineComposition
open GeneratorCode GeneratorSerialization GeneratorSource GeneratorFullSample
open RecursiveRequestCodeShape
open RecursiveSamplingProgram

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem shape_copies (n : Nat) (c : Code) (hc : Shape c) : Shape (copies n c) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨hc, ih⟩

theorem shape_outer (q₁ q₂ s : Nat) (c : Code) (hc : Shape c) :
    Shape (outerCode q₁ q₂ s c) := ⟨trivial, shape_copies _ _ hc⟩

theorem shape_raw (q₁ q₂ s : Nat) (c : Code) (hc : Shape c) :
    Shape (rawCode q₁ q₂ s c) :=
  ⟨shape_copies _ _ hc, shape_copies _ _ (shape_outer q₁ q₂ s c hc)⟩

theorem shape_fixedTail (q₁ q₂ s : Nat) (c : Code) (hc : Shape c) :
    Shape (fixedTailCode q₁ q₂ s c) := shape_copies _ _ (shape_outer q₁ q₂ s c hc)

theorem shape_tagged (q₁ q₂ s : Nat) (c : Code) (hc : Shape c) :
    Shape (taggedCode q₁ q₂ s c) := by
  refine ⟨Or.inr (Or.inl ⟨rfl, rfl, rfl, ?_⟩), ?_, ?_, ?_⟩
  · exact ⟨rawCode q₁ q₂ s c, fixedTailCode q₁ q₂ s c, outerCode q₁ q₂ s c, rfl, rfl, rfl⟩
  · exact ⟨trivial, shape_raw q₁ q₂ s c hc⟩
  · exact ⟨trivial, shape_fixedTail q₁ q₂ s c hc⟩
  · exact ⟨trivial, shape_outer q₁ q₂ s c hc⟩

theorem shape_template (q₁ q₂ : Nat) (c : Code) (hc : Shape c) :
    Shape (templateCode q₁ q₂ c) := shape_copies _ _ ⟨trivial, hc⟩

theorem shape_templateRow (q₁ q₂ s : Nat) (c : Code) (hc : Shape c) :
    Shape (templateRowCode q₁ q₂ s c) := ⟨trivial, shape_template q₁ q₂ c hc⟩

theorem shape_graphRows (n q₁ q₂ s : Nat) (hs : 0 < s) (c : Code) (hc : Shape c) :
    Shape (graphRowsCode (V := Fin n) q₁ q₂ s c) := by
  change Shape (rowsCode q₁ q₂ s (vertexLabelsCode (V := Fin n) s)
    (auxiliaryLabelsCode s) c)
  refine ⟨Or.inr (Or.inr ⟨rfl, rfl, rfl, ?_⟩), ?_, ?_, ?_⟩
  · exact ⟨4 * s, by omega, templateRowCode q₁ q₂ s c,
      .ticket (Fintype.card (Fin n)), .ticket (s - 3), c, rfl, rfl, rfl⟩
  · exact ⟨trivial, shape_templateRow q₁ q₂ s c hc⟩
  · exact ⟨trivial, ⟨⟨trivial, ⟨trivial, trivial⟩⟩, hc⟩⟩
  · exact ⟨trivial, ⟨⟨trivial, ⟨trivial, trivial⟩⟩, hc⟩⟩

theorem shape_recursiveCodes (n s q₁ q₂ w Q : Nat) (hs : 0 < s)
    (row₀ col₀ : Code) (hr : Shape row₀) (hc : Shape col₀) (k : Nat) :
    Shape (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).1 ∧
    Shape (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).2 := by
  induction k with
  | zero => exact ⟨hr, hc⟩
  | succ k ih =>
      exact ⟨shape_copies _ _ ⟨trivial, shape_tagged q₁ q₂ s _ ih.2⟩,
        ⟨trivial, shape_copies _ _ (shape_graphRows n q₁ q₂ s hs _ ih.1)⟩⟩

theorem shape_seedRecursiveCodes (n p s q₁ q₂ w Q k : Nat) (hs : 0 < s) :
    Shape (seedRecursiveCodes n p s q₁ q₂ w Q k).1 ∧
    Shape (seedRecursiveCodes n p s q₁ q₂ w Q k).2 :=
  shape_recursiveCodes n s q₁ q₂ w Q hs (copies p .bit) (.ticket p)
    (shape_copies p .bit trivial) trivial k

theorem shape_seedSampleCode (n p s q₁ q₂ w Q k mX mY : Nat) (hs : 0 < s) :
    Shape (seedSampleCode n p s q₁ q₂ w Q k mX mY) := by
  have h := shape_seedRecursiveCodes n p s q₁ q₂ w Q k hs
  exact ⟨shape_copies _ _ h.2, shape_copies _ _ h.1⟩

/-! ### Semantics of a successful run -/

theorem reaches_produces {A : Type*} (p : Program A) (a : A)
    (h : Program.Reaches p a) : Produces p a := by
  induction p with
  | pure b =>
    simp only [Program.Reaches] at h
    subst h
    exact .pure _
  | draw n hn next ih =>
      obtain ⟨i, hi⟩ := h
      exact .draw i (ih i hi)

theorem run_produces {M : Nat} (B R : Nat) (hMB : Nat.clog 2 M ≤ B) (N : Nat)
    (root : Code) (hM : (meaning root).maxAlphabet ≤ M)
    (t : CappedSampler.Adaptive.Tape B R N) (bytes : List Bool)
    (hr : GeneratorCode.run B R hMB N (GeneratorStateSize.initialBounded root hM) t = some bytes) :
    Produces (meaning root) bytes := by
  rw [GeneratorCode.run_eq] at hr
  have h := RecursiveSamplingCapped.run_reaches B R hMB N _ t bytes hr
  have hsem : (semantic (GeneratorStateSize.initialBounded root hM)).val = meaning root := by
    simp [semantic, GeneratorStateSize.initialBounded, initial_meaning]
  rw [hsem] at h
  exact reaches_produces _ _ h

theorem produces_copies (c : Code) : ∀ (n : Nat) (w : List Bool),
    Produces (meaning (copies n c)) w →
      ∃ ws : List (List Bool), ws.length = n ∧
        (∀ x ∈ ws, Produces (meaning c) x) ∧ w = ws.flatten
  | 0, w, h => by
      have hw := (produces_emit [] w).mp h
      exact ⟨[], rfl, by simp, by simp [hw]⟩
  | n + 1, w, h => by
      obtain ⟨x, y, hx, hy, rfl⟩ := produces_append h
      obtain ⟨ws, hlen, hall, rfl⟩ := produces_copies c n y hy
      refine ⟨x :: ws, by simp [hlen], ?_, by simp⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hx
      · exact hall z hz

/-! ### One label, from start to halt -/

theorem label_run (c : Code) (hc : Shape c) (w : List Bool)
    (hw : Produces (meaning c) w) (rest O U : List Bool) :
    ∃ t ≤ 8 * codeSize c * (w.length + 1) + 1,
      run t (ready (encodeCode c ++ rest) [true] (w ++ O) U) =
        ⟨none, (ctl0.1, (none, (none, 0))), bk rest [] [] [] [] [] [] [] O (w.reverse ++ U) []⟩ := by
  obtain ⟨t, ht, hr⟩ := trav_one c hc w hw rest [] O U
  refine ⟨t + 1, by omega, ?_⟩
  rw [run_add, hr, run_one, ready, check_nil]

#print axioms shape_seedSampleCode
#print axioms run_produces
#print axioms produces_copies
#print axioms label_run

end Paper2.OutputSkipper
