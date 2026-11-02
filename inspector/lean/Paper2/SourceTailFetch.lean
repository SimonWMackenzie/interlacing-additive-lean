import Paper2.FetchIndexed
import Paper2.FullSupport
import Paper2.OutputSkipperLabel

/-! Paper 2 v12 `eq:raw-source` and Appendix D. The fixed column-fetch
program traverses the actual `s+1` tail words at the unary source position.
This does not perform outer-token comparison or coordinate scanning. -/

namespace Paper2.SourceTailFetch

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveRequestCodeShape
open RecursiveLabelCodecScratch RecursiveEntries SourceMatrix
open OutputSkipper

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

variable {n p s q₁ q₂ w Q : ℕ}
  [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

theorem unrestricted_source_tail_fetch (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ)
    (i : SourceConstruction.Items s (Fin n))
    (activity : SourceConstruction.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (Z : RawColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k))
    (O rc my : List Bool) :
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let col := (seedRecursiveCodes n p s q₁ q₂ w Q k).2
    let cs := List.ofFn (fun a : Fin (s + 1) => C.2.encode (Z.1 a))
    let pos := (sourcePosition activity i Z).val
    ∃ t ≤ FetchIndexed.colBound col cs pos O, ∃ v,
      ((advance FetchIndexed.colProgram)^[t])
        (⟨some FetchIndexed.colStart, FetchIndexed.colControl,
          FetchIndexed.FB [] [] [] [] (cs.flatten ++ O) (encodeCode col) rc my
            (List.replicate pos true)⟩ :
          TM2.Cfg (fun _ : FetchIndexed.Stack => Bool) _ _) =
        ⟨none, v, FetchIndexed.FB [] [] [] (C.2.encode (sourceColumn activity i Z))
          (cs.flatten ++ O) (encodeCode col) rc my (List.replicate pos true)⟩ := by
  dsimp only
  let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
  let col := (seedRecursiveCodes n p s q₁ q₂ w Q k).2
  let cs := List.ofFn (fun a : Fin (s + 1) => C.2.encode (Z.1 a))
  let pos := (sourcePosition activity i Z).val
  have hshape : Shape col :=
    (OutputSkipper.shape_seedRecursiveCodes n p s q₁ q₂ w Q k (by omega)).2
  have hprod : ∀ c ∈ cs, Produces (meaning col) c := by
    intro c hc
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hc
    exact (FullSupport.codes_full (n := n) (p := p) (s := s)
      (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k).2 (Z.1 a)
  have hpos : pos < cs.length := by
    simpa [pos, cs] using (sourcePosition activity i Z).isLt
  obtain ⟨t, ht, v, hr⟩ := FetchIndexed.col_fetch col hshape cs hprod O pos hpos
    (encodeCode col) rc my rfl
  refine ⟨t, ht, v, ?_⟩
  have hword : cs.getD pos [] = C.2.encode (sourceColumn activity i Z) := by
    rw [List.getD_eq_getElem _ _ hpos]
    change (List.ofFn (fun a : Fin (s + 1) => C.2.encode (Z.1 a)))[pos] =
      C.2.encode (Z.1 (sourcePosition activity i Z))
    rw [List.getElem_ofFn]
  simpa only [hword] using hr

/-- For a diagonal tag, the physical word is the single outer word rather
than an expanded copy of its tail. The index includes the `q₁` head cells. -/
theorem diagonal_source_tail_fetch (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ)
    (i : SourceConstruction.Items s (Fin n))
    (activity : SourceConstruction.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (j : OuterColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (O rc my : List Bool) :
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let col := (seedRecursiveCodes n p s q₁ q₂ w Q k).2
    let cs := List.ofFn (fun a : Fin (q₁ + s + 1) => C.2.encode (j.2 a))
    let pos := q₁ + (sourcePosition activity i (forgetTag ξ₀ (.diagonal j))).val
    ∃ t ≤ FetchIndexed.colBound col cs pos O, ∃ v,
      ((advance FetchIndexed.colProgram)^[t])
        (⟨some FetchIndexed.colStart, FetchIndexed.colControl,
          FetchIndexed.FB [] [] [] [] (cs.flatten ++ O) (encodeCode col) rc my
            (List.replicate pos true)⟩ :
          TM2.Cfg (fun _ : FetchIndexed.Stack => Bool) _ _) =
        ⟨none, v, FetchIndexed.FB [] [] []
          (C.2.encode (sourceColumn activity i (forgetTag ξ₀ (.diagonal j))))
          (cs.flatten ++ O) (encodeCode col) rc my (List.replicate pos true)⟩ := by
  dsimp only
  let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
  let col := (seedRecursiveCodes n p s q₁ q₂ w Q k).2
  let cs := List.ofFn (fun a : Fin (q₁ + s + 1) => C.2.encode (j.2 a))
  let pos := q₁ + (sourcePosition activity i (forgetTag ξ₀ (.diagonal j))).val
  have hshape : Shape col :=
    (OutputSkipper.shape_seedRecursiveCodes n p s q₁ q₂ w Q k (by omega)).2
  have hprod : ∀ c ∈ cs, Produces (meaning col) c := by
    intro c hc
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hc
    exact (FullSupport.codes_full (n := n) (p := p) (s := s)
      (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k).2 (j.2 a)
  have hpos : pos < cs.length := by
    simp only [pos, cs, List.length_ofFn]
    have h := (sourcePosition activity i (forgetTag ξ₀ (.diagonal j))).isLt
    omega
  obtain ⟨t, ht, v, hr⟩ := FetchIndexed.col_fetch col hshape cs hprod O pos hpos
    (encodeCode col) rc my rfl
  refine ⟨t, ht, v, ?_⟩
  have hword : cs.getD pos [] =
      C.2.encode (sourceColumn activity i (forgetTag ξ₀ (.diagonal j))) := by
    rw [List.getD_eq_getElem _ _ hpos]
    change (List.ofFn (fun a : Fin (q₁ + s + 1) => C.2.encode (j.2 a)))[pos] =
      C.2.encode (j.2 ⟨pos, by simpa [cs] using hpos⟩)
    rw [List.getElem_ofFn]
  simpa only [hword] using hr

#print axioms unrestricted_source_tail_fetch
#print axioms diagonal_source_tail_fetch

end Paper2.SourceTailFetch
