import Paper2.LocateUniform

/-! Unit 3, segment (1), outer-token step for the fixed-tail tag: the
production column-fetch program `FetchIndexed.colProgram` with code
`outerCode q₁ q₂ s col_k` (the `NavJoin` cell 7 code) fetches the `p`-th outer
word of the fixed-tail tuple `js` NON-destructively (the tuple word stays in
its cell; exact exit bank); the outer token `(js p).1` is the unary prefix of
that word (`outer_word_token`). This is the body of the outer-token equality
loop for the fixed-tail tag; the loop itself, the unrestricted tag (which
first skips the `s+1` tail words) and the diagonal tag are NOT built here. -/

namespace Paper2.OuterTokenFetch

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveRequestCodeShape
open RecursiveLabelCodecScratch RecursiveEntries SourceMatrix
open OutputSkipper

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

variable {n p s q₁ q₂ w Q : ℕ}
  [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

theorem fixed_outer_fetch (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ)
    (js : Fin s → OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (pp : Fin s) (O cc my : List Bool) :
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let oc := outerColumnCodec q₁ q₂ s C.2
    let rc := outerCode q₁ q₂ s (seedRecursiveCodes n p s q₁ q₂ w Q k).2
    let cs := List.ofFn (fun a : Fin s => oc.encode (js a))
    ∃ t ≤ FetchIndexed.colBound rc cs pp.val O, ∃ v,
      ((advance FetchIndexed.colProgram)^[t])
        (⟨some FetchIndexed.colStart, FetchIndexed.colControl,
          FetchIndexed.FB [] [] [] [] ((piCodec oc s).encode js ++ O) (encodeCode rc) cc my
            (List.replicate pp.val true)⟩ :
          TM2.Cfg (fun _ : FetchIndexed.Stack => Bool) _ _) =
        ⟨none, v, FetchIndexed.FB [] [] [] (oc.encode (js pp))
          ((piCodec oc s).encode js ++ O) (encodeCode rc) cc my (List.replicate pp.val true)⟩ := by
  intro C oc rc cs
  have hshape : Shape rc :=
    OutputSkipper.shape_outer q₁ q₂ s _
      (OutputSkipper.shape_seedRecursiveCodes n p s q₁ q₂ w Q k (by omega)).2
  have hout := (FullSupport.subcodes_full (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hp hs k).2.2.2.1
  have hprod : ∀ c ∈ cs, Produces (meaning rc) c := by
    intro c hc
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hc
    exact hout (js a)
  have hflat : (piCodec oc s).encode js = cs.flatten := by
    rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord, SuccessCodec.tupleWord_eq_flatten]
  have hpos : pp.val < cs.length := by simp [cs]
  obtain ⟨t, ht, v, hr⟩ := FetchIndexed.col_fetch rc hshape cs hprod O pp.val hpos
    (encodeCode rc) cc my rfl
  refine ⟨t, ht, v, ?_⟩
  have hword : cs.getD pp.val [] = oc.encode (js pp) := by
    rw [List.getD_eq_getElem _ _ hpos]
    simp [cs]
  rw [hflat]
  simpa only [hword] using hr

omit [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s] in
/-- The outer word begins with its unary token. -/
theorem outer_word_token (k : ℕ)
    (o : OuterColumn q₁ q₂ s
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)) :
    (outerColumnCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).2).encode o =
      List.replicate o.1.val true ++ false ::
        (piCodec (defaultCarrierCodecs n p s q₁ q₂ w Q k).2 (q₁ + s + 1)).encode o.2 := by
  simp [outerColumnCodec, prodCodec, finCodec]

#print axioms fixed_outer_fetch
#print axioms outer_word_token

end Paper2.OuterTokenFetch
