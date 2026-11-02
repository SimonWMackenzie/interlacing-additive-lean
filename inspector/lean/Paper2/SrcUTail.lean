import Paper2.SrcURun

/-! Unit 3, segment (1): the unrestricted source arm `SrcU.srcU` as ONE run
on ONE bank (`srcU_run`): item operands ; outer-token equality ; physical
`scanAtCanonical` ; clear the index ; unary `sourcePosition` ; tail fetch.
The label cell ends with `C.2.encode (sourceColumn activity i Z)`, the row
cell with `C.1.encode u`, i.e. the encoded
`baseRequest activity (.inr (i, u)) Z` (`eq:raw-source`), for
`activity = SourceActiveRank.scanAtCanonical (graphEdge g hg) hs hq`. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SrcU

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveRequestCodeShape
open RecursiveLabelCodecScratch RecursiveEntries SourceMatrix
open BitMachineRawSequence (leftLabel)
open Paper2.OTOps (u)
open Paper2.OTBody (B BB aC eqC sC idxB lblB ob)
open Paper2.ScanDecodeMachine (K D0)
open Paper2.RankRun (R RB)

theorem FB_idx_irrel (O code cnt lbl fw cc rc my idx idx' : List Bool) (kk : FetchIndexed.Stack)
    (hk : kk ≠ FetchIndexed.idxC) :
    FetchIndexed.FB O code cnt lbl fw cc rc my idx kk =
      FetchIndexed.FB O code cnt lbl fw cc rc my idx' kk := by
  rcases kk with kk | kk
  · rfl
  · fin_cases kk
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd rfl hk

theorem ιP_range_F (kk : FetchIndexed.Stack) (hk : kk ≠ FetchIndexed.idxC) :
    ¬ ∃ j, ιP j = ιF kk := by
  rintro ⟨j, hj⟩
  fin_cases j <;> simp [ιP, ιPf, ιF, eqC, sC, idxB, sp5, sp6] at hj
  exact hk hj.symm

theorem ιP_range_src : ¬ ∃ j, ιP j = srcA := by
  rintro ⟨j, hj⟩
  fin_cases j <;> simp [ιP, ιPf, eqC, sC, idxB, sp5, sp6, srcA] at hj

theorem ιF_range_src : ¬ ∃ j, ιF j = srcA := by
  rintro ⟨j, hj⟩
  simp [ιF, srcA] at hj

theorem ιF_idx : ιF FetchIndexed.idxC = ιP 4 := rfl
theorem ιF_lbl : ιF (.inl FetchLabel.lblC) = (.inl lblB : JA) := rfl

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The exact composite clock of the unrestricted source arm. -/
def srcUBound (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r) (k : ℕ)
    (i : SourceConstruction.Items s (Fin g.vertices))
    (Z : RawColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k))
    (O : List Bool) : ℕ :=
  let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k
  let col := (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2
  let xv := CanonicalEndpointRankBridge.itemValue i.2
  let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
    (by omega) hq
  (1 + ((i.1.val + 1) + 1 + (xv + 1) + 2) + 1) +
    OTGen.fullGBound s (OTTags.TfU k Z O) (OTLoop.tokF k Z.2) (OTTags.restF k Z.2) +
    scanPosBound g hg (Z.2 0).1.val r i.1.val xv i.2.isRight + (2 * s + 4) + (s + 1) +
    FetchIndexed.colBound col (List.ofFn (fun a : Fin (s + 1) => C.2.encode (Z.1 a)))
      (sourcePosition activity i Z).val
      ((piCodec (outerColumnCodec q₁ q₂ s C.2) s).encode Z.2 ++ O) + 5

/-- Segment (1), unrestricted tag: the whole source arm as ONE program on ONE
bank, from the raw source-row word, the raw column word (tag bit popped), the
serialized column and outer codes, unary `s+1`, unary `s`, unary `r`, unary
`m`, and the literal public graph bytes. -/
theorem srcU_run (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r) (k : ℕ)
    (i : SourceConstruction.Items s (Fin g.vertices))
    (uu : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q k)
    (Z : RawColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k))
    (O : List Bool) :
    let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k
    let col := (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2
    let fw := (rawColumnCodec q₁ q₂ s C.2).encode Z ++ O
    let X0 := BB [] fw (encodeCode col) (encodeCode (outerCode q₁ q₂ s col)) (u (s + 1))
      [] [] [] [] [] [] [] (u s)
    let WA0 : JA → List Bool := Sum.elim X0 (Sum.elim (JJ0 g r)
      ![(prodCodec (defaultItemCodec g.vertices s) C.1).encode (i, uu), [], [], []])
    let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by omega) hq
    ∃ t ≤ srcUBound g hg hs r hq k i Z O, ∃ v F,
      ((advance srcU)^[t]) (⟨some srcUStart, srcUCtl, WA0⟩ : TM2.Cfg (fun _ : JA => Bool) _ _) =
        ⟨none, v, F⟩ ∧
      F (.inl lblB) = C.2.encode (sourceColumn activity i Z) ∧
      F srcA = C.1.encode uu ∧
      F (.inl idxB) = List.replicate (sourcePosition activity i Z).val true ∧
      F (.inl (.inl FetchIndexed.fwC)) = fw ∧
      F (.inl (.inl FetchIndexed.ccC)) = encodeCode col := by
  intro C col fw X0 WA0 activity
  obtain ⟨t, T, act, rk, t3, ht, hb3, hA, hR, hV, v, q2⟩ :=
    front_run g hg hp hs r hq k i uu Z O
  let X2 := BB [] fw (encodeCode col) (encodeCode (outerCode q₁ q₂ s col)) (u (s + 1))
      (u s) (u (Z.2 0).1.val) [] [] [] [] [decide (∀ pp, (Z.2 pp).1 = (Z.2 0).1)] (u s)
  let F4 : Fin 4 → List Bool := ![C.1.encode uu, [], [], []]
  let W3 : JA → List Bool := Sum.elim (Function.update X2 aC (T K0))
    (Sum.elim (Function.update T K0 []) F4)
  change _ = (⟨none, v, W3⟩ : TM2.Cfg (fun _ : JA => Bool) _ _) at q2
  -- phase 4: clear the index cell
  have hI : W3 (.inl idxB) = u s := by
    show Function.update X2 aC (T K0) idxB = u s
    rw [Function.update_of_ne (by simp [idxB, aC])]
    rfl
  have l4 := OTOps.clr_run (.inl idxB : JA) (u s) W3 ob hI
  let W4 := Function.update W3 (.inl idxB) []
  have hW4 : ∀ x, x ≠ (.inl idxB : JA) → W4 x = W3 x := fun x hx => Function.update_of_ne hx _ _
  -- phase 5: the source position
  let eqb := decide (∀ pp, (Z.2 pp).1 = (Z.2 0).1)
  have hSP : ∀ j, SourcePos.PB [eqb] [act] rk s j = W4 (ιP j) := by
    intro j
    fin_cases j
    · show [eqb] = W4 (.inl eqC)
      rw [hW4 _ (by simp [eqC, idxB])]
      show [eqb] = Function.update X2 aC (T K0) eqC
      rw [Function.update_of_ne (by simp [eqC, aC])]
      rfl
    · show [act] = W4 (.inr (.inl ScanJoin.actC))
      rw [hW4 _ (by simp)]
      show [act] = Function.update T K0 [] ScanJoin.actC
      rw [Function.update_of_ne (by simp [ScanJoin.actC, K0]), hA]
    · show SourcePos.u rk = W4 (.inr (.inl rkC))
      rw [hW4 _ (by simp)]
      show SourcePos.u rk = Function.update T K0 [] rkC
      rw [Function.update_of_ne (by simp [rkC, K0]), hR]
      rfl
    · show SourcePos.u s = W4 (.inl sC)
      rw [hW4 _ (by simp [sC, idxB])]
      show SourcePos.u s = Function.update X2 aC (T K0) sC
      rw [Function.update_of_ne (by simp [sC, aC])]
      rfl
    · show [] = Function.update W3 (.inl idxB : JA) [] (.inl idxB)
      rw [Function.update_self]
    · show [] = W4 sp5
      rw [hW4 _ (by simp [sp5])]
      rfl
    · show [] = W4 sp6
      rw [hW4 _ (by simp [sp6])]
      rfl
  obtain ⟨t5, ht5, c5', l5⟩ := SourcePos.pos_run eqb act rk s
  have l5' := liftA ιP SourcePos.program W4 _ _ hSP _ _ _ _ l5
  have hpos : (sourcePosition activity i Z).val = if eqb && act then rk else s :=
    SourcePos.sourcePosition_eq (X := Unit) activity i Z eqb act rk decide_eq_true_iff hV
  let W5 := bank ιP W4 (SourcePos.PF s (if eqb && act then rk else s))
  have hW5 : W5 = bank ιP W4 (SourcePos.PF s (if eqb && act then rk else s)) := rfl
  -- phase 6: the tail fetch at the unary source position
  let cs := List.ofFn (fun a : Fin (s + 1) => C.2.encode (Z.1 a))
  let O' := (piCodec (outerColumnCodec q₁ q₂ s C.2) s).encode Z.2 ++ O
  have hfw : cs.flatten ++ O' = fw := by
    have e1 : (piCodec C.2 (s + 1)).encode Z.1 = cs.flatten := by
      rw [CodeSampleOutputDecoder.piCodec_encode_tupleWord, SuccessCodec.tupleWord_eq_flatten]
    have e3 : (rawColumnCodec q₁ q₂ s C.2).encode Z =
        (piCodec C.2 (s + 1)).encode Z.1 ++
          (piCodec (outerColumnCodec q₁ q₂ s C.2) s).encode Z.2 := rfl
    simp only [fw, O', e3, e1, List.append_assoc]
  obtain ⟨t6, ht6, v6, l6⟩ := SourceTailFetch.unrestricted_source_tail_fetch
    (n := g.vertices) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k i
    activity Z O' (encodeCode (outerCode q₁ q₂ s col)) (u (s + 1))
  have hSF : ∀ kk, FetchIndexed.FB [] [] [] [] (cs.flatten ++ O') (encodeCode col)
      (encodeCode (outerCode q₁ q₂ s col)) (u (s + 1))
      (List.replicate (sourcePosition activity i Z).val true) kk = W5 (ιF kk) := by
    intro kk
    by_cases hk : kk = FetchIndexed.idxC
    · subst hk
      rw [ιF_idx]
      show List.replicate (sourcePosition activity i Z).val true = W5 (ιP 4)
      rw [hW5, bank_at, hpos]
      rfl
    · rw [hW5, bank_outside ιP _ _ (ιF kk) (ιP_range_F kk hk)]
      rw [hW4 _ (by
        intro h
        apply hk
        have h' : (Sum.inl (Sum.inl kk) : JA) = Sum.inl (Sum.inl FetchIndexed.idxC) := h
        simpa using h')]
      show _ = Function.update X2 aC (T K0) (.inl kk)
      rw [Function.update_of_ne (by simp [aC])]
      rw [FB_idx_irrel _ _ _ _ _ _ _ _ _ (u s) kk hk, hfw]
      rfl
  have l6' := liftA ιF FetchIndexed.colProgram W5 _ _ hSF _ _ _ _ l6
  -- sequencing
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs z2 S4
    (leftLabel (leftLabel (leftLabel ()))) () ((c1, c2), c3) v ob ob _ _ _ _ _ q2 l4
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs z3 S5
    (leftLabel (leftLabel (leftLabel (leftLabel ())))) (leftLabel .l0) (((c1, c2), c3), ob)
    (((c1, c2), c3), ob) c5 c5' _ _ _ _ _ q3 l5'
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs z4 S6
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ()))))) FetchIndexed.colStart
    ((((c1, c2), c3), ob), c5) ((((c1, c2), c3), ob), c5') FetchIndexed.colControl v6
    _ _ _ _ _ q4 l6'
  refine ⟨u5, ?_, _, _, q5, ?_, ?_, ?_, ?_, ?_⟩
  · have hl : (u s).length = s := by simp [u]
    have ht6' : t6 ≤ FetchIndexed.colBound (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2
        (List.ofFn fun a => (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode (Z.1 a))
        (sourcePosition (SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
          (by omega) hq) i Z).val
        ((piCodec (outerColumnCodec q₁ q₂ s (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2)
          s).encode Z.2 ++ O) := ht6
    rw [hl] at hu3
    simp only [srcUBound]
    omega
  · rw [← ιF_lbl, bank_at]
    rfl
  · rw [bank_outside ιF _ _ srcA ιF_range_src, hW5, bank_outside ιP _ _ srcA ιP_range_src,
      hW4 _ (by simp [srcA, idxB])]
    rfl
  · show bank ιF W5 _ (ιF FetchIndexed.idxC) = _
    rw [bank_at]
    rfl
  · show bank ιF W5 _ (ιF FetchIndexed.fwC) = _
    rw [bank_at]
    exact hfw
  · show bank ιF W5 _ (ιF FetchIndexed.ccC) = _
    rw [bank_at]
    rfl

#print axioms FB_idx_irrel
#print axioms ιP_range_F
#print axioms srcU_run

end

end Paper2.SrcU
