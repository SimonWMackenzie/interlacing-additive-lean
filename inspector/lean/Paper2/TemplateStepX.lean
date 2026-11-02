import Paper2.TStepXPre

/-! Unit 3, ROOT DECISION R5: the one-level composite `stepX` over
`JT = TemplateStep.J ⊕ SrcX.JX` with the source arm DISCHARGED.

* `template_stepX`: the template case, the same conclusion shape as the
  admitted `TemplateStep.template_step` (exit bank `bank i2 F (mk …)` on the
  `J` part with the admitted `LocateUniform.Frame`, the `E` part unchanged),
  now for the ONE fixed program `stepX` (no program parameter).
* `source_stepX`: the source case (`y.2 (x y.1).1 = .inr (i, u)`), for every
  tag of `(x y.1).2`, with `activity = SourceActiveRank.scanAtCanonical
  (graphEdge g hg) _ hq` and any tail family `ξ` satisfying the fixed-tail
  premise `hfix`: the encoded `RecursiveEntries.request activity ξ k x y`
  lands in the SAME two output cells `r2 tagC`, `r2 rowC` as in the template
  case, by two charged copies; every other `J` cell outside the four placed
  cells equals its value after the prefix. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.TemplateStepX

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries
open BitMachineRawSequence (leftLabel)
open Paper2.TemplateStep (J RS nC r1 r2 lC pcC myJ iN i1 i2 eL srcCell navP rs1 pre arm
  armStart armCtl)
open Paper2.CanonicalDefaultWordScratch (words)

theorem WXb_irrel {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]
    (g : EncodedGraph.Graph) (r k : ℕ) (a f : List Bool) (zz : SrcX.JX)
    (h1 : zz ≠ SrcX.srcAX) (h2 : zz ≠ SrcX.fwX) :
    SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k a f zz =
      SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k [] [] zz := by
  rcases zz with (((zz | zz) | zz) | (zz | zz)) | zz
  · rfl
  · fin_cases zz
    · exact absurd rfl h2
    all_goals rfl
  · rfl
  · rfl
  · fin_cases zz
    · exact absurd rfl h1
    all_goals rfl
  · rfl

variable {n p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

/-- The template case of the ONE fixed program `stepX` over `J ⊕ E` (root decision R5):
the same conclusion shape as the admitted `TemplateStep.template_step`. -/
theorem template_stepX [NeZero n] (E0 : SrcX.JX → List Bool) [NeZero s]
    (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ)
    (activity : SourceConstruction.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
      s q₁ q₂ w Q (k + 1))
    (pp : Fin s)
    (z : SourceMatrix.Template q₁ q₂
      (Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k))
    (hraw : y.2 (x y.1).1 = .inl (pp, z)) :
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let c := seedRecursiveCodes n p s q₁ q₂ w Q k
    let o := (SourceMatrix.forgetTag (ξ k) (x y.1).2).2 pp
    let TW := (piCodec (prodCodec (finCodec q₁) C.1) q₂).encode z
    let OW := (outerColumnCodec q₁ q₂ s C.2).encode o
    let S1 := Function.update (Function.update (Function.update (W2f k x y) srcCell
      (List.replicate pp.val true ++ false :: TW)) srcCell TW) pcC (List.replicate pp.val true)
    ∃ t ≤ NavJoin.joinBound n p s q₁ q₂ w Q k + selClock k x y + 1 +
        ((pp.val + 1) + LocateUniform.locBound q₁ q₂ s C.2 c.2 pp.val (x y.1).2 + 1 +
          RequestSelect.clock OW o.1.val (z o.1).1.val (.append (.ticket q₁) c.1) c.2
            (List.ofFn (fun a => (prodCodec (finCodec q₁) C.1).encode (z a)))
            (List.ofFn (fun b => C.2.encode (o.2 b))) + 1 + 1) + 1,
      ∃ v, ∃ F : J → List Bool,
      ((advance stepX)^[t])
        (⟨some (leftLabel (leftLabel NavJoin.startLabel)), stepXCtl, Sum.elim (W0f k x y) E0⟩ :
          TM2.Cfg (fun _ : JT => Bool) _ _) =
        ⟨none, v, Sum.elim (bank i2 F (RequestSelect.mk
          (C.1.encode (RecursiveEntries.request activity ξ k x y).1)
          (C.2.encode (RecursiveEntries.request activity ξ k x y).2)
          (RequestSelect.vec TW OW (encodeCode (.append (.ticket q₁) c.1)) (encodeCode c.2)
            (List.replicate o.1.val true) ((piCodec C.2 (q₁ + s + 1)).encode o.2)
            (List.replicate (z o.1).1.val true)))) E0⟩ ∧
      LocateUniform.Frame eL S1 F ∧ F (lC FetchLabel.lblC) = OW := by
  intro C c o TW OW S1
  have hreq : RecursiveEntries.request activity ξ k x y =
      ((z o.1).2, SourceMatrix.head o.2 (z o.1).1) := by
    unfold RecursiveEntries.request
    rw [hraw]
    rfl
  rw [hreq]
  -- the prefix, transported by `inJ`
  obtain ⟨u1, hu1, v1, q1⟩ := pre_run hp hs k x y
  have q1' := liftT inJ pre (Sum.elim (W0f k x y) E0) _ _ (fun _ => rfl) _ _ _ _ q1
  rw [bank_inJ] at q1'
  -- the template arm on the `J` part
  let W1 := bank iN (W0f k x y) (NavJoin.jb (NavJoin.outVec n p s q₁ q₂ w Q k))
  have hsrcW2 : W2f k x y srcCell = false :: (List.replicate pp.val true ++ false :: TW) := by
    unfold W2f
    rw [show srcCell = i1 RequestSelect.rowC from rfl, bank_at]
    show (rawRowCodec q₁ q₂ s C.1 (defaultItemCodec n s)).encode (y.2 (x y.1).1) = _
    rw [hraw]
    exact TemplateStep.rawrow_template_encode k pp z
  let S := Function.update (W2f k x y) srcCell (List.replicate pp.val true ++ false :: TW)
  have hSx : ∀ xx, xx ≠ srcCell → (∀ yy, xx ≠ r1 yy) → xx ≠ nC 2 → xx ≠ nC 3 →
      S xx = W1 xx := by
    intro xx h0 h1 h2 h3
    simp only [S]
    rw [Function.update_of_ne h0]
    unfold W2f
    exact TemplateStep.i1_off W1 _ xx h1 h2 h3
  have hW1r : ∀ xx, W1 (.inr xx) = W0f k x y (.inr xx) := fun xx =>
    TemplateStep.bank_iN_inr _ _ xx
  have hW1l : ∀ yy, W1 (.inl yy) = NavJoin.jb (NavJoin.outVec n p s q₁ q₂ w Q k) yy :=
    fun yy => TemplateStep.bank_iN_inl _ _ yy
  obtain ⟨ta, hta, va, F, pa, hFr, hFl⟩ := TemplateStep.arm_run (n := n) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k (x y.1).2 (ξ k) pp z S
    (by simp only [S]; rw [Function.update_self])
    (by rw [hSx _ (by simp [pcC, srcCell, r1]) (by intro yy; simp [pcC, r1])
          (by simp [pcC, nC]) (by simp [pcC, nC]), show pcC = .inr (.inr (.inr (.inr 0))) from rfl,
          hW1r]; rfl)
    (fun j => by
      rw [hSx _ (by simp [lC, srcCell, r1]) (by intro yy; simp [lC, r1])
          (by simp [lC, nC]) (by simp [lC, nC]), show lC j = .inr (.inr (.inr (.inl j))) from rfl,
          hW1r]; rfl)
    (by rw [hSx _ (by simp [myJ, srcCell, r1]) (by intro yy; simp [myJ, r1])
          (by simp [myJ, nC]) (by simp [myJ, nC]), show myJ = .inr (.inr (.inr (.inr 1))) from rfl,
          hW1r]; rfl)
    (by
      simp only [S]
      rw [Function.update_of_ne (by simp [srcCell, r1, RequestSelect.tagC, RequestSelect.rowC])]
      unfold W2f
      exact bank_at i1 W1 _ RequestSelect.tagC)
    (by rw [hSx _ (by simp [nC, srcCell, r1]) (by intro yy; simp [nC, r1])
          (by simp [nC]) (by simp [nC]), show nC 6 = .inl (.inr 6) from rfl, hW1l]; rfl)
    (by rw [hSx _ (by simp [nC, srcCell, r1]) (by intro yy; simp [nC, r1])
          (by simp [nC]) (by simp [nC]), show nC 7 = .inl (.inr 7) from rfl, hW1l]; rfl)
    (by rw [hSx _ (by simp [nC, srcCell, r1]) (by intro yy; simp [nC, r1])
          (by simp [nC]) (by simp [nC]), show nC 8 = .inl (.inr 8) from rfl, hW1l]; rfl)
    (by rw [hSx _ (by simp [nC, srcCell, r1]) (by intro yy; simp [nC, r1])
          (by simp [nC]) (by simp [nC]), show nC 4 = .inl (.inr 4) from rfl, hW1l]; rfl)
    (fun xx => by
      rw [hSx _ (by simp [r2, srcCell, r1]) (by intro yy; simp [r2, r1])
          (by simp [r2, nC]) (by simp [r2, nC]), show r2 xx = .inr (.inr (.inl xx)) from rfl,
          hW1r]; rfl)
  have pa' := liftT inJ arm (Sum.elim S E0) _ _ (fun _ => rfl) _ _ _ _ pa
  rw [bank_inJ] at pa'
  -- the dispatch on the raw-row sum bit
  obtain ⟨td, htd, qd⟩ := TagDispatch.if_false (inJ srcCell) armX srcP armStart srcPStart
    armCtl srcPCtl (Sum.elim (W2f k x y) E0) (List.replicate pp.val true ++ false :: TW)
    hsrcW2 ta va _
    (by rw [show inJ srcCell = .inl srcCell from rfl, Sum.update_elim_inl]; exact pa')
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs preX
    (TagDispatch.ifProgram (inJ srcCell) armX srcP armStart srcPStart armCtl srcPCtl)
    (leftLabel NavJoin.startLabel) (.inl ()) (NavJoin.ctl, RequestSelect.startControl)
    v1 ((none : Option Bool), (armCtl, srcPCtl))
    (some false, (va, srcPCtl)) _ _ _ _ _ q1' qd
  refine ⟨u2, ?_, _, F, q2, hFr, hFl⟩
  have hta' : ta ≤ (pp.val + 1) + LocateUniform.locBound q₁ q₂ s C.2 c.2 pp.val (x y.1).2 + 1 +
      RequestSelect.clock OW o.1.val (z o.1).1.val (.append (.ticket q₁) c.1) c.2
        (List.ofFn (fun a => (prodCodec (finCodec q₁) C.1).encode (z a)))
        (List.ofFn (fun b => C.2.encode (o.2 b))) + 1 := hta
  omega

/-- The source case of the ONE fixed program `stepX` (root decision R5), every tag. -/
theorem source_stepX (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] [NeZero s]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r) (k : ℕ)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q (k + 1))
    (i : SourceConstruction.Items s (Fin g.vertices))
    (uu : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q k)
    (hraw : y.2 (x y.1).1 = .inr (i, uu))
    (hfix : ∀ js : Fin s → SourceMatrix.OuterColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k),
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode
        (SourceMatrix.sourceColumn (SourceActiveRank.scanAtCanonical
          (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) i
          (SourceMatrix.forgetTag (ξ k) (.fixedTail js))) = (words p s q₁ q₂ w Q k).2) :
    let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k
    let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by omega) hq
    let req := RecursiveEntries.request activity ξ k x y
    ∃ t ≤ NavJoin.joinBound g.vertices p s q₁ q₂ w Q k + selClock k x y + 1 +
        ((SrcX.srcXBound g hg hs r hq k i (ξ k) [] (x y.1).2 +
          (2 * (C.2.encode (SourceMatrix.sourceColumn activity i
            (SourceMatrix.forgetTag (ξ k) (x y.1).2))).length + 2) + 1 +
          (2 * (C.1.encode uu).length + 2) + 1) + 1) + 1,
      ∃ v, ∃ F : JT → List Bool,
      ((advance stepX)^[t])
        (⟨some (leftLabel (leftLabel NavJoin.startLabel)), stepXCtl,
          Sum.elim (W0f k x y) (SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w)
            (Q := Q) g r k [] [])⟩ : TM2.Cfg (fun _ : JT => Bool) _ _) =
        ⟨none, v, F⟩ ∧
      F (.inl (r2 RequestSelect.tagC)) = C.1.encode req.1 ∧
      F (.inl (r2 RequestSelect.rowC)) = C.2.encode req.2 ∧
      ∀ xx : J, xx ≠ srcCell → xx ≠ r1 RequestSelect.tagC → xx ≠ nC 4 → xx ≠ nC 7 →
        xx ≠ r2 RequestSelect.tagC → xx ≠ r2 RequestSelect.rowC → F (.inl xx) = W2f k x y xx := by
  intro C activity req
  have hreq : req = (uu, SourceMatrix.sourceColumn activity i
      (SourceMatrix.forgetTag (ξ k) (x y.1).2)) :=
    SrcReq.request_source activity ξ k x y i uu hraw
  let E0 := SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k [] []
  -- the prefix, transported by `inJ`
  obtain ⟨u1, hu1, v1, q1⟩ := pre_run hp hs k x y
  have q1' := liftT inJ pre (Sum.elim (W0f k x y) E0) _ _ (fun _ => rfl) _ _ _ _ q1
  rw [bank_inJ] at q1'
  let rowW := (prodCodec (defaultItemCodec g.vertices s) C.1).encode (i, uu)
  have hsrcW2 : W2f k x y srcCell = true :: rowW := by
    unfold W2f
    rw [show srcCell = i1 RequestSelect.rowC from rfl, bank_at]
    show (rawRowCodec q₁ q₂ s C.1 (defaultItemCodec g.vertices s)).encode (y.2 (x y.1).1) = _
    rw [hraw]
    rfl
  -- the three-tag source arm, placed by `ιE`
  obtain ⟨t2, ht2, v2, F2, l2, h1, h2⟩ := SrcX.srcX_run (w := w) (Q := Q)
    g hg hp hs r hq k i uu (ξ k) (x y.1).2 [] hfix
  let WS := Function.update (W2f k x y) srcCell rowW
  let WTs : JT → List Bool := Sum.elim WS E0
  have hS : ∀ zz, SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k
      rowW ((taggedColumnCodec q₁ q₂ s C.2).encode (x y.1).2 ++ []) zz = WTs (ιE zz) := by
    intro zz
    by_cases e1 : zz = SrcX.srcAX
    · subst e1
      rw [ιE_srcA]
      show rowW = WS srcCell
      simp only [WS, Function.update_self]
    by_cases e2 : zz = SrcX.fwX
    · subst e2
      rw [ιE_fw, List.append_nil]
      show (taggedColumnCodec q₁ q₂ s C.2).encode (x y.1).2 = WS (r1 RequestSelect.tagC)
      simp only [WS]
      rw [Function.update_of_ne (by simp [srcCell, r1, RequestSelect.tagC, RequestSelect.rowC])]
      unfold W2f
      rw [show r1 RequestSelect.tagC = i1 RequestSelect.tagC from rfl, bank_at]
      rfl
    by_cases e3 : zz = ccX
    · subst e3
      rw [ιE_cc]
      show _ = WS (nC 4)
      simp only [WS]
      rw [Function.update_of_ne (by simp [srcCell, r1, nC])]
      unfold W2f
      rw [TemplateStep.i1_off _ _ _ (by intro yy; simp [nC, r1]) (by simp [nC]) (by simp [nC]),
        show nC 4 = .inl (.inr 4) from rfl, TemplateStep.bank_iN_inl]
      rfl
    by_cases e4 : zz = rcX
    · subst e4
      rw [ιE_rc]
      show _ = WS (nC 7)
      simp only [WS]
      rw [Function.update_of_ne (by simp [srcCell, r1, nC])]
      unfold W2f
      rw [TemplateStep.i1_off _ _ _ (by intro yy; simp [nC, r1]) (by simp [nC]) (by simp [nC]),
        show nC 7 = .inl (.inr 7) from rfl, TemplateStep.bank_iN_inl]
      rfl
    rw [ιE_other zz e1 e2 e3 e4]
    exact WXb_irrel g r k _ _ zz e1 e2
  have l2' := liftT ιE SrcX.srcX WTs _ _ hS _ _ _ _ l2
  -- copy 1: the column word into `r2 rowC`
  let WT3 := bank ιE WTs F2
  have hlblX : SrcX.lblX ≠ SrcX.srcAX ∧ SrcX.lblX ≠ SrcX.fwX ∧ SrcX.lblX ≠ ccX ∧
      SrcX.lblX ≠ rcX := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [SrcX.lblX, SrcX.srcAX, SrcU.srcA, SrcX.fwX, ccX, rcX,
      OTBody.lblB, FetchIndexed.fwC, FetchIndexed.ccC, FetchIndexed.rcC]
  have hz1 : WT3 (cpC 2) = [] := by
    show bank ιE WTs F2 (.inr SrcX.srcAX) = []
    rw [bank_outside ιE _ _ _ ιE_range_srcA]
    rfl
  have h0 : WT3 (cpC 0) = F2 SrcX.lblX := by
    show bank ιE WTs F2 (.inr SrcX.lblX) = _
    rw [← ιE_other SrcX.lblX hlblX.1 hlblX.2.1 hlblX.2.2.1 hlblX.2.2.2, bank_at]
  have hne1 : r2 RequestSelect.rowC ≠ srcCell := by simp [r2, srcCell, r1]
  have hne2 : r2 RequestSelect.rowC ≠ r1 RequestSelect.tagC := by simp [r2, r1]
  have hne3 : r2 RequestSelect.rowC ≠ nC 4 := by simp [r2, nC]
  have hne4 : r2 RequestSelect.rowC ≠ nC 7 := by simp [r2, nC]
  have hl1 : WT3 (cpC 1) = [] := by
    show bank ιE WTs F2 (.inl (r2 RequestSelect.rowC)) = []
    rw [bank_outside ιE _ _ _ (ιE_range_inl _ hne1 hne2 hne3 hne4)]
    show WS (r2 RequestSelect.rowC) = []
    simp only [WS]
    rw [Function.update_of_ne hne1]
    exact W2f_r2 k x y _
  have l3 := MatrixStage4ScalarPreparationOps.copy_run cpC WT3 hz1
  rw [h0, hl1, h1, List.append_nil] at l3
  let colW := C.2.encode (SourceMatrix.sourceColumn activity i
    (SourceMatrix.forgetTag (ξ k) (x y.1).2))
  let WT4 := Function.update WT3 (cpC 1) colW
  -- copy 2: the row word into `r2 tagC`
  have hm1 : r2 RequestSelect.tagC ≠ srcCell := by simp [r2, srcCell, r1]
  have hm2 : r2 RequestSelect.tagC ≠ r1 RequestSelect.tagC := by simp [r2, r1]
  have hm3 : r2 RequestSelect.tagC ≠ nC 4 := by simp [r2, nC]
  have hm4 : r2 RequestSelect.tagC ≠ nC 7 := by simp [r2, nC]
  have hm5 : r2 RequestSelect.tagC ≠ r2 RequestSelect.rowC := by
    simp [r2, RequestSelect.tagC, RequestSelect.rowC]
  have hz2 : WT4 (cpR 2) = [] := by
    show Function.update WT3 (cpC 1) colW (.inr SrcX.srcAX) = []
    rw [Function.update_of_ne (by simp [cpC, cpCf])]
    exact hz1
  have h0' : WT4 (cpR 0) = F2 SrcX.srcAX := by
    show Function.update WT3 (cpC 1) colW (.inl srcCell) = _
    rw [Function.update_of_ne (by simp [cpC, cpCf, srcCell, r1, r2])]
    show bank ιE WTs F2 (.inl srcCell) = _
    rw [← ιE_srcA, bank_at]
  have hl2 : WT4 (cpR 1) = [] := by
    show Function.update WT3 (cpC 1) colW (.inl (r2 RequestSelect.tagC)) = []
    rw [Function.update_of_ne (by
      show (Sum.inl (r2 RequestSelect.tagC) : JT) ≠ .inl (r2 RequestSelect.rowC)
      exact fun h => hm5 (Sum.inl_injective h))]
    show bank ιE WTs F2 (.inl (r2 RequestSelect.tagC)) = []
    rw [bank_outside ιE _ _ _ (ιE_range_inl _ hm1 hm2 hm3 hm4)]
    show WS (r2 RequestSelect.tagC) = []
    simp only [WS]
    rw [Function.update_of_ne hm1]
    exact W2f_r2 k x y _
  have l4 := MatrixStage4ScalarPreparationOps.copy_run cpR WT4 hz2
  rw [h0', hl2, h2, List.append_nil] at l4
  -- sequencing inside the source arm
  obtain ⟨ua, hua, qa⟩ := BitMachineRawSequence.runs srcXT cp1 (.inl ())
    BitMachineCopy.Label.scan SrcX.srcXCtl v2 (none : Option Bool) none _ _ _ _ _ l2' l3
  obtain ⟨ub, hub, qb⟩ := BitMachineRawSequence.runs srcP1 cp2 (leftLabel (.inl ()))
    BitMachineCopy.Label.scan (SrcX.srcXCtl, (none : Option Bool))
    (SrcX.srcXCtl, (none : Option Bool)) (none : Option Bool) none _ _ _ _ _ qa l4
  -- the dispatch on the raw-row sum bit
  obtain ⟨td, htd, qd⟩ := TagDispatch.if_true (inJ srcCell) armX srcP armStart srcPStart
    armCtl srcPCtl (Sum.elim (W2f k x y) E0) rowW hsrcW2 ub _ _
    (by rw [show inJ srcCell = .inl srcCell from rfl, Sum.update_elim_inl]; exact qb)
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs preX
    (TagDispatch.ifProgram (inJ srcCell) armX srcP armStart srcPStart armCtl srcPCtl)
    (leftLabel NavJoin.startLabel) (.inl ()) (NavJoin.ctl, RequestSelect.startControl)
    v1 ((none : Option Bool), (armCtl, srcPCtl)) _ _ _ _ _ _ q1' qd
  refine ⟨u2, ?_, _, _, q2, ?_, ?_, ?_⟩
  · have hua' : ua ≤ t2 + (2 * (C.2.encode (SourceMatrix.sourceColumn activity i
        (SourceMatrix.forgetTag (ξ k) (x y.1).2))).length + 2) + 1 := hua
    have hub' : ub ≤ ua + (2 * (C.1.encode uu).length + 2) + 1 := hub
    have ht2' : t2 ≤ SrcX.srcXBound g hg hs r hq k i (ξ k) [] (x y.1).2 := ht2
    omega
  · show Function.update WT4 (cpR 1) (C.1.encode uu) (cpR 1) = _
    rw [Function.update_self, hreq]
  · show Function.update WT4 (cpR 1) (C.1.encode uu) (.inl (r2 RequestSelect.rowC)) = _
    rw [Function.update_of_ne (by
      show (Sum.inl (r2 RequestSelect.rowC) : JT) ≠ .inl (r2 RequestSelect.tagC)
      exact fun h => hm5 (Sum.inl_injective h).symm)]
    show Function.update WT3 (cpC 1) colW (cpC 1) = _
    rw [Function.update_self, hreq]
  · intro xx n1 n2 n3 n4 n5 n6
    show Function.update WT4 (cpR 1) (C.1.encode uu) (.inl xx) = _
    rw [Function.update_of_ne (by
      show (Sum.inl xx : JT) ≠ .inl (r2 RequestSelect.tagC)
      exact fun h => n5 (Sum.inl_injective h))]
    show Function.update WT3 (cpC 1) colW (.inl xx) = _
    rw [Function.update_of_ne (by
      show (Sum.inl xx : JT) ≠ .inl (r2 RequestSelect.rowC)
      exact fun h => n6 (Sum.inl_injective h))]
    show bank ιE WTs F2 (.inl xx) = _
    rw [bank_outside ιE _ _ _ (ιE_range_inl xx n1 n2 n3 n4)]
    show WS xx = _
    simp only [WS]
    rw [Function.update_of_ne n1]

end

#print axioms WXb_irrel
#print axioms template_stepX
#print axioms source_stepX

end Paper2.TemplateStepX
