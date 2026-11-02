import Paper2.TemplateStep

/-! Unit 3, segment (2), the composite: the ONE fixed program
`TemplateStep.step Src` run on ONE bank from the serialized level-`k+1`
codes and label words, for every level-`k+1` pair `(x, y)` whose requested
raw row `y.2 (x y.1).1` is a template row. It halts with the encoded
`RecursiveEntries.request activity ξ k x y` in the two output label cells
of the second `RequestSelect` bank, for every `activity` and every tail
family `ξ` (the template case reads neither). The source arm `Src` is a
parameter (segment 3); its label/control types are arbitrary. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.TemplateStep

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries
open BitMachineRawSequence (leftLabel)

theorem W1_eq (W : J → List Bool) (T : NavJoin.Stack → List Bool) :
    bank iN W T = Sum.elim T (fun x => W (.inr x)) := by
  funext j
  rcases j with j | j
  · exact bank_iN_inl W T j
  · exact bank_iN_inr W T j

theorem i1_off (W : J → List Bool) (T : RS → List Bool) (x : J) (h1 : ∀ y, x ≠ r1 y)
    (h2 : x ≠ nC 2) (h3 : x ≠ nC 3) : bank i1 W T x = W x := by
  apply bank_outside i1 W T x
  rintro ⟨k, hk⟩
  rcases k with j | j | q
  · exact h1 _ hk.symm
  · exact h1 _ hk.symm
  · fin_cases q
    · exact h1 _ hk.symm
    · exact h1 _ hk.symm
    · exact h2 hk.symm
    · exact h3 hk.symm
    · exact h1 _ hk.symm
    · exact h1 _ hk.symm
    · exact h1 _ hk.symm
    · exact h1 _ hk.symm

theorem rawrow_template_encode {n p s q₁ q₂ w Q : ℕ} (k : ℕ) (pp : Fin s)
    (z : SourceMatrix.Template q₁ q₂
      (Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)) :
    (rawRowCodec q₁ q₂ s (defaultCarrierCodecs n p s q₁ q₂ w Q k).1
      (defaultItemCodec n s)).encode (.inl (pp, z)) =
      false :: (List.replicate pp.val true ++ false ::
        (piCodec (prodCodec (finCodec q₁) (defaultCarrierCodecs n p s q₁ q₂ w Q k).1) q₂).encode z) := by
  change false :: ((finCodec s).encode pp ++ _) = _
  simp [finCodec]

variable {n p s q₁ q₂ w Q : ℕ} [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

/-- Segment (2): one request level, template case, one bank, one program. -/
theorem template_step {LS VS : Type*} (Src : LS → TM2.Stmt (fun _ : J => Bool) LS VS)
    (srcStart : LS) (srcCtl : VS) [NeZero s]
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
    let D := defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)
    let c := seedRecursiveCodes n p s q₁ q₂ w Q k
    let c' := seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)
    let E : Code := .append (.ticket w) (taggedCode q₁ q₂ s c.2)
    let G : Code := graphRowsCode (V := Fin n) q₁ q₂ s c.1
    let rrow := rawRowCodec q₁ q₂ s C.1 (defaultItemCodec n s)
    let o := (SourceMatrix.forgetTag (ξ k) (x y.1).2).2 pp
    let TW := (piCodec (prodCodec (finCodec q₁) C.1) q₂).encode z
    let OW := (outerColumnCodec q₁ q₂ s C.2).encode o
    let W0 : J → List Bool :=
      Sum.elim (NavJoin.jb (NavJoin.inVec (encodeCode c'.1) (encodeCode c'.2)))
        (Sum.elim (RequestSelect.mk [] [] (RequestSelect.vec (D.1.encode x) (D.2.encode y)
          [] [] [] [] [])) (fun _ => []))
    let W1 := bank iN W0 (NavJoin.jb (NavJoin.outVec n p s q₁ q₂ w Q k))
    let W2 := bank i1 W1 (RequestSelect.mk ((taggedColumnCodec q₁ q₂ s C.2).encode (x y.1).2)
      (rrow.encode (y.2 (x y.1).1))
      (RequestSelect.vec (D.1.encode x) (D.2.encode y) (encodeCode E) (encodeCode G)
        (List.replicate y.1.val true) ((piCodec rrow w).encode y.2)
        (List.replicate (x y.1).1.val true)))
    let S1 := Function.update (Function.update (Function.update W2 srcCell
      (List.replicate pp.val true ++ false :: TW)) srcCell TW) pcC (List.replicate pp.val true)
    ∃ t ≤ NavJoin.joinBound n p s q₁ q₂ w Q k +
        RequestSelect.clock (D.2.encode y) y.1.val (x y.1).1.val E G
          (List.ofFn (fun j => (prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s C.2)).encode (x j)))
          (List.ofFn (fun i => rrow.encode (y.2 i))) + 1 +
        ((pp.val + 1) + LocateUniform.locBound q₁ q₂ s C.2 c.2 pp.val (x y.1).2 + 1 +
          RequestSelect.clock OW o.1.val (z o.1).1.val (.append (.ticket q₁) c.1) c.2
            (List.ofFn (fun a => (prodCodec (finCodec q₁) C.1).encode (z a)))
            (List.ofFn (fun b => C.2.encode (o.2 b))) + 1 + 1) + 1,
      ∃ v, ∃ F : J → List Bool,
      ((advance (step Src srcStart srcCtl))^[t])
        (⟨some (leftLabel (leftLabel NavJoin.startLabel)), stepCtl srcCtl, W0⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, bank i2 F (RequestSelect.mk (C.1.encode (RecursiveEntries.request activity ξ k x y).1)
          (C.2.encode (RecursiveEntries.request activity ξ k x y).2)
          (RequestSelect.vec TW OW (encodeCode (.append (.ticket q₁) c.1)) (encodeCode c.2)
            (List.replicate o.1.val true) ((piCodec C.2 (q₁ + s + 1)).encode o.2)
            (List.replicate (z o.1).1.val true)))⟩ ∧
      LocateUniform.Frame eL S1 F ∧ F (lC FetchLabel.lblC) = OW := by
  intro C D c c' E G rrow o TW OW W0 W1 W2 S1
  have hreq : RecursiveEntries.request activity ξ k x y = ((z o.1).2, SourceMatrix.head o.2 (z o.1).1) := by
    unfold RecursiveEntries.request
    rw [hraw]
    rfl
  rw [hreq]
  -- phase 1: the code join, transported by `iN`
  obtain ⟨t1, ht1, p1⟩ := NavJoin.join_run (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) (NeZero.pos Q) (NeZero.pos w) (by omega) (NeZero.pos q₂) k
  have l1 := lift iN NavJoin.program W0 _ _ (fun _ => rfl) _ _ _ _ p1
  -- phase 2: request selection, transported by `i1`
  obtain ⟨t2, ht2, v2, p2⟩ := RequestSelectActual.select_run (n := n) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k x y
  have hW1 : W1 = Sum.elim (NavJoin.jb (NavJoin.outVec n p s q₁ q₂ w Q k))
      (fun x => W0 (.inr x)) := W1_eq W0 _
  have hS1 : ∀ kk, RequestSelect.mk [] [] (RequestSelect.vec (D.1.encode x) (D.2.encode y)
      (encodeCode E) (encodeCode G) [] [] []) kk = W1 (i1 kk) := by
    intro kk
    rw [hW1]
    rcases kk with j | j | q
    · rfl
    · rfl
    · fin_cases q <;> rfl
  have l2 := lift i1 RequestSelect.program W1 _ _ hS1 _ _ _ _ p2
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs navP rs1 NavJoin.startLabel
    RequestSelect.startLabel NavJoin.ctl NavJoin.ctl RequestSelect.startControl v2
    _ _ _ _ _ l1 l2
  -- phase 3: the template arm on the updated bank
  have hsrcW2 : W2 srcCell = false :: (List.replicate pp.val true ++ false :: TW) := by
    have h := bank_at i1 W1 (RequestSelect.mk ((taggedColumnCodec q₁ q₂ s C.2).encode (x y.1).2)
      (rrow.encode (y.2 (x y.1).1))
      (RequestSelect.vec (D.1.encode x) (D.2.encode y) (encodeCode E) (encodeCode G)
        (List.replicate y.1.val true) ((piCodec rrow w).encode y.2)
        (List.replicate (x y.1).1.val true))) RequestSelect.rowC
    refine h.trans ?_
    show rrow.encode (y.2 (x y.1).1) = _
    rw [hraw]
    exact rawrow_template_encode k pp z
  let S := Function.update W2 srcCell (List.replicate pp.val true ++ false :: TW)
  have hSx : ∀ xx, xx ≠ srcCell → (∀ yy, xx ≠ r1 yy) → xx ≠ nC 2 → xx ≠ nC 3 →
      S xx = W1 xx := by
    intro xx h0 h1 h2 h3
    simp only [S]
    rw [Function.update_of_ne h0]
    exact i1_off W1 _ xx h1 h2 h3
  have hW1r : ∀ xx, W1 (.inr xx) = W0 (.inr xx) := fun xx => bank_iN_inr W0 _ xx
  have hW1l : ∀ yy, W1 (.inl yy) = NavJoin.jb (NavJoin.outVec n p s q₁ q₂ w Q k) yy :=
    fun yy => bank_iN_inl W0 _ yy
  obtain ⟨ta, hta, va, F, pa, hFr, hFl⟩ := arm_run (n := n) (p := p) (s := s) (q₁ := q₁)
    (q₂ := q₂) (w := w) (Q := Q) hp hs k (x y.1).2 (ξ k) pp z S
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
  -- phase 4: the dispatch on the raw-row sum bit
  obtain ⟨td, htd, qd⟩ := TagDispatch.if_false srcCell arm Src armStart srcStart armCtl srcCtl
    W2 (List.replicate pp.val true ++ false :: TW) hsrcW2 ta va _ pa
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs pre
    (TagDispatch.ifProgram srcCell arm Src armStart srcStart armCtl srcCtl)
    (leftLabel NavJoin.startLabel) (.inl ()) (NavJoin.ctl, RequestSelect.startControl)
    (NavJoin.ctl, v2) ((none : Option Bool), (armCtl, srcCtl))
    (some false, (va, srcCtl)) _ _ _ _ _ q1 qd
  refine ⟨u2, ?_, _, F, q2, hFr, hFl⟩
  have ht1' : t1 ≤ NavJoin.joinBound n p s q₁ q₂ w Q k := ht1
  have ht2' : t2 ≤ RequestSelect.clock (D.2.encode y) y.1.val (x y.1).1.val E G
      (List.ofFn (fun j => (prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s C.2)).encode (x j)))
      (List.ofFn (fun i => rrow.encode (y.2 i))) := ht2
  have hta' : ta ≤ (pp.val + 1) + LocateUniform.locBound q₁ q₂ s C.2 c.2 pp.val (x y.1).2 + 1 +
      RequestSelect.clock OW o.1.val (z o.1).1.val (.append (.ticket q₁) c.1) c.2
        (List.ofFn (fun a => (prodCodec (finCodec q₁) C.1).encode (z a)))
        (List.ofFn (fun b => C.2.encode (o.2 b))) + 1 := hta
  omega

/-- Read-out: the two output label cells hold the encoded request pair. -/
theorem out_cells (F : J → List Bool) (a b X Y E G jw R iw : List Bool) :
    bank i2 F (RequestSelect.mk a b (RequestSelect.vec X Y E G jw R iw))
        (r2 RequestSelect.tagC) = a ∧
    bank i2 F (RequestSelect.mk a b (RequestSelect.vec X Y E G jw R iw))
        (r2 RequestSelect.rowC) = b :=
  ⟨bank_at i2 F _ RequestSelect.tagC, bank_at i2 F _ RequestSelect.rowC⟩

end

#print axioms W1_eq
#print axioms i1_off
#print axioms rawrow_template_encode
#print axioms template_step
#print axioms out_cells

end Paper2.TemplateStep
