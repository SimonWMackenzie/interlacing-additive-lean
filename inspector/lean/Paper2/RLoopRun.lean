import Paper2.RLoopBody

/-! Unit 3, segment (2): `body_run`, ONE run of the ONE fixed loop body from the
level-`k+1` loop bank (counter holding `k` marks) to EXACTLY the level-`k` loop
bank of `RecursiveEntries.request activity ξ k x y`. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.RLoop

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries
open BitMachineRawSequence (leftLabel)
open Paper2.TemplateStep (J RS nC r1 r2 lC pcC myJ iN i1 i2 eL srcCell)
open Paper2.TemplateStepX (JT ccX rcX W0f W2f selClock stepX stepXCtl)

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

theorem B0_inr (g : EncodedGraph.Graph) (r k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q (k + 1))
    (x' : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q k)
    (y' : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q k) (c : SrcX.JX ⊕ Fin 2) :
    Function.update (bankL g r (k + 1) x y) ctr (List.replicate k true) (.inr c) =
      bankL g r k x' y' (.inr c) := by
  rcases c with z | i
  · rw [Function.update_of_ne (by simp [ctr])]
    rfl
  · fin_cases i
    · show Function.update _ ctr _ ctr = _
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne (by simp [ctr])]
      rfl

theorem body_run (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (k : ℕ)
    (hfix : ∀ (i : SourceConstruction.Items s (Fin g.vertices))
      (js : Fin s → SourceMatrix.OuterColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k)),
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode
        (SourceMatrix.sourceColumn (SourceActiveRank.scanAtCanonical
          (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) i
          (SourceMatrix.forgetTag (ξ k) (.fixedTail js))) =
        (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q k).2)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q (k + 1)) :
    let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by omega) hq
    let req := RecursiveEntries.request activity ξ k x y
    ∃ t ≤ bodyClock g hg hs r hq ξ k x y, ∃ v,
      ((advance body)^[t])
        (⟨some bodyStart, bodyCtl,
          Function.update (bankL g r (k + 1) x y) ctr (List.replicate k true)⟩ :
          TM2.Cfg (fun _ : JL => Bool) _ _) =
        ⟨none, v, bankL g r k req.1 req.2⟩ := by
  intro activity req
  set C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k with hC
  set c := seedRecursiveCodes g.vertices p s q₁ q₂ w Q k with hc
  set c' := seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1) with hc'
  set B0 := Function.update (bankL (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    g r (k + 1) x y) ctr (List.replicate k true) with hB0
  set E0 := E0k (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k with hE0def
  set Tst := stepClock g hg hs r hq ξ k x y with hTst
  -- (1) preparation copies
  set Lp := (∑ z : SrcX.JX, (master (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    g r z).length) + k with hLp
  have hB0scr : B0 scr = [] := by
    rw [hB0, Function.update_of_ne (by simp [scr, ctr])]; rfl
  have hB0e : ∀ z, B0 (eX z) = [] := by
    intro z; rw [hB0, Function.update_of_ne (by simp [eX, ctr])]; rfl
  obtain ⟨t1, ht1, v1, r1run⟩ := CopyAll.all_run prepCps prep_hsd prep_hzd prep_hdd B0
    (fun i => by rw [prep_scr]; exact hB0scr) Lp
    (by
      intro i
      rw [prep_src]
      unfold prepSrc
      split_ifs with hm
      · rw [hB0, Function.update_self]; simp [hLp]
      · rw [hB0, Function.update_of_ne (by simp [mX, ctr])]
        show (master g r (exX i)).length ≤ _
        have := Finset.single_le_sum (f := fun z => (master (p := p) (s := s) (q₁ := q₁)
          (q₂ := q₂) (w := w) (Q := Q) g r z).length) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ (exX i))
        simp only at this
        omega)
    oc
  set B1 := CopyAll.done prepCps NX B0 with hB1
  have hB1off : ∀ a, (∀ z, a ≠ eX z) → B1 a = B0 a := fun a ha =>
    CopyAll.done_off prepCps B0 a (prep_notdst a ha) NX
  have hB1e : ∀ z, B1 (eX z) = E0 z := by
    intro z
    have hz : eX z = prepCps (exX.symm z) 1 := by rw [prep_dst, Equiv.apply_symm_apply]
    rw [hz, hB1, CopyAll.done_dst prepCps prep_hdd B0, prep_src, ← hz, hB0e, List.append_nil,
      Equiv.apply_symm_apply, hE0def]
    unfold prepSrc E0k
    split_ifs with hm
    · rw [hB0, Function.update_self]
    · rw [hB0, Function.update_of_ne (by simp [mX, ctr])]; rfl
  have hS1 : ∀ a : JT, Sum.elim (W0f k x y) E0 a = B1 (inT a) := by
    intro a
    rcases a with j | z
    · show W0f k x y j = B1 (.inl (.inl j))
      rw [hB1off _ (by intro z; simp [eX]), hB0, Function.update_of_ne (by simp [ctr])]
      rfl
    · exact (hB1e z).symm
  -- (2) the one-level program
  obtain ⟨t2, ht2, v2, F, r2run, hF0, hF1, hFt, hFr⟩ := stepK g hg hp hs r hq ξ k hfix x y E0
    (fun z h1 h2 h3 h4 => E0k_hE0 g r k z h1 h2 h3 h4) (E0k_srcA g r k)
  have r2L := liftL inT stepX B1 _ F hS1 _ _ _ _ r2run
  set B2 := bank inT B1 F with hB2
  obtain ⟨u1, hu1, s1⟩ := BitMachineRawSequence.runs prep stepL (.inl ⟨0, by omega⟩)
    (leftLabel (leftLabel NavJoin.startLabel)) oc v1 stepXCtl v2 B0 B1 B2 t1 t2 r1run r2L
  -- (3) clear every JT cell but four
  set Lc := (∑ a : JT, ((Sum.elim (W0f k x y) E0) a).length) + StepXGrowth.pushBound * Tst
    with hLc
  have hB2l : ∀ b : JT, B2 (.inl b) = F b := fun b => bank_at inT B1 F b
  have hB2r : ∀ cc, B2 (.inr cc) = B1 (.inr cc) := fun cc =>
    bank_outside inT B1 F (.inr cc) (by rintro ⟨kk, hkk⟩; cases hkk)
  obtain ⟨t3, ht3, v3, r3run⟩ := ClearAll.all_run cl1 cl1_injective Lc B2
    (by
      intro j
      show (B2 (.inl (e1 j).1)).length ≤ Lc
      rw [hB2l]
      have hg1 := StepXGrowth.exit_length_le _ t2 Tst ht2 v2 F r2run (e1 j).1
      change (F (e1 j).1).length ≤ ((Sum.elim (W0f k x y) E0) (e1 j).1).length +
        StepXGrowth.pushBound * Tst at hg1
      have := Finset.single_le_sum (f := fun a => ((Sum.elim (W0f k x y) E0) a).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (e1 j).1)
      change ((Sum.elim (W0f k x y) E0) (e1 j).1).length ≤
        ∑ a : JT, ((Sum.elim (W0f k x y) E0) a).length at this
      rw [hLc]
      omega)
    oc
  set B3 := ClearAll.clearFrom cl1 0 B2 with hB3
  obtain ⟨u2, hu2, s2⟩ := BitMachineRawSequence.runs b1 (ClearAll.prog cl1)
    (leftLabel (.inl ⟨0, by omega⟩)) ⟨0, by omega⟩ ctl1 (oc, v2) oc v3 B0 B2 B3 u1 t3 s1 r3run
  -- (4) the navigation join, rerun
  have hS4 : ∀ xx : NavJoin.Stack,
      NavJoin.jb (NavJoin.inVec (encodeCode c'.1) (encodeCode c'.2)) xx = B3 (iNL xx) := by
    intro xx
    rcases xx with ce | i
    · rw [hB3, clr_in cl1 B2 (iNL (.inl ce)) (cl1_mem (.inl (.inl (.inl ce)))
        (by simp [keep, nC, r2]))]
      rfl
    · fin_cases i
      · show NavJoin.jb _ (.inr 0) = B3 (iNL (.inr 0))
        rw [hB3, clr_out cl1 B2 (iNL (.inr 0)) (cl1_not (.inl (nC 0)) (Or.inl rfl))]
        show _ = B2 (.inl (.inl (nC 0)))
        rw [hB2l, hF0]; rfl
      · show NavJoin.jb _ (.inr 1) = B3 (iNL (.inr 1))
        rw [hB3, clr_out cl1 B2 (iNL (.inr 1)) (cl1_not (.inl (nC 1)) (Or.inr (Or.inl rfl)))]
        show _ = B2 (.inl (.inl (nC 1)))
        rw [hB2l, hF1]; rfl
      all_goals
        rw [hB3, clr_in cl1 B2 (iNL (.inr _)) (cl1_mem (.inl (.inl (.inr _)))
          (by simp [keep, nC, r2]))]
        rfl
  obtain ⟨t4, ht4, r4run⟩ := NavJoin.join_run (n := g.vertices) (p := p) (s := s) (q₁ := q₁)
    (q₂ := q₂) (w := w) (Q := Q) (NeZero.pos Q) (NeZero.pos w) (by omega) (NeZero.pos q₂) k
  have r4L := liftL iNL NavJoin.program B3 _ _ hS4 _ _ _ _ r4run
  set B4 := bank iNL B3 (NavJoin.jb (NavJoin.outVec g.vertices p s q₁ q₂ w Q k)) with hB4
  obtain ⟨u3, hu3, s3⟩ := BitMachineRawSequence.runs b2 navL
    (leftLabel (leftLabel (.inl ⟨0, by omega⟩))) NavJoin.startLabel ctl2 (ctl1, v3)
    NavJoin.ctl NavJoin.ctl B0 B3 B4 u2 t4 s2 r4L
  -- values of B4
  have h4nav : ∀ xx, B4 (iNL xx) = NavJoin.jb (NavJoin.outVec g.vertices p s q₁ q₂ w Q k) xx :=
    fun xx => bank_at iNL B3 _ xx
  have h4off : ∀ a, (∀ xx, iNL xx ≠ a) → B4 a = B3 a := fun a ha =>
    bank_outside iNL B3 _ a (by rintro ⟨kk, hkk⟩; exact ha kk hkk)
  have h4t : B4 (jC (r2 RequestSelect.tagC)) = C.1.encode req.1 := by
    rw [h4off _ (by intro xx; simp [iNL, iNLf, jC, r2]), hB3,
      clr_out cl1 B2 (jC (r2 RequestSelect.tagC)) (cl1_not _ (Or.inr (Or.inr (Or.inl rfl))))]
    show B2 (.inl (.inl (r2 RequestSelect.tagC))) = _
    rw [hB2l, hFt]
  have h4r : B4 (jC (r2 RequestSelect.rowC)) = C.2.encode req.2 := by
    rw [h4off _ (by intro xx; simp [iNL, iNLf, jC, r2]), hB3,
      clr_out cl1 B2 (jC (r2 RequestSelect.rowC)) (cl1_not _ (Or.inr (Or.inr (Or.inr rfl))))]
    show B2 (.inl (.inl (r2 RequestSelect.rowC))) = _
    rw [hB2l, hFr]
  have h4inr : ∀ cc, B4 (.inr cc) = B0 (.inr cc) := by
    intro cc
    rw [h4off _ (by intro xx; simp [iNL, iNLf]), hB3, clr_out cl1 B2 (.inr cc) (cl1_inr cc), hB2r,
      hB1off _ (by intro z; simp [eX])]
  have h4rest : ∀ b : JT, (∀ xx, iNL xx ≠ .inl b) → b ≠ .inl (r2 RequestSelect.tagC) →
      b ≠ .inl (r2 RequestSelect.rowC) → B4 (.inl b) = [] := by
    intro b hb ht hr
    rw [h4off _ hb, hB3, clr_in cl1 B2 (.inl b) (cl1_mem b ?_)]
    rintro (h | h | h | h)
    · exact hb (.inr 0) (by rw [h]; rfl)
    · exact hb (.inr 1) (by rw [h]; rfl)
    · exact ht h
    · exact hr h
  -- (5) clear nC 0, nC 1
  set L2 := (encodeCode c'.1).length + (encodeCode c'.2).length with hL2
  obtain ⟨t5, ht5, v5, r5run⟩ := ClearAll.all_run cl2 cl2_injective L2 B4
    (by
      intro j
      fin_cases j
      · show (B4 (iNL (.inr 0))).length ≤ L2
        rw [h4nav]; show (encodeCode c'.1).length ≤ L2; omega
      · show (B4 (iNL (.inr 1))).length ≤ L2
        rw [h4nav]; show (encodeCode c'.2).length ≤ L2; omega)
    oc
  set B5 := ClearAll.clearFrom cl2 0 B4 with hB5
  obtain ⟨u4, hu4, s4⟩ := BitMachineRawSequence.runs b3 (ClearAll.prog cl2)
    (leftLabel (leftLabel (leftLabel (.inl ⟨0, by omega⟩)))) ⟨0, by omega⟩ ctl3
    (ctl2, NavJoin.ctl) oc v5 B0 B4 B5 u3 t5 s3 r5run
  have h5off : ∀ a, a ≠ jC (nC 0) → a ≠ jC (nC 1) → B5 a = B4 a := by
    intro a h0 h1
    rw [hB5, clr_out cl2 B4 a (by
      intro j; fin_cases j
      · intro h; exact h0 h.symm
      · intro h; exact h1 h.symm)]
  have h5nC : ∀ i : Fin 9, i ≠ 0 → i ≠ 1 →
      B5 (jC (nC i)) = NavJoin.outVec g.vertices p s q₁ q₂ w Q k i := by
    intro i h0 h1
    rw [h5off _ (by simp [jC, nC, h0]) (by simp [jC, nC, h1])]
    exact h4nav (.inr i)
  -- (6) the four copies
  set L6 := (encodeCode c.1).length + (encodeCode c.2).length + (C.1.encode req.1).length +
    (C.2.encode req.2).length with hL6
  have hB5scr : B5 scr = [] := by
    rw [h5off _ (by simp [scr, jC]) (by simp [scr, jC])]
    show B4 (.inr (.inr 1)) = []
    rw [h4inr]; exact hB0scr
  have h5t : B5 (jC (r2 RequestSelect.tagC)) = C.1.encode req.1 := by
    rw [h5off _ (by simp [jC, r2, nC]) (by simp [jC, r2, nC]), h4t]
  have h5r : B5 (jC (r2 RequestSelect.rowC)) = C.2.encode req.2 := by
    rw [h5off _ (by simp [jC, r2, nC]) (by simp [jC, r2, nC]), h4r]
  obtain ⟨t6, ht6, v6, r6run⟩ := CopyAll.all_run cp2 cp2_hsd cp2_hzd cp2_hdd B5
    (fun i => by fin_cases i <;> exact hB5scr) L6
    (by
      intro i
      fin_cases i
      · show (B5 (jC (nC 5))).length ≤ L6
        rw [h5nC 5 (by decide) (by decide)]; show (encodeCode c.1).length ≤ L6; omega
      · show (B5 (jC (nC 4))).length ≤ L6
        rw [h5nC 4 (by decide) (by decide)]; show (encodeCode c.2).length ≤ L6; omega
      · show (B5 (jC (r2 RequestSelect.tagC))).length ≤ L6
        rw [h5t]; omega
      · show (B5 (jC (r2 RequestSelect.rowC))).length ≤ L6
        rw [h5r]; omega)
    oc
  set B6 := CopyAll.done cp2 4 B5 with hB6
  obtain ⟨u5, hu5, s5⟩ := BitMachineRawSequence.runs b4 (CopyAll.prog cp2)
    (leftLabel (leftLabel (leftLabel (leftLabel (.inl ⟨0, by omega⟩))))) (.inl ⟨0, by omega⟩)
    ctl4 (ctl3, v5) oc v6 B0 B5 B6 u4 t6 s4 r6run
  have h6off : ∀ a, a ≠ jC (nC 0) → a ≠ jC (nC 1) → a ≠ jC (r1 RequestSelect.Xc) →
      a ≠ jC (r1 RequestSelect.Yc) → B6 a = B5 a := by
    intro a h0 h1 hX hY
    rw [hB6]
    exact CopyAll.done_off cp2 B5 a (by
      intro j; fin_cases j
      · intro h; exact h0 h.symm
      · intro h; exact h1 h.symm
      · intro h; exact hX h.symm
      · intro h; exact hY h.symm) 4
  -- (7) clear nC 2 .. nC 8, r2 tagC, r2 rowC
  set L7 := (∑ i : Fin 9, (NavJoin.outVec g.vertices p s q₁ q₂ w Q k i).length) +
    (C.1.encode req.1).length + (C.2.encode req.2).length with hL7
  have hov : ∀ i : Fin 9, (NavJoin.outVec g.vertices p s q₁ q₂ w Q k i).length ≤ L7 := by
    intro i
    have := Finset.single_le_sum (f := fun i => (NavJoin.outVec g.vertices p s q₁ q₂ w Q k
      i).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only at this
    omega
  obtain ⟨t7, ht7, v7, r7run⟩ := ClearAll.all_run cl3 cl3_injective L7 B6
    (by
      intro j
      fin_cases j
      all_goals first
        | (show (B6 (jC (r2 RequestSelect.tagC))).length ≤ L7
           rw [h6off _ (by simp [jC, r2, nC]) (by simp [jC, r2, nC]) (by simp [jC, r2, r1])
             (by simp [jC, r2, r1]), h5t]; omega)
        | (show (B6 (jC (r2 RequestSelect.rowC))).length ≤ L7
           rw [h6off _ (by simp [jC, r2, nC]) (by simp [jC, r2, nC]) (by simp [jC, r2, r1])
             (by simp [jC, r2, r1]), h5r]; omega)
        | (rw [show cl3 _ = jC (nC _) from rfl, h6off _ (by simp [jC, nC]) (by simp [jC, nC])
             (by simp [jC, nC, r1]) (by simp [jC, nC, r1]), h5nC _ (by decide) (by decide)]
           exact hov _))
    oc
  set B7 := ClearAll.clearFrom cl3 0 B6 with hB7
  obtain ⟨u6, hu6, s6⟩ := BitMachineRawSequence.runs b5 (ClearAll.prog cl3)
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (.inl ⟨0, by omega⟩)))))) ⟨0, by omega⟩
    ctl5 (ctl4, v6) oc v7 B0 B6 B7 u5 t7 s5 r7run
  -- the final bank
  have hcl3n : ∀ i : Fin 9, i = 0 ∨ i = 1 → ∀ j, cl3 j ≠ jC (nC i) := by
    intro i hi j
    rcases hi with h | h <;> subst h <;> fin_cases j <;> simp [cl3, jC, nC, r2]
  have hfinal : B7 = bankL g r k req.1 req.2 := by
    funext a
    rcases a with (a | z) | cc
    · by_cases h0 : a = nC 0
      · subst h0
        show B7 (jC (nC 0)) = bankL g r k req.1 req.2 (jC (nC 0))
        rw [hB7, clr_out cl3 B6 (jC (nC 0)) (hcl3n 0 (Or.inl rfl)), hB6,
          show jC (nC 0) = cp2 0 1 from rfl, CopyAll.done_dst cp2 cp2_hdd B5 0]
        show B5 (jC (nC 5)) ++ B5 (jC (nC 0)) = _
        rw [h5nC 5 (by decide) (by decide), hB5, clr_in cl2 B4 (jC (nC 0)) ⟨0, rfl⟩,
          List.append_nil]
        rfl
      by_cases h1 : a = nC 1
      · subst h1
        show B7 (jC (nC 1)) = bankL g r k req.1 req.2 (jC (nC 1))
        rw [hB7, clr_out cl3 B6 (jC (nC 1)) (hcl3n 1 (Or.inr rfl)), hB6,
          show jC (nC 1) = cp2 1 1 from rfl, CopyAll.done_dst cp2 cp2_hdd B5 1]
        show B5 (jC (nC 4)) ++ B5 (jC (nC 1)) = _
        rw [h5nC 4 (by decide) (by decide), hB5, clr_in cl2 B4 (jC (nC 1)) ⟨1, rfl⟩,
          List.append_nil]
        rfl
      by_cases hX : a = r1 RequestSelect.Xc
      · subst hX
        show B7 (jC (r1 RequestSelect.Xc)) = bankL g r k req.1 req.2 (jC (r1 RequestSelect.Xc))
        rw [hB7, clr_out cl3 B6 (jC (r1 RequestSelect.Xc)) (by
            intro j; fin_cases j <;> simp [cl3, jC, nC, r1, r2, RequestSelect.tagC,
              RequestSelect.rowC, RequestSelect.Xc]), hB6,
          show jC (r1 RequestSelect.Xc) = cp2 2 1 from rfl, CopyAll.done_dst cp2 cp2_hdd B5 2]
        show B5 (jC (r2 RequestSelect.tagC)) ++ B5 (jC (r1 RequestSelect.Xc)) = _
        rw [h5t, h5off _ (by simp [jC, nC, r1]) (by simp [jC, nC, r1]),
          show B4 (jC (r1 RequestSelect.Xc)) = [] from
            h4rest (.inl (r1 RequestSelect.Xc)) (by intro xx; simp [iNL, iNLf, r1])
            (by simp [r1, r2]) (by simp [r1, r2]), List.append_nil]
        rfl
      by_cases hY : a = r1 RequestSelect.Yc
      · subst hY
        show B7 (jC (r1 RequestSelect.Yc)) = bankL g r k req.1 req.2 (jC (r1 RequestSelect.Yc))
        rw [hB7, clr_out cl3 B6 (jC (r1 RequestSelect.Yc)) (by
            intro j; fin_cases j <;> simp [cl3, jC, nC, r1, r2, RequestSelect.tagC,
              RequestSelect.rowC, RequestSelect.Yc]), hB6,
          show jC (r1 RequestSelect.Yc) = cp2 3 1 from rfl, CopyAll.done_dst cp2 cp2_hdd B5 3]
        show B5 (jC (r2 RequestSelect.rowC)) ++ B5 (jC (r1 RequestSelect.Yc)) = _
        rw [h5r, h5off _ (by simp [jC, nC, r1]) (by simp [jC, nC, r1]),
          show B4 (jC (r1 RequestSelect.Yc)) = [] from
            h4rest (.inl (r1 RequestSelect.Yc)) (by intro xx; simp [iNL, iNLf, r1])
            (by simp [r1, r2]) (by simp [r1, r2]), List.append_nil]
        rfl
      show B7 (jC a) = J0 k req.1 req.2 a
      rw [J0_support k _ _ a h0 h1 hX hY]
      by_cases hc3 : ∃ j, cl3 j = jC a
      · rw [hB7, clr_in cl3 B6 (jC a) hc3]
      · push_neg at hc3
        rw [hB7, clr_out cl3 B6 (jC a) hc3,
          h6off _ (by simp [jC, h0]) (by simp [jC, h1]) (by simp [jC, hX]) (by simp [jC, hY]),
          h5off _ (by simp [jC, h0]) (by simp [jC, h1])]
        rcases a with nav | rest
        · rcases nav with ce | i
          · show B4 (iNL (.inl ce)) = []
            rw [h4nav]; rfl
          · fin_cases i
            all_goals first
              | exact absurd rfl h0
              | exact absurd rfl h1
              | exact absurd rfl (hc3 0)
              | exact absurd rfl (hc3 1)
              | exact absurd rfl (hc3 2)
              | exact absurd rfl (hc3 3)
              | exact absurd rfl (hc3 4)
              | exact absurd rfl (hc3 5)
              | exact absurd rfl (hc3 6)
        · apply h4rest (.inl (.inr rest)) (by intro xx; simp [iNL, iNLf])
          · intro h
            apply hc3 7
            rw [Sum.inl.injEq] at h
            show (Sum.inl (Sum.inl (r2 RequestSelect.tagC)) : JL) = Sum.inl (Sum.inl (Sum.inr rest))
            rw [h]
          · intro h
            apply hc3 8
            rw [Sum.inl.injEq] at h
            show (Sum.inl (Sum.inl (r2 RequestSelect.rowC)) : JL) = Sum.inl (Sum.inl (Sum.inr rest))
            rw [h]
    · show B7 (eX z) = []
      rw [hB7, clr_out cl3 B6 (eX z) (by intro j; fin_cases j <;> simp [cl3, jC, eX]),
        h6off _ (by simp [eX, jC]) (by simp [eX, jC]) (by simp [eX, jC]) (by simp [eX, jC]),
        h5off _ (by simp [eX, jC]) (by simp [eX, jC]),
        show B4 (eX z) = [] from h4rest (.inr z) (by intro xx; simp [iNL, iNLf]) (by simp) (by simp)]
    · show B7 (.inr cc) = bankL g r k req.1 req.2 (.inr cc)
      rw [hB7, clr_out cl3 B6 (.inr cc) (by intro j; fin_cases j <;> simp [cl3, jC]),
        h6off _ (by simp [jC]) (by simp [jC]) (by simp [jC]) (by simp [jC]),
        h5off _ (by simp [jC]) (by simp [jC]), h4inr, hB0]
      exact B0_inr g r k x y req.1 req.2 cc
  refine ⟨u6, ?_, (ctl5, v7), ?_⟩
  · have hb : bodyClock g hg hs r hq ξ k x y =
        (((((NX * (2 * Lp + 3) + 1 + Tst + 1) + (N1 * (Lc + 1) + 1) + 1) +
          NavJoin.joinBound g.vertices p s q₁ q₂ w Q k + 1) + (2 * (L2 + 1) + 1) + 1) +
          (4 * (2 * L6 + 3) + 1) + 1) + (9 * (L7 + 1) + 1) + 1 := rfl
    rw [hb]
    omega
  · rw [← hfinal]
    exact s6

end

#print axioms B0_inr
#print axioms body_run

end Paper2.RLoop
