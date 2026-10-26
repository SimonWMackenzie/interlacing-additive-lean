import Paper2.RLoopDefs

/-! Unit 3, segment (2): one run of the ONE fixed program `TemplateStepX.stepX`
for EVERY level-`k+1` pair (both raw-row cases, every tag), with the four cells
the loop keeps stated exactly: `nC 0`, `nC 1` (the level-`k+1` codes, untouched)
and `r2 tagC`, `r2 rowC` (the encoded request). The clock `stepClock` is the
checked clock of the case at hand (a `Sum.elim` on the requested raw row). -/

set_option maxHeartbeats 32000000
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

/-- The checked one-level clock, by the case of the requested raw row. -/
def stepClock (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q (k + 1)) : ℕ :=
  let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k
  let c := seedRecursiveCodes g.vertices p s q₁ q₂ w Q k
  let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
    (by omega) hq
  Sum.elim
    (fun pz => NavJoin.joinBound g.vertices p s q₁ q₂ w Q k + selClock k x y + 1 +
        ((pz.1.val + 1) + LocateUniform.locBound q₁ q₂ s C.2 c.2 pz.1.val (x y.1).2 + 1 +
          RequestSelect.clock
            ((outerColumnCodec q₁ q₂ s C.2).encode ((SourceMatrix.forgetTag (ξ k) (x y.1).2).2 pz.1))
            ((SourceMatrix.forgetTag (ξ k) (x y.1).2).2 pz.1).1.val
            (pz.2 ((SourceMatrix.forgetTag (ξ k) (x y.1).2).2 pz.1).1).1.val
            (.append (.ticket q₁) c.1) c.2
            (List.ofFn (fun a => (prodCodec (finCodec q₁) C.1).encode (pz.2 a)))
            (List.ofFn (fun b => C.2.encode (((SourceMatrix.forgetTag (ξ k) (x y.1).2).2 pz.1).2 b)))
            + 1 + 1) + 1)
    (fun iu => NavJoin.joinBound g.vertices p s q₁ q₂ w Q k + selClock k x y + 1 +
        ((SrcX.srcXBound g hg hs r hq k iu.1 (ξ k) [] (x y.1).2 +
          (2 * (C.2.encode (SourceMatrix.sourceColumn activity iu.1
            (SourceMatrix.forgetTag (ξ k) (x y.1).2))).length + 2) + 1 +
          (2 * (C.1.encode iu.2).length + 2) + 1) + 1) + 1)
    (y.2 (x y.1).1)

theorem W2f_nC01 {n : ℕ} [NeZero n] (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    (i : Fin 9) (hi : i = 0 ∨ i = 1) :
    W2f k x y (nC i) = NavJoin.outVec n p s q₁ q₂ w Q k i := by
  unfold W2f
  rw [TemplateStep.i1_off _ _ _ (by intro yy; simp [nC, r1]) (by rcases hi with h | h <;> subst h <;> decide)
    (by rcases hi with h | h <;> subst h <;> decide)]
  exact TemplateStep.bank_iN_inl _ _ (.inr i)

/-- One level, both cases, the four kept cells exact. -/
theorem stepK (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
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
      s q₁ q₂ w Q (k + 1))
    (E0 : SrcX.JX → List Bool)
    (hE0 : ∀ z, z ≠ SrcX.srcAX → z ≠ SrcX.fwX → z ≠ ccX → z ≠ rcX →
      E0 z = SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k [] [] z)
    (hE0s : E0 SrcX.srcAX = []) :
    let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k
    let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by omega) hq
    let req := RecursiveEntries.request activity ξ k x y
    ∃ t ≤ stepClock g hg hs r hq ξ k x y, ∃ v, ∃ F : JT → List Bool,
      ((advance stepX)^[t])
        (⟨some (leftLabel (leftLabel NavJoin.startLabel)), stepXCtl,
          Sum.elim (W0f k x y) E0⟩ : TM2.Cfg (fun _ : JT => Bool) _ _) =
        ⟨none, v, F⟩ ∧
      F (.inl (nC 0)) = encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 ∧
      F (.inl (nC 1)) = encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).2 ∧
      F (.inl (r2 RequestSelect.tagC)) = C.1.encode req.1 ∧
      F (.inl (r2 RequestSelect.rowC)) = C.2.encode req.2 := by
  intro C activity req
  rcases hr : y.2 (x y.1).1 with ⟨pp, z⟩ | ⟨i, uu⟩
  · obtain ⟨t, ht, v, F, hrun, hFr, hFl⟩ := TemplateStepX.template_stepX (n := g.vertices) E0 hp hs k
      activity ξ x y pp z hr
    refine ⟨t, ?_, v, _, hrun, ?_, ?_, ?_, ?_⟩
    · unfold stepClock
      simp only [hr, Sum.elim_inl]
      exact ht
    · show bank i2 F _ (nC 0) = _
      rw [bank_outside i2 _ _ (nC 0) (by
        rintro ⟨kk, hkk⟩
        rcases kk with kk | kk | kk
        · cases hkk
        · cases hkk
        · fin_cases kk <;> simp [i2, TemplateStep.i2Fun, nC, r1, r2, lC] at hkk)]
      rw [hFr (nC 0) (by simp [eL, TemplateStep.eLFun, nC, r1, FetchIndexed.fwC])
        (by simp [eL, TemplateStep.eLFun, nC, myJ, FetchIndexed.myC])
        (by simp [eL, TemplateStep.eLFun, nC, lC, SuccessFetchJoin.lblF])]
      rw [Function.update_of_ne (by simp [nC, pcC]), Function.update_of_ne (by simp [nC, srcCell, r1]),
        Function.update_of_ne (by simp [nC, srcCell, r1])]
      rw [W2f_nC01 k x y 0 (Or.inl rfl)]
      rfl
    · show bank i2 F _ (nC 1) = _
      rw [bank_outside i2 _ _ (nC 1) (by
        rintro ⟨kk, hkk⟩
        rcases kk with kk | kk | kk
        · cases hkk
        · cases hkk
        · fin_cases kk <;> simp [i2, TemplateStep.i2Fun, nC, r1, r2, lC] at hkk)]
      rw [hFr (nC 1) (by simp [eL, TemplateStep.eLFun, nC, r1, FetchIndexed.fwC])
        (by simp [eL, TemplateStep.eLFun, nC, myJ, FetchIndexed.myC])
        (by simp [eL, TemplateStep.eLFun, nC, lC, SuccessFetchJoin.lblF])]
      rw [Function.update_of_ne (by simp [nC, pcC]), Function.update_of_ne (by simp [nC, srcCell, r1]),
        Function.update_of_ne (by simp [nC, srcCell, r1])]
      rw [W2f_nC01 k x y 1 (Or.inr rfl)]
      rfl
    · show bank i2 F _ (r2 RequestSelect.tagC) = _
      rw [← TemplateStep.i2_tag, bank_at]
      rfl
    · show bank i2 F _ (r2 RequestSelect.rowC) = _
      rw [← TemplateStep.i2_row, bank_at]
      rfl
  · obtain ⟨t, ht, v, F, hrun, h1, h2, hfr⟩ := TemplateStepX.source_stepXG g hg hp hs r hq k ξ x y
      i uu hr (hfix i) E0 hE0 hE0s
    refine ⟨t, ?_, v, F, hrun, ?_, ?_, h1, h2⟩
    · unfold stepClock
      simp only [hr, Sum.elim_inr]
      exact ht
    · rw [hfr (nC 0) (by simp [nC, srcCell, r1]) (by simp [nC, r1]) (by decide) (by decide)
        (by simp [nC, r2]) (by simp [nC, r2]), W2f_nC01 k x y 0 (Or.inl rfl)]
      rfl
    · rw [hfr (nC 1) (by simp [nC, srcCell, r1]) (by simp [nC, r1]) (by decide) (by decide)
        (by simp [nC, r2]) (by simp [nC, r2]), W2f_nC01 k x y 1 (Or.inr rfl)]
      rfl

end

#print axioms W2f_nC01
#print axioms stepK

end Paper2.RLoop
