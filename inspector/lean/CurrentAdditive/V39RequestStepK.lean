import CurrentAdditive.V39RequestStepRun
import Paper2.RLoopStep
import Paper2.TemplateStepXG

/-! The actual current two-family one-level request run. The legacy parser
layout is reused only through explicit structural label maps. No source
run, completed request, fixed-tail computation or desired conclusion is a
caller premise. The source arm is the literal current edge dispatch. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39RequestStep
noncomputable section
open Paper2
open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries
open BitMachineRawSequence (leftLabel)
open Paper2.TemplateStep (J RS nC r1 r2 lC pcC myJ iN i1 i2 eL srcCell navP rs1 pre arm
  armStart armCtl)
open Paper2.TemplateStepX (JT inJ ιE cpC cpR cpCf cp1 cp2 preX armX ccX rcX
  W0f W2f W2f_r2 selClock pre_run liftT bank_inJ ιE_srcA ιE_fw ιE_cc ιE_rc
  ιE_other ιE_range_srcA ιE_range_inl WXb_irrel)
open Paper2.CanonicalDefaultWordScratch (words)
open Paper2.RLoop (W2f_nC01)
variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

def stepClock (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (k : ℕ)
    (x0 : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q (k + 1))
    (y0 : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q (k + 1)) : ℕ :=
  let x := (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q (k+1)).1 x0
  let y := (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q (k+1)).2 y0
  let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k
  let c := seedRecursiveCodes g.vertices p s q₁ q₂ w Q k
  let activity := V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
  Sum.elim
    (fun pz => NavJoin.joinBound g.vertices p s q₁ q₂ w Q k + selClock k x y + 1 +
        ((pz.1.val + 1) + LocateUniform.locBound q₁ q₂ s C.2 c.2 pz.1.val (x y.1).2 + 1 +
          RequestSelect.clock
            ((outerColumnCodec q₁ q₂ s C.2).encode ((SourceMatrix.forgetTag (ξ k) (x y.1).2).2 pz.1))
            ((SourceMatrix.forgetTag (ξ k) (x y.1).2).2 pz.1).1.val
            ((fun a => ((pz.2 a).1, (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q k).1 (pz.2 a).2)) ((SourceMatrix.forgetTag (ξ k) (x y.1).2).2 pz.1).1).1.val
            (.append (.ticket q₁) c.1) c.2
            (List.ofFn (fun a => (prodCodec (finCodec q₁) C.1).encode ((fun a => ((pz.2 a).1, (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q k).1 (pz.2 a).2)) a)))
            (List.ofFn (fun b => C.2.encode (((SourceMatrix.forgetTag (ξ k) (x y.1).2).2 pz.1).2 b)))
            + 1 + 1) + 1)
    (fun iu => NavJoin.joinBound g.vertices p s q₁ q₂ w Q k + selClock k x y + 1 +
        ((V39EdgeSourceDispatch.clock g hg hs r hq k iu.1 [] (x0 y0.1).2 +
          (2 * (C.2.encode (SourceMatrix.sourceColumn activity iu.1
            (SourceMatrix.forgetTag (ξ k) (x y.1).2))).length + 2) + 1 +
          (2 * (V39PhysicalSelect.rowWord k iu.2).length + 2) + 1) + 1) + 1)
    (y0.2 (x0 y0.1).1)

theorem stepK (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (k : ℕ)
    (x0 : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q (k + 1))
    (y0 : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q (k + 1))
    (E0 : SrcX.JX → List Bool)
    (hE0 : ∀ z, z ≠ SrcX.srcAX → z ≠ SrcX.fwX → z ≠ ccX → z ≠ rcX →
      E0 z = SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k [] [] z)
    (hE0s : E0 SrcX.srcAX = []) :
    let x := (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q (k+1)).1 x0
    let y := (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q (k+1)).2 y0
    let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k
    let activity := V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
    let req := RecursiveEntries.request activity ξ k x y
    ∃ t ≤ stepClock g hg hs r hq ξ k x0 y0, ∃ v, ∃ F : JT → List Bool,
      ((advance stepX)^[t])
        (⟨some (leftLabel (leftLabel NavJoin.startLabel)), stepXCtl,
          Sum.elim (W0f k x y) E0⟩ : TM2.Cfg (fun _ : JT => Bool) _ _) =
        ⟨none, v, F⟩ ∧
      F (.inl (nC 0)) = encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 ∧
      F (.inl (nC 1)) = encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).2 ∧
      F (.inl (r2 RequestSelect.tagC)) = C.1.encode req.1 ∧
      F (.inl (r2 RequestSelect.rowC)) = C.2.encode req.2 := by
  intro x y C activity req
  rcases hr0 : y0.2 (x0 y0.1).1 with ⟨pp, z0⟩ | ⟨i, uu⟩
  · let z := fun a => ((z0 a).1, (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q k).1 (z0 a).2)
    have hr : y.2 (x y.1).1 = .inl (pp,z) := by
      change V39PhysicalSelect.rawRowMap _ (y0.2 (x0 y0.1).1) = _
      rw [hr0]
      rfl
    obtain ⟨t, ht, v, F, hrun, hFr, hFl⟩ := template_stepX (n := g.vertices) E0 hp hs k
      activity ξ x y pp z hr
    refine ⟨t, ?_, v, _, hrun, ?_, ?_, ?_, ?_⟩
    · unfold stepClock
      simp only [hr0, Sum.elim_inl]
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
  · have hr : y.2 (x y.1).1 = .inr
        (i,(V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q k).1 uu) := by
      change V39PhysicalSelect.rawRowMap _ (y0.2 (x0 y0.1).1) = _
      rw [hr0]
      rfl
    have htag : (x y.1).2 = V39PhysicalSelect.tagMap
        (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q k).2 (x0 y0.1).2 := rfl
    obtain ⟨t, ht, v, F, hrun, h1, h2, hfr⟩ := source_stepX g hg hp hs r hq k ξ x y
      i uu (x0 y0.1).2 hr htag E0 hE0 hE0s
    refine ⟨t, ?_, v, F, hrun, ?_, ?_, h1, h2⟩
    · unfold stepClock
      simp only [hr0, Sum.elim_inr]
      exact ht
    · rw [hfr (nC 0) (by simp [nC, srcCell, r1]) (by simp [nC, r1]) (by decide) (by decide)
        (by simp [nC, r2]) (by simp [nC, r2]), W2f_nC01 k x y 0 (Or.inl rfl)]
      rfl
    · rw [hfr (nC 1) (by simp [nC, srcCell, r1]) (by simp [nC, r1]) (by decide) (by decide)
        (by simp [nC, r2]) (by simp [nC, r2]), W2f_nC01 k x y 1 (Or.inr rfl)]
      rfl

theorem stepK_current (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (k : ℕ)
    (x0 : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q (k+1))
    (y0 : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q (k+1))
    (E0 : SrcX.JX → List Bool)
    (hE0 : ∀ z, z ≠ SrcX.srcAX → z ≠ SrcX.fwX → z ≠ ccX → z ≠ rcX →
      E0 z = SrcX.WXb (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r k [] [] z)
    (hE0s : E0 SrcX.srcAX = []) :
    let x := (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q (k+1)).1 x0
    let y := (V39PhysicalSelect.embedding g.vertices p q₁ q₂ s w Q (k+1)).2 y0
    let activity := V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
    let req := V39RecursiveTable.request activity k x0 y0
    ∃ t ≤ stepClock g hg hs r hq ξ k x0 y0, ∃ v, ∃ F : JT → List Bool,
      ((advance stepX)^[t])
        (⟨some (leftLabel (leftLabel NavJoin.startLabel)), stepXCtl,
          Sum.elim (W0f k x y) E0⟩ : TM2.Cfg (fun _ : JT => Bool) _ _) =
        ⟨none,v,F⟩ ∧
      F (.inl (nC 0)) = encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k+1)).1 ∧
      F (.inl (nC 1)) = encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k+1)).2 ∧
      F (.inl (r2 RequestSelect.tagC)) = V39PhysicalSelect.rowWord k req.1 ∧
      F (.inl (r2 RequestSelect.rowC)) = V39PhysicalSelect.columnWord k req.2 := by
  intro x y activity req
  obtain ⟨t,ht,v,F,hr,h0,h1,h2,h3⟩ := stepK g hg hp hs r hq ξ k x0 y0 E0 hE0 hE0s
  rw [V39PhysicalSelect.request_embedding] at h2 h3
  exact ⟨t,ht,v,F,hr,h0,h1,h2,h3⟩

end
#print axioms stepK
#print axioms stepK_current
end CurrentAdditive.V39RequestStep
