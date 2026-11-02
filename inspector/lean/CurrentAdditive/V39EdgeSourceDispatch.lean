import CurrentAdditive.V39EdgeSourceDiagonal
import Paper2.SrcX

/-! Actual tag dispatch for the current two source families. The parser's
unused true,false spelling halts; no fixed-tail constructor is evaluated. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39EdgeSourceDispatch
noncomputable section

open Paper2
open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveRequestCodeShape
open RecursiveLabelCodecScratch SourceMatrix
open BitMachineRawSequence (leftLabel)
open Paper2.OTOps (u)
open Paper2.OTBody (B BB lblB)
open Paper2.SrcX (JX inA fwX lblX srcAX cpT cpTf liftX WXb WXb_fw WXb_at_fw)
open V39EdgeSourceFront (edgeActivity)
open V39EdgeSourceTail (srcU srcUStart srcUCtl srcUBound sourceExitBank)
open V39EdgeSourceDiagonal (srcD srcDStart srcDCtl srcDBound diagonalExitBank)
open V39PhysicalSelect (embedding rawColumnMap outerMap tagMap rowWord columnWord)

def reject : Unit → TM2.Stmt (fun _ : JX => Bool) Unit Unit := fun _ => halt
def PU := fun l => stackStmt inA (srcU l)
def PD1 := MatrixStage4ScalarPreparationOps.copyProgram cpT
def PD2 := fun l => stackStmt inA (srcD l)
def PD := BitMachineRawSequence.program PD1 PD2 srcDStart (none : Option Bool) srcDCtl
abbrev ctlD := ((none : Option Bool), srcDCtl)
abbrev ctlQ := ((none : Option Bool), ((), ctlD))
def QI := TagDispatch.ifProgram fwX reject PD () (leftLabel BitMachineCopy.Label.scan) () ctlD
def program := TagDispatch.ifProgram fwX PU QI srcUStart (.inl ()) srcUCtl ctlQ
def control := ((none : Option Bool), (srcUCtl, ctlQ))

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

def clock (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 4 ≤ s) (r : ℕ) (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) (k : ℕ)
    (i : EdgeSourceMatrix.Items s (Fin g.vertices)) (O : List Bool) :
    V38Matrix.TaggedColumn q₁ q₂ s (V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q k) → ℕ
  | .inl Z => srcUBound g hg hs r hq k i (rawColumnMap (embedding g.vertices p q₁ q₂ s w Q k).2 Z) O + 1
  | .inr j =>
      let j' := outerMap (embedding g.vertices p q₁ q₂ s w Q k).2 j
      (2*q₁+2) + srcDBound g hg hs r hq k i (SourceMatrix.tail j'.2) j' O + 3

def finalBank (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 4 ≤ s) (r : ℕ) (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) (k : ℕ)
    (i : EdgeSourceMatrix.Items s (Fin g.vertices))
    (uu : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q k)
    (zt : V38Matrix.TaggedColumn q₁ q₂ s (V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q k))
    (O : List Bool) : JX → List Bool :=
  let e := embedding g.vertices p q₁ q₂ s w Q k
  let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k
  let rowW := (prodCodec (defaultItemCodec g.vertices s) C.1).encode (i,e.1 uu)
  let col := (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2
  match zt with
  | .inl Z =>
      let Z' := rawColumnMap e.2 Z
      bank inA (WXb (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r k rowW ((rawColumnCodec q₁ q₂ s C.2).encode Z' ++ O))
        (sourceExitBank g hg hs r hq k i (e.1 uu) Z' O)
  | .inr j =>
      let j' := outerMap e.2 j
      let cs := List.ofFn (fun a : Fin (q₁+s+1) => C.2.encode (j'.2 a))
      let dw := u j'.1.val ++ false :: (cs.flatten ++ O)
      bank inA (Function.update (WXb (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r k rowW dw) (cpT 1) (u q₁))
        (diagonalExitBank g hg hs r hq k i (e.1 uu) (SourceMatrix.tail j'.2) j' O
          (encodeCode (outerCode q₁ q₂ s col)) (u (s+1)))

/-- Every supplied word is a current label or public shape/graph input.
The result identifies the entire final bank and both current request words. -/
theorem run (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) (k : ℕ)
    (i : EdgeSourceMatrix.Items s (Fin g.vertices))
    (uu : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q k)
    (zt : V38Matrix.TaggedColumn q₁ q₂ s (V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q k))
    (O : List Bool) :
    let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k
    let e := embedding g.vertices p q₁ q₂ s w Q k
    let activity := edgeActivity g hg (by omega) r hq
    ∃ t ≤ clock g hg hs r hq k i O zt, ∃ v F,
      ((advance program)^[t])
        (⟨some (.inl ()), control,
          WXb (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r k ((prodCodec (defaultItemCodec g.vertices s) C.1).encode (i,e.1 uu))
            ((taggedColumnCodec q₁ q₂ s C.2).encode (tagMap e.2 zt) ++ O)⟩ :
          TM2.Cfg (fun _ : JX => Bool) _ _) = ⟨none,v,F⟩ ∧
      F lblX = columnWord k (sourceColumn activity i (V39RecursiveTable.eraseTag zt)) ∧
      F srcAX = rowWord k uu ∧ F = finalBank g hg hs r hq k i uu zt O := by
  intro C e activity
  let rowW := (prodCodec (defaultItemCodec g.vertices s) C.1).encode (i,e.1 uu)
  let col := (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2
  cases zt with
  | inl Z =>
    let Z' := rawColumnMap e.2 Z
    obtain ⟨t1,ht1,v1,F1,l1,h1,h2,-,-,-,hF⟩ := V39EdgeSourceTail.current_srcU_run
      (w:=w) (Q:=Q) g hg hp hs r hq k i uu Z O
    have hW : ∀ kk, (Sum.elim (BB [] ((rawColumnCodec q₁ q₂ s C.2).encode Z' ++ O)
        (encodeCode col) (encodeCode (outerCode q₁ q₂ s col)) (u (s+1))
        [] [] [] [] [] [] [] (u s)) (Sum.elim (Paper2.SrcU.JJ0 g r) ![rowW,[],[],[]]) :
          Paper2.SrcU.JA → List Bool) kk =
        Function.update (WXb (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r k rowW
          ((taggedColumnCodec q₁ q₂ s C.2).encode (.unrestricted Z') ++ O)) fwX
          ((rawColumnCodec q₁ q₂ s C.2).encode Z' ++ O) (inA kk) := by
      intro kk
      rw [WXb_fw]
      rfl
    have l1' := liftX inA srcU _ _ _ hW _ _ _ _ l1
    obtain ⟨t0,ht0,q0⟩ := TagDispatch.if_false fwX PU QI srcUStart (.inl ()) srcUCtl ctlQ
      (WXb (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r k rowW ((taggedColumnCodec q₁ q₂ s C.2).encode (.unrestricted Z') ++ O))
      ((rawColumnCodec q₁ q₂ s C.2).encode Z' ++ O) rfl t1 v1 _ l1'
    refine ⟨t0,?_,_,_,q0,?_,?_,?_⟩
    · change t0 ≤ srcUBound g hg hs r hq k i Z' O + 1
      have ht1' : t1 ≤ srcUBound g hg hs r hq k i Z' O := ht1
      omega
    · show bank inA _ F1 (inA (.inl lblB)) = _
      rw [bank_at]
      exact h1
    · show bank inA _ F1 (inA Paper2.SrcU.srcA) = _
      rw [bank_at]
      exact h2
    · rw [hF, WXb_fw]
      rfl
  | inr j =>
    let j' := outerMap e.2 j
    let cs := List.ofFn (fun a : Fin (q₁+s+1) => C.2.encode (j'.2 a))
    let dw := u j'.1.val ++ false :: (cs.flatten ++ O)
    let W2 := WXb (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r k rowW dw
    have hz : W2 (cpT 2) = [] := rfl
    have ht : W2 (cpT 1) = [] := rfl
    have h0 : W2 (cpT 0) = u q₁ := rfl
    have l1 := MatrixStage4ScalarPreparationOps.copy_run cpT W2 hz
    rw [h0,ht,List.append_nil] at l1
    obtain ⟨t2,ht2,v2,F2,l2,h1,h2,hF⟩ := V39EdgeSourceDiagonal.current_srcD_run
      (w:=w) (Q:=Q) g hg hp hs r hq k i uu j O (encodeCode (outerCode q₁ q₂ s col)) (u (s+1))
    have hW : ∀ kk, (Sum.elim (BB [] dw (encodeCode col) (encodeCode (outerCode q₁ q₂ s col))
        (u (s+1)) [] [] (u q₁) [] [] [] [] (u s))
        (Sum.elim (Paper2.SrcU.JJ0 g r) ![rowW,[],[],[]]) : Paper2.SrcU.JA → List Bool) kk =
        Function.update W2 (cpT 1) (u q₁) (inA kk) := by
      intro kk
      have hw : Function.update W2 (cpT 1) (u q₁) =
          Sum.elim (Sum.elim (BB [] dw (encodeCode col) (encodeCode (outerCode q₁ q₂ s col))
            (u (s+1)) [] [] (u q₁) [] [] [] [] (u s))
            (Sum.elim (Paper2.SrcU.JJ0 g r) ![rowW,[],[],[]])) (DefaultWordLoop.entry p q₁ s Q w k) := by
        simp only [W2,WXb,cpT,cpTf,Function.Embedding.coeFn_mk,Matrix.cons_val_one,
          Matrix.cons_val_zero,Sum.update_elim_inl,OTBody.upd_t]
        rfl
      rw [hw]
      rfl
    have l2' := liftX inA srcD _ _ _ hW _ _ _ _ l2
    obtain ⟨u1,hu1,q1⟩ := BitMachineRawSequence.runs PD1 PD2 BitMachineCopy.Label.scan srcDStart
      (none : Option Bool) none srcDCtl v2 _ _ _ _ _ l1 l2'
    have hdw : (taggedColumnCodec q₁ q₂ s C.2).encode (.diagonal j') ++ O = true :: true :: dw := by
      rw [OTTags.diag_word]
      simp only [dw,cs,List.cons_append,List.append_assoc]
      rfl
    obtain ⟨ta,hta,qa⟩ := TagDispatch.if_true fwX reject PD () (leftLabel BitMachineCopy.Label.scan)
      () ctlD (Function.update (WXb (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r k rowW
        ((taggedColumnCodec q₁ q₂ s C.2).encode (.diagonal j') ++ O)) fwX (true :: dw))
      dw (by rw [Function.update_self]) u1 _ _
      (by rw [Function.update_idem,WXb_fw]; exact q1)
    obtain ⟨t0,ht0,q0⟩ := TagDispatch.if_true fwX PU QI srcUStart (.inl ()) srcUCtl ctlQ
      (WXb (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r k rowW ((taggedColumnCodec q₁ q₂ s C.2).encode (.diagonal j') ++ O))
      (true :: dw) (by rw [WXb_at_fw,hdw]) ta _ _ qa
    refine ⟨t0,?_,_,_,q0,?_,?_,?_⟩
    · have hl : (u q₁).length = q₁ := by simp [u]
      rw [hl] at hu1
      change t0 ≤ (2*q₁+2) + srcDBound g hg hs r hq k i (SourceMatrix.tail j'.2) j' O + 3
      have ht2' : t2 ≤ srcDBound g hg hs r hq k i (SourceMatrix.tail j'.2) j' O := ht2
      omega
    · show bank inA _ F2 (inA (.inl lblB)) = _
      rw [bank_at]
      exact h1
    · show bank inA _ F2 (inA Paper2.SrcU.srcA) = _
      rw [bank_at]
      exact h2
    · rw [hF]
      rfl

#print axioms run

end
end CurrentAdditive.V39EdgeSourceDispatch
