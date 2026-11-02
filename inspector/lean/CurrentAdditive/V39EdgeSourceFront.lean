import CurrentAdditive.V39PhysicalSelect
import CurrentAdditive.EdgeScanValue
import Paper2.SrcUTail

/-! Current edge-only ordinary-source arm: actual item parser, outer selector
test, graph-byte activity scan, followed later by source-position and fetch.
Only coordinate-independent old parser and bank lemmas are reused. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39EdgeSourceFront
noncomputable section

open Paper2
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
open Paper2.SrcU (JA srcA sp5 sp6 K0 rkC iA iK iX ιB ιF ιS ιP S1 S2
  c1 c2 c5 liftA JJ0 JJ1 items_bank bank_ιB bank_ιS)

def S3 := fun l => stackStmt ιS (LiteralEdgeScanJoin.full l)
abbrev c3 := (LiteralEdgeScanJoin.testCtl, ((none : Option Bool),
  ((), (LiteralEdgeScanJoin.opCtl, RankRun.startCtl))))
abbrev z1 := Paper2.SrcU.z1
def z2 := BitMachineRawSequence.program z1 S3
  (leftLabel (leftLabel (leftLabel .start))) (c1, c2) c3

theorem scan_entry (X : B → List Bool) (Z4 : Fin 4 → List Bool) (g : EncodedGraph.Graph)
    (a r ig xv : ℕ) (kb : Bool) (hX : X aC = u a) :
    ∀ x, LiteralEdgeScanJoin.W0 g a r ig xv kb x =
      (Sum.elim X (Sum.elim (JJ1 g r ig xv kb) Z4) : JA → List Bool) (ιS x) := by
  exact Paper2.SrcU.scan_entry X Z4 g a r ig xv kb hX

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

def edgeActivity (g : EncodedGraph.Graph) (hg : g.Valid) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) :
    SourceConstruction.Items s (Fin g.vertices) → Fin q₂ → Option (Fin s) :=
  fun i a => LiteralEdgeEncoder.activity hs (LiteralEdgeEncoder.edge g hg) i (Fin.cast hq a)

def scanFinal (g : EncodedGraph.Graph) (hg : g.Valid) (a r ig xv : ℕ) (kb : Bool) :
    LiteralEdgeScanJoin.JJ → List Bool :=
  if h : 0 < g.edges.length ∧ a / r / g.edges.length = ig then
    LiteralEdgeScanJoin.Wtrue g hg a r ig xv kb
      ⟨a / r % g.edges.length, Nat.mod_lt _ h.1⟩
  else
    Function.update (Function.update (LiteralEdgeScanJoin.W1 g a r ig xv kb)
      LiteralEdgeScanJoin.ansC []) LiteralEdgeScanJoin.actC [false]

def scanPosBound (g : EncodedGraph.Graph) (hg : g.Valid) (a r ig xv : ℕ) (kb : Bool) : ℕ :=
  if h : 0 < g.edges.length ∧ a / r / g.edges.length = ig then
    let e : Fin g.edges.length := ⟨a / r % g.edges.length, Nat.mod_lt _ h.1⟩
    let edge := CanonicalEdgeTape.graphEdge g hg
    ((LiteralEdgeDecodeMachine.clock a r g.edges.length +
        (a / r / g.edges.length + ig + 4) + 1) +
        ((((103 * ((EncodedGraph.encode g).length + 1)^3 +
          (2 * (CanonicalEdgeTape.word edge).length + 2) + (2 * g.vertices + 2) +
          (2 * e.val + 2) + (2 * e.val + 2) + 1 + 1 +
          UnaryFieldListParserScratch.fuel g.vertices (2 * (e.val + 1))
            (CanonicalEdgeTape.word edge) + 7) +
          ((edge e true).val + (edge e false).val + 7) + 1) +
          (max (edge e false).val (max (edge e true).val xv) + 7) + 1) + 1) + 1) +
    (CanonicalEndpointRankMachine.semanticRank (RankRun.kindOfNat 0)
        (RankRun.itemOfBool kb) (edge e false).val (edge e true).val xv + 3)
  else
    ((LiteralEdgeDecodeMachine.clock a r g.edges.length +
        (a / r / g.edges.length + ig + 4) + 1) + (1 + 1) + 1) + (0 + 3)


theorem rkC_W1 (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) :
    Function.update (Function.update (LiteralEdgeScanJoin.W1 g a r ig xv kb) LiteralEdgeScanJoin.ansC [])
      LiteralEdgeScanJoin.actC [false] rkC = [] := by
  rw [Function.update_of_ne (by simp [rkC, LiteralEdgeScanJoin.actC]),
    Function.update_of_ne (by simp [rkC, LiteralEdgeScanJoin.ansC])]
  unfold LiteralEdgeScanJoin.W1
  rw [bank_outside LiteralEdgeScanJoin.ιT _ _ rkC (by
    rintro ⟨j, hj⟩
    change LiteralEdgeScanJoin.ιTf j = rkC at hj
    unfold LiteralEdgeScanJoin.ιTf at hj
    by_cases h8 : j = 8
    · rw [if_pos h8] at hj; simp [rkC] at hj
    · rw [if_neg h8] at hj
      by_cases h5 : j = 5
      · rw [if_pos h5] at hj; simp [rkC] at hj
      · rw [if_neg h5] at hj; simp [rkC] at hj)]
  rfl

theorem front_run (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r) (k : ℕ)
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
    let X2 := BB [] fw (encodeCode col) (encodeCode (outerCode q₁ q₂ s col)) (u (s + 1))
      (u s) (u (Z.2 0).1.val) [] [] [] [] [decide (∀ pp, (Z.2 pp).1 = (Z.2 0).1)] (u s)
    let xv := CanonicalEndpointRankBridge.itemValue i.2
    let WA0 : JA → List Bool := Sum.elim X0 (Sum.elim (JJ0 g r)
      ![(prodCodec (defaultItemCodec g.vertices s) C.1).encode (i, uu), [], [], []])
    ∃ t T act rk t3,
      t ≤ (1 + ((i.1.val + 1) + 1 + (xv + 1) + 2) + 1) +
        OTGen.fullGBound s (OTTags.TfU k Z O) (OTLoop.tokF k Z.2) (OTTags.restF k Z.2) + 1 +
        t3 + 1 ∧
      t3 + (rk + 3) ≤ scanPosBound g hg (Z.2 0).1.val r i.1.val xv i.2.isRight ∧
      T LiteralEdgeScanJoin.actC = [act] ∧ T rkC = u rk ∧
      Option.map Fin.val (edgeActivity g hg (by omega) r hq i (Z.2 0).1) = (if act then some rk else none) ∧
      T = scanFinal g hg (Z.2 0).1.val r i.1.val xv i.2.isRight ∧
      ∃ v, ((advance z2)^[t])
        (⟨some (leftLabel (leftLabel (leftLabel ()))), ((c1, c2), c3), WA0⟩ :
          TM2.Cfg (fun _ : JA => Bool) _ _) =
        ⟨none, v, Sum.elim (Function.update X2 aC (T K0))
          (Sum.elim (Function.update T K0 []) ![C.1.encode uu, [], [], []])⟩ := by
  intro C col fw X0 X2 xv WA0
  have hs3 : 3 ≤ s := by omega
  -- phase 1: item operands
  obtain ⟨t1, ht1, v1, l1⟩ := ItemOperands.item_operands (n := g.vertices) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) k i uu srcA iA iK iX
    (by simp [srcA, iA]) (by simp [srcA, iK]) (by simp [srcA, iX]) (by simp [iA, iK])
    (by simp [iA, iX]) (by simp [iK, iX]) WA0 rfl rfl rfl rfl
  rw [items_bank] at l1
  -- phase 2: outer-token equality
  obtain ⟨t2, ht2, v2, l2⟩ := OTTags.unrestricted_eq_run (n := g.vertices) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k Z O
  have l2' := liftA ιB _ (Sum.elim X0 (Sum.elim (JJ1 g r i.1.val xv i.2.isRight)
    ![C.1.encode uu, [], [], []])) _ _ (fun _ => rfl) _ _ _ _ l2
  rw [bank_ιB] at l2'
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs S1 S2 (leftLabel ())
    (OTGen.fullGStart FetchIndexed.rowProgram FetchIndexed.rowStart FetchIndexed.rowControl)
    c1 v1 c2 v2 _ _ _ _ _ l1 l2'
  -- phase 3: the scan, by branch
  have hent := scan_entry X2 ![C.1.encode uu, [], [], []] g (Z.2 0).1.val r i.1.val xv i.2.isRight rfl
  by_cases h : 0 < g.edges.length ∧ (Z.2 0).1.val / r / g.edges.length = i.1.val
  · obtain ⟨t3, ht3, c3', l3⟩ := LiteralEdgeScanJoin.join_true g hg (Z.2 0).1.val r i.1.val xv i.2.isRight h
    have l3' := liftA ιS LiteralEdgeScanJoin.full _ _ _ hent _ _ _ _ l3
    rw [bank_ιS] at l3'
    obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs z1 S3 (leftLabel (leftLabel ()))
      (leftLabel (leftLabel (leftLabel .start))) (c1, c2) (c1, v2) c3 c3'
      _ _ _ _ _ q1 l3'
    obtain ⟨act', rk', hA, hR, hV⟩ := LiteralEdgeScanValue.scan_value_some g hg hs3 i.1 i.2 (Fin.cast hq (Z.2 0).1) h
    let e : Fin g.edges.length := ⟨(Z.2 0).1.val / r % g.edges.length, Nat.mod_lt _ h.1⟩
    have hA' := LiteralEdgeScanJoin.Wtrue_act g hg (Z.2 0).1.val r i.1.val xv i.2.isRight e
    have hR' := LiteralEdgeScanJoin.Wtrue_rank g hg (Z.2 0).1.val r i.1.val xv i.2.isRight e
    refine ⟨u2, LiteralEdgeScanJoin.Wtrue g hg (Z.2 0).1.val r i.1.val xv i.2.isRight e, act', rk', t3, ?_, ?_, hA,
      hR, hV, by simp only [scanFinal, dif_pos h]; rfl, _, q2⟩
    · omega
    · have hrk : rk' = CanonicalEndpointRankMachine.semanticRank
          (RankRun.kindOfNat 0) (RankRun.itemOfBool i.2.isRight)
          (CanonicalEdgeTape.graphEdge g hg e false).val
          (CanonicalEdgeTape.graphEdge g hg e true).val xv := by
        have := congrArg List.length (hR.symm.trans hR')
        simpa using this
      rw [hrk]
      simp only [scanPosBound, dif_pos h]
      exact Nat.add_le_add_right ht3 _
  · obtain ⟨t3, ht3, c3', l3⟩ := LiteralEdgeScanJoin.join_false g (Z.2 0).1.val r i.1.val xv i.2.isRight h
    have l3' := liftA ιS LiteralEdgeScanJoin.full _ _ _ hent _ _ _ _ l3
    rw [bank_ιS] at l3'
    obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs z1 S3 (leftLabel (leftLabel ()))
      (leftLabel (leftLabel (leftLabel .start))) (c1, c2) (c1, v2) c3 c3'
      _ _ _ _ _ q1 l3'
    have hN := LiteralEdgeScanValue.scan_value_none g hg hs3 i.1 i.2 (Fin.cast hq (Z.2 0).1) h
    refine ⟨u2, Function.update (Function.update (LiteralEdgeScanJoin.W1 g (Z.2 0).1.val r i.1.val xv i.2.isRight)
      LiteralEdgeScanJoin.ansC []) LiteralEdgeScanJoin.actC [false], false, 0, t3, ?_, ?_, Function.update_self _ _ _,
      rkC_W1 g (Z.2 0).1.val r i.1.val xv i.2.isRight, ?_,
      by simp only [scanFinal, dif_neg h], _, q2⟩
    · omega
    · simp only [scanPosBound, dif_neg h]
      omega
    · show Option.map Fin.val (edgeActivity g hg hs3 r hq (i.1, i.2) (Z.2 0).1) = none
      change Option.map Fin.val (LiteralEdgeEncoder.activity hs3 (LiteralEdgeEncoder.edge g hg)
        (i.1, i.2) (Fin.cast hq (Z.2 0).1)) = none
      rw [hN]
      rfl


#print axioms front_run

end
end CurrentAdditive.V39EdgeSourceFront
