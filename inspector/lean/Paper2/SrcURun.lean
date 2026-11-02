import Paper2.SrcUFront

/-! Unit 3, segment (1), unrestricted source arm: the first three phases
(`SrcU.z2`) as one run, both scan branches (`front_run`). -/

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

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

theorem rkC_W1 (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) :
    Function.update (Function.update (ScanJoin.W1 g a r ig xv kb) ScanJoin.ansC [])
      ScanJoin.actC [false] rkC = [] := by
  rw [Function.update_of_ne (by simp [rkC, ScanJoin.actC]),
    Function.update_of_ne (by simp [rkC, ScanJoin.ansC])]
  unfold ScanJoin.W1
  rw [bank_outside ScanJoin.ιT _ _ rkC (by
    rintro ⟨j, hj⟩
    change ScanJoin.ιTf j = rkC at hj
    unfold ScanJoin.ιTf at hj
    by_cases h8 : j = 8
    · rw [if_pos h8] at hj; simp [rkC] at hj
    · rw [if_neg h8] at hj
      by_cases h5 : j = 5
      · rw [if_pos h5] at hj; simp [rkC] at hj
      · rw [if_neg h5] at hj; simp [rkC] at hj)]
  rfl

theorem front_run (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
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
      T ScanJoin.actC = [act] ∧ T rkC = u rk ∧
      Option.map Fin.val (SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
        (by omega) hq i (Z.2 0).1) = (if act then some rk else none) ∧
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
  by_cases h : 0 < g.edges.length ∧ (Z.2 0).1.val / r / 3 / g.edges.length = i.1.val
  · obtain ⟨t3, ht3, c3', l3⟩ := ScanJoin.join_true g hg (Z.2 0).1.val r i.1.val xv i.2.isRight h
    have l3' := liftA ιS ScanJoin.full _ _ _ hent _ _ _ _ l3
    rw [bank_ιS] at l3'
    obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs z1 S3 (leftLabel (leftLabel ()))
      (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ()))))) (c1, c2) (c1, v2) c3 c3'
      _ _ _ _ _ q1 l3'
    obtain ⟨act', rk', hA, hR, hV⟩ := ScanValue.scan_value_some g hg hs3 hq i.1 i.2 (Z.2 0).1 h
    let e : Fin g.edges.length := ⟨(Z.2 0).1.val / r / 3 % g.edges.length, Nat.mod_lt _ h.1⟩
    have hA' := ScanJoin.Wtrue_act g hg (Z.2 0).1.val r i.1.val xv i.2.isRight e
    have hR' := ScanJoin.Wtrue_rank g hg (Z.2 0).1.val r i.1.val xv i.2.isRight e
    refine ⟨u2, ScanJoin.Wtrue g hg (Z.2 0).1.val r i.1.val xv i.2.isRight e, act', rk', t3, ?_, ?_, hA,
      hR, hV, _, q2⟩
    · omega
    · have hrk : rk' = CanonicalEndpointRankMachine.semanticRank
          (RankRun.kindOfNat ((Z.2 0).1.val / r % 3)) (RankRun.itemOfBool i.2.isRight)
          (CanonicalEdgeTape.graphEdge g hg e false).val
          (CanonicalEdgeTape.graphEdge g hg e true).val xv := by
        have := congrArg List.length (hR.symm.trans hR')
        simpa using this
      rw [hrk]
      simp only [scanPosBound, dif_pos h]
      exact Nat.add_le_add_right ht3 _
  · obtain ⟨t3, ht3, c3', l3⟩ := ScanJoin.join_false g (Z.2 0).1.val r i.1.val xv i.2.isRight h
    have l3' := liftA ιS ScanJoin.full _ _ _ hent _ _ _ _ l3
    rw [bank_ιS] at l3'
    obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs z1 S3 (leftLabel (leftLabel ()))
      (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ()))))) (c1, c2) (c1, v2) c3 c3'
      _ _ _ _ _ q1 l3'
    have hN := ScanValue.scan_value_none g hg hs3 hq i.1 i.2 (Z.2 0).1 h
    refine ⟨u2, Function.update (Function.update (ScanJoin.W1 g (Z.2 0).1.val r i.1.val xv i.2.isRight)
      ScanJoin.ansC []) ScanJoin.actC [false], false, 0, t3, ?_, ?_, Function.update_self _ _ _,
      rkC_W1 g (Z.2 0).1.val r i.1.val xv i.2.isRight, ?_, _, q2⟩
    · omega
    · simp only [scanPosBound, dif_neg h]
      omega
    · show Option.map Fin.val (SourceActiveRank.scanAtCanonical
          (CanonicalEdgeTape.graphEdge g hg) hs3 hq (i.1, i.2) (Z.2 0).1) = none
      rw [hN]
      rfl

#print axioms rkC_W1
#print axioms front_run

end

end Paper2.SrcU
