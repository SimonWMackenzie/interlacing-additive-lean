import Paper2.SrcUTail

/-! Unit 3, segment (1): the source arm for the DIAGONAL tag as ONE program
on the bank `SrcU.JA`: item operands (into the scan entry cells) ;
`OTTags.diagProg` (token of the single outer word into the scan's decode
cell `aC`, one pushed `true` on `eqC`) ; `ScanJoin.full` ; `SourcePos` ;
production `copyProgram` of unary `q₁` onto the source-position cell (index
`q₁ + pos`) ; production `FetchIndexed.colProgram` on the diagonal word:
the Codex-checked `SourceTailFetch.diagonal_source_tail_fetch`. The diagonal
word is never expanded into an unrestricted label. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SrcD

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveRequestCodeShape
open RecursiveLabelCodecScratch RecursiveEntries SourceMatrix
open BitMachineRawSequence (leftLabel)
open Paper2.OTOps (u)
open Paper2.OTBody (B BB aC tC zC eqC sC idxB lblB ob)
open Paper2.ScanDecodeMachine (K D0)
open Paper2.RankRun (R RB)
open Paper2.SrcU

theorem upd_fw (lbl fw cc rc my idx a t x acc ctr eqv sU y : List Bool) :
    Function.update (BB lbl fw cc rc my idx a t x acc ctr eqv sU) (.inl FetchIndexed.fwC) y =
      BB lbl y cc rc my idx a t x acc ctr eqv sU := by
  funext j
  rcases j with ((j | j) | j) | j
  · simp [BB, FetchIndexed.FB, FetchIndexed.fwC, Function.update_apply]
  · simp [BB, FetchIndexed.FB, FetchIndexed.fwC, Function.update_apply]
  · fin_cases j <;> simp [BB, FetchIndexed.FB, FetchIndexed.fwC,
      FetchIndexed.ext5, Function.update_apply]
  · simp [BB, FetchIndexed.fwC, Function.update_apply]

def cpQFun : Fin 3 → JA := ![.inl tC, .inl idxB, .inl zC]

theorem cpQFun_injective : Function.Injective cpQFun := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [cpQFun, tC, idxB, zC]

def cpQ : Fin 3 ↪ JA := ⟨cpQFun, cpQFun_injective⟩

def fwA : JA := .inl (.inl FetchIndexed.fwC)

def D2 := OTTags.diagProg fwA (.inl aC : JA) (.inl eqC : JA)
def D6 := MatrixStage4ScalarPreparationOps.copyProgram cpQ

abbrev cD := ((ob, ob) : Option Bool × Option Bool)

def y1 := BitMachineRawSequence.program S1 D2 (leftLabel ()) c1 cD
def y2 := BitMachineRawSequence.program y1 S3
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ()))))) (c1, cD) c3
def y3 := BitMachineRawSequence.program y2 S5 (leftLabel .l0) ((c1, cD), c3) c5
def y4 := BitMachineRawSequence.program y3 D6 BitMachineCopy.Label.scan (((c1, cD), c3), c5) ob
/-- The diagonal source arm: one program. -/
def srcD := BitMachineRawSequence.program y4 S6 FetchIndexed.colStart ((((c1, cD), c3), c5), ob)
  FetchIndexed.colControl
def srcDStart := FetchIndexed.labelOf srcD
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ()))))))
def srcDCtl := (((((c1, cD), c3), c5), ob), FetchIndexed.colControl)

theorem ιP_range_t : ¬ ∃ j, ιP j = (.inl tC : JA) := by
  rintro ⟨j, hj⟩
  fin_cases j <;> simp [ιP, ιPf, eqC, sC, idxB, sp5, sp6, tC] at hj

theorem ιP_range_z : ¬ ∃ j, ιP j = (.inl zC : JA) := by
  rintro ⟨j, hj⟩
  fin_cases j <;> simp [ιP, ιPf, eqC, sC, idxB, sp5, sp6, zC] at hj

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

def srcDBound (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r) (k : ℕ)
    (i : SourceConstruction.Items s (Fin g.vertices))
    (ξ₀ : Tail s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k))
    (j : OuterColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k))
    (O : List Bool) : ℕ :=
  let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k
  let col := (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2
  let xv := CanonicalEndpointRankBridge.itemValue i.2
  let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
    (by omega) hq
  (1 + ((i.1.val + 1) + 1 + (xv + 1) + 2) + 1) + (j.1.val + 3) +
    scanPosBound g hg j.1.val r i.1.val xv i.2.isRight + (2 * s + 4) + (2 * q₁ + 2) +
    FetchIndexed.colBound col (List.ofFn (fun a : Fin (q₁ + s + 1) => C.2.encode (j.2 a)))
      (q₁ + (sourcePosition activity i (forgetTag ξ₀ (.diagonal j))).val) O + 5

/-- Segment (1), diagonal tag: the whole source arm as ONE program on ONE bank. -/
theorem srcD_run (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r) (k : ℕ)
    (i : SourceConstruction.Items s (Fin g.vertices))
    (uu : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q k)
    (ξ₀ : Tail s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k))
    (j : OuterColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k))
    (O rc0 my0 : List Bool) :
    let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k
    let col := (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2
    let cs := List.ofFn (fun a : Fin (q₁ + s + 1) => C.2.encode (j.2 a))
    let dw := List.replicate j.1.val true ++ false :: (cs.flatten ++ O)
    let XD0 := BB [] dw (encodeCode col) rc0 my0 [] [] (u q₁) [] [] [] [] (u s)
    let WD0 : JA → List Bool := Sum.elim XD0 (Sum.elim (JJ0 g r)
      ![(prodCodec (defaultItemCodec g.vertices s) C.1).encode (i, uu), [], [], []])
    let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by omega) hq
    ∃ t ≤ srcDBound g hg hs r hq k i ξ₀ j O, ∃ v F,
      ((advance srcD)^[t]) (⟨some srcDStart, srcDCtl, WD0⟩ : TM2.Cfg (fun _ : JA => Bool) _ _) =
        ⟨none, v, F⟩ ∧
      F (.inl lblB) = C.2.encode (sourceColumn activity i (forgetTag ξ₀ (.diagonal j))) ∧
      F srcA = C.1.encode uu := by
  intro C col cs dw XD0 WD0 activity
  have hs3 : 3 ≤ s := by omega
  let xv := CanonicalEndpointRankBridge.itemValue i.2
  let F4 : Fin 4 → List Bool := ![C.1.encode uu, [], [], []]
  -- phase 1: item operands
  obtain ⟨t1, ht1, v1, l1⟩ := ItemOperands.item_operands (n := g.vertices) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) k i uu srcA iA iK iX
    (by simp [srcA, iA]) (by simp [srcA, iK]) (by simp [srcA, iX]) (by simp [iA, iK])
    (by simp [iA, iX]) (by simp [iK, iX]) WD0 rfl rfl rfl rfl
  rw [items_bank] at l1
  -- phase 2: the diagonal token and the equality bit
  obtain ⟨t2, ht2, l2⟩ := OTTags.diag_run fwA (.inl aC : JA) (.inl eqC : JA)
    (by simp [fwA, aC]) (by simp [fwA, eqC]) (by simp [aC, eqC]) j.1.val (cs.flatten ++ O)
    (Sum.elim XD0 (Sum.elim (JJ1 g r i.1.val xv i.2.isRight) F4)) rfl rfl rfl
  let XD2 := BB [] (cs.flatten ++ O) (encodeCode col) rc0 my0 [] (List.replicate j.1.val true)
    (u q₁) [] [] [] [true] (u s)
  have hX2 : Function.update (Function.update (Function.update
      (Sum.elim XD0 (Sum.elim (JJ1 g r i.1.val xv i.2.isRight) F4) : JA → List Bool)
      fwA (cs.flatten ++ O)) (.inl aC) (List.replicate j.1.val true)) (.inl eqC) [true] =
      Sum.elim XD2 (Sum.elim (JJ1 g r i.1.val xv i.2.isRight) F4) := by
    simp only [fwA, Sum.update_elim_inl, XD0, XD2, upd_fw, OTBody.upd_a, OTBody.upd_eq]
  rw [hX2] at l2
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs S1 D2 (leftLabel ()) (leftLabel ())
    c1 v1 cD cD _ _ _ _ _ l1 l2
  -- phase 3: the scan, by branch
  have hent := scan_entry XD2 F4 g j.1.val r i.1.val xv i.2.isRight rfl
  have hscan : ∃ tt T act rk t3,
      tt ≤ (1 + ((i.1.val + 1) + 1 + (xv + 1) + 2) + 1) + (j.1.val + 1 + 1 + 1) + 1 + t3 + 1 ∧
      t3 + (rk + 3) ≤ scanPosBound g hg j.1.val r i.1.val xv i.2.isRight ∧
      T ScanJoin.actC = [act] ∧ T rkC = u rk ∧
      Option.map Fin.val (activity i j.1) = (if act then some rk else none) ∧
      ∃ v, ((advance y2)^[tt])
        (⟨some (leftLabel (leftLabel (leftLabel ()))), ((c1, cD), c3), WD0⟩ :
          TM2.Cfg (fun _ : JA => Bool) _ _) =
        ⟨none, v, Sum.elim (Function.update XD2 aC (T K0))
          (Sum.elim (Function.update T K0 []) F4)⟩ := by
    by_cases h : 0 < g.edges.length ∧ j.1.val / r / 3 / g.edges.length = i.1.val
    · obtain ⟨t3, ht3, c3', l3⟩ := ScanJoin.join_true g hg j.1.val r i.1.val xv i.2.isRight h
      have l3' := liftA ιS ScanJoin.full _ _ _ hent _ _ _ _ l3
      rw [bank_ιS] at l3'
      obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs y1 S3 (leftLabel (leftLabel ()))
        (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ()))))) (c1, cD) (c1, cD) c3 c3'
        _ _ _ _ _ q1 l3'
      obtain ⟨act', rk', hA, hR, hV⟩ := ScanValue.scan_value_some g hg hs3 hq i.1 i.2 j.1 h
      let e : Fin g.edges.length := ⟨j.1.val / r / 3 % g.edges.length, Nat.mod_lt _ h.1⟩
      have hR' := ScanJoin.Wtrue_rank g hg j.1.val r i.1.val xv i.2.isRight e
      refine ⟨u2, ScanJoin.Wtrue g hg j.1.val r i.1.val xv i.2.isRight e, act', rk', t3, ?_, ?_,
        hA, hR, hV, _, q2⟩
      · omega
      · have hrk : rk' = CanonicalEndpointRankMachine.semanticRank
            (RankRun.kindOfNat (j.1.val / r % 3)) (RankRun.itemOfBool i.2.isRight)
            (CanonicalEdgeTape.graphEdge g hg e false).val
            (CanonicalEdgeTape.graphEdge g hg e true).val xv := by
          have := congrArg List.length (hR.symm.trans hR')
          simpa using this
        rw [hrk]
        simp only [scanPosBound, dif_pos h]
        exact Nat.add_le_add_right ht3 _
    · obtain ⟨t3, ht3, c3', l3⟩ := ScanJoin.join_false g j.1.val r i.1.val xv i.2.isRight h
      have l3' := liftA ιS ScanJoin.full _ _ _ hent _ _ _ _ l3
      rw [bank_ιS] at l3'
      obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs y1 S3 (leftLabel (leftLabel ()))
        (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ()))))) (c1, cD) (c1, cD) c3 c3'
        _ _ _ _ _ q1 l3'
      have hN := ScanValue.scan_value_none g hg hs3 hq i.1 i.2 j.1 h
      refine ⟨u2, Function.update (Function.update (ScanJoin.W1 g j.1.val r i.1.val xv
        i.2.isRight) ScanJoin.ansC []) ScanJoin.actC [false], false, 0, t3, ?_, ?_,
        Function.update_self _ _ _, rkC_W1 g j.1.val r i.1.val xv i.2.isRight, ?_, _, q2⟩
      · omega
      · simp only [scanPosBound, dif_neg h]
        omega
      · show Option.map Fin.val (SourceActiveRank.scanAtCanonical
            (CanonicalEdgeTape.graphEdge g hg) hs3 hq (i.1, i.2) j.1) = none
        rw [hN]
        rfl
  obtain ⟨t, T, act, rk, t3, ht, hb3, hA, hR, hV, v, q2⟩ := hscan
  let W3 : JA → List Bool := Sum.elim (Function.update XD2 aC (T K0))
    (Sum.elim (Function.update T K0 []) F4)
  -- phase 5: the source position
  have hSP : ∀ jj, SourcePos.PB [true] [act] rk s jj = W3 (ιP jj) := by
    intro jj
    fin_cases jj
    · show [true] = Function.update XD2 aC (T K0) eqC
      rw [Function.update_of_ne (by simp [eqC, aC])]
      rfl
    · show [act] = Function.update T K0 [] ScanJoin.actC
      rw [Function.update_of_ne (by simp [ScanJoin.actC, K0]), hA]
    · show SourcePos.u rk = Function.update T K0 [] rkC
      rw [Function.update_of_ne (by simp [rkC, K0]), hR]
      rfl
    · show SourcePos.u s = Function.update XD2 aC (T K0) sC
      rw [Function.update_of_ne (by simp [sC, aC])]
      rfl
    · show [] = Function.update XD2 aC (T K0) idxB
      rw [Function.update_of_ne (by simp [idxB, aC])]
      rfl
    · rfl
    · rfl
  obtain ⟨t5, ht5, c5', l5⟩ := SourcePos.pos_run true act rk s
  have l5' := liftA ιP SourcePos.program W3 _ _ hSP _ _ _ _ l5
  let Z := forgetTag ξ₀ (.diagonal j)
  have hpos : (sourcePosition activity i Z).val = if true && act then rk else s :=
    SourcePos.sourcePosition_eq (X := Unit) activity i Z true act rk
      (OTTags.diag_eq ξ₀ j).1 hV
  let pos := if true && act then rk else s
  let W5 := bank ιP W3 (SourcePos.PF s pos)
  have hW5 : W5 = bank ιP W3 (SourcePos.PF s pos) := rfl
  -- phase 6: add unary q₁ to the position
  have h0 : W5 (cpQ 0) = u q₁ := by
    show W5 (.inl tC) = u q₁
    rw [hW5, bank_outside ιP _ _ _ ιP_range_t]
    show Function.update XD2 aC (T K0) tC = u q₁
    rw [Function.update_of_ne (by simp [tC, aC])]
    rfl
  have h1 : W5 (cpQ 1) = u pos := by
    show W5 (ιP 4) = u pos
    rw [hW5, bank_at]
    rfl
  have h2 : W5 (cpQ 2) = [] := by
    show W5 (.inl zC) = []
    rw [hW5, bank_outside ιP _ _ _ ιP_range_z]
    show Function.update XD2 aC (T K0) zC = []
    rw [Function.update_of_ne (by simp [zC, aC])]
    rfl
  have l6 := MatrixStage4ScalarPreparationOps.copy_run cpQ W5 h2
  rw [h0, h1] at l6
  let W6 := Function.update W5 (cpQ 1) (u q₁ ++ u pos)
  -- phase 7: the diagonal tail fetch
  obtain ⟨t7, ht7, v7, l7⟩ := SourceTailFetch.diagonal_source_tail_fetch
    (n := g.vertices) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k i
    activity ξ₀ j O rc0 my0
  have hSF : ∀ kk, FetchIndexed.FB [] [] [] [] (cs.flatten ++ O) (encodeCode col) rc0 my0
      (List.replicate (q₁ + (sourcePosition activity i Z).val) true) kk = W6 (ιF kk) := by
    intro kk
    by_cases hk : kk = FetchIndexed.idxC
    · subst hk
      show List.replicate (q₁ + (sourcePosition activity i Z).val) true =
        Function.update W5 (cpQ 1) (u q₁ ++ u pos) (cpQ 1)
      rw [Function.update_self, hpos, List.replicate_add]
      rfl
    · have hne : ιF kk ≠ cpQ 1 := by
        intro h
        apply hk
        have h' : (Sum.inl (Sum.inl kk) : JA) = Sum.inl (Sum.inl FetchIndexed.idxC) := h
        simpa using h'
      show _ = Function.update W5 (cpQ 1) (u q₁ ++ u pos) (ιF kk)
      rw [Function.update_of_ne hne, hW5, bank_outside ιP _ _ (ιF kk) (ιP_range_F kk hk)]
      show _ = Function.update XD2 aC (T K0) (.inl kk)
      rw [Function.update_of_ne (by simp [aC])]
      rw [FB_idx_irrel _ _ _ _ _ _ _ _ _ [] kk hk]
      rfl
  have l7' := liftA ιF FetchIndexed.colProgram W6 _ _ hSF _ _ _ _ l7
  -- sequencing
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs y2 S5
    (leftLabel (leftLabel (leftLabel ()))) (leftLabel .l0) ((c1, cD), c3) v c5 c5'
    _ _ _ _ _ q2 l5'
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs y3 D6
    (leftLabel (leftLabel (leftLabel (leftLabel ())))) BitMachineCopy.Label.scan
    (((c1, cD), c3), c5) (((c1, cD), c3), c5') ob ob _ _ _ _ _ q3 l6
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs y4 S6
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel ()))))) FetchIndexed.colStart
    ((((c1, cD), c3), c5), ob) ((((c1, cD), c3), c5), ob) FetchIndexed.colControl v7
    _ _ _ _ _ q4 l7'
  refine ⟨u5, ?_, _, _, q5, ?_, ?_⟩
  · have hl : (u q₁).length = q₁ := by simp [u]
    have ht7' : t7 ≤ FetchIndexed.colBound (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2
        (List.ofFn fun a : Fin (q₁ + s + 1) =>
          (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode (j.2 a))
        (q₁ + (sourcePosition (SourceActiveRank.scanAtCanonical
          (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) i
          (forgetTag ξ₀ (.diagonal j))).val) O := ht7
    have hb3' : t3 + (rk + 3) ≤ scanPosBound g hg j.1.val r i.1.val
        (CanonicalEndpointRankBridge.itemValue i.2) i.2.isRight := hb3
    have ht' : t ≤ (1 + ((i.1.val + 1) + 1 + (CanonicalEndpointRankBridge.itemValue i.2 + 1) + 2)
        + 1) + (j.1.val + 1 + 1 + 1) + 1 + t3 + 1 := ht
    rw [hl] at hu4
    simp only [srcDBound]
    omega
  · rw [← ιF_lbl, bank_at]
    rfl
  · rw [bank_outside ιF _ _ srcA ιF_range_src]
    show Function.update W5 (cpQ 1) (u q₁ ++ u pos) srcA = _
    rw [Function.update_of_ne (by simp [cpQ, cpQFun, srcA, idxB]), hW5,
      bank_outside ιP _ _ srcA ιP_range_src]
    rfl

#print axioms upd_fw
#print axioms cpQFun_injective
#print axioms srcD_run

end

end Paper2.SrcD
