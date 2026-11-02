import Paper2.SrcD
import Paper2.SrcF
import Paper2.TagDispatch

/-! Unit 3, segment (1): the source arm for ALL THREE tags as ONE program on
ONE bank, with the tag-bit dispatch.

Bank `JX = SrcU.JA ⊕ DefaultWordLoop.LB`. Entry bank `WXb … rowW fw`
(shared by the three tags): the `SrcU` bank with the tagged column word
`fw` (tag bits NOT popped) in the fetch-word cell, the serialized column and
outer codes, unary `s+1` (`my`), unary `s` (`sC`), the scan region `JJ0 g r`
(unary `r`, unary `m`, literal public graph bytes), the raw source-row word
in `srcA`, every other `JA` cell blank; and the admitted
`DefaultWordLoop.entry p q₁ s Q w k` (unary `q₁, s, Q, p, w`, `k` marks).

Program `srcX` (production `TagDispatch.ifProgram` twice on the fetch-word
cell, production `BitMachineRawSequence` handoffs):
* tag `false` (unrestricted): `SrcU.srcU` (frozen owner-5) lifted by `Sum.inl`;
* tag `true, false` (fixed tail): `SrcF.armF` (frozen owner-5) placed by `ιFX`
  (its `Fin 4` cells ARE `srcA, iA, iK, iX`, its loop bank IS the `LB` part),
  then the production `copyProgram` of the default column word (row-machine
  cell 3 of `LB`) into the label cell `lblB`;
* tag `true, true` (diagonal): the production `copyProgram` of unary `q₁`
  (row-machine cell 0 of `LB`, preserved) into the lane cell `tC`, then
  `SrcD.srcD` (frozen owner-5) lifted by `Sum.inl`.
All three branches end with the source column word in `lblB` and the row word
`C.1.encode u` in `srcA`. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SrcX

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
open Paper2.CanonicalDefaultWordScratch (words)

abbrev JX := SrcU.JA ⊕ DefaultWordLoop.LB

def inA : SrcU.JA ↪ JX := ⟨Sum.inl, Sum.inl_injective⟩

def fwX : JX := .inl (.inl (.inl FetchIndexed.fwC))
def lblX : JX := .inl (.inl lblB)
def srcAX : JX := .inl SrcU.srcA

def ιFXf : SrcF.JF → JX
  | .inl l => .inr l
  | .inr q => (![.inl SrcU.srcA, .inl SrcU.iA, .inl SrcU.iK, .inl SrcU.iX] : Fin 4 → JX) q

theorem ιFXf_injective : Function.Injective ιFXf := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · simpa [ιFXf] using h
  · fin_cases b <;> simp [ιFXf] at h
  · fin_cases a <;> simp [ιFXf] at h
  · fin_cases a <;> fin_cases b <;> simp_all [ιFXf, SrcU.srcA, SrcU.iA, SrcU.iK, SrcU.iX]

def ιFX : SrcF.JF ↪ JX := ⟨ιFXf, ιFXf_injective⟩

theorem ιFX_range_z : ¬ ∃ kk, ιFX kk = (.inl (.inl zC) : JX) := by
  rintro ⟨kk, hkk⟩
  rcases kk with kk | kk
  · cases hkk
  · fin_cases kk <;> simp [ιFX, ιFXf, SrcU.srcA, SrcU.iA, SrcU.iK, SrcU.iX, zC] at hkk

theorem ιFX_range_lbl : ¬ ∃ kk, ιFX kk = (.inl (.inl lblB) : JX) := by
  rintro ⟨kk, hkk⟩
  rcases kk with kk | kk
  · cases hkk
  · fin_cases kk <;> simp [ιFX, ιFXf, SrcU.srcA, SrcU.iA, SrcU.iK, SrcU.iX, lblB] at hkk

def cpLf : Fin 3 → JX := ![.inr (.inl (3 : Fin 10)), .inl (.inl lblB), .inl (.inl zC)]

theorem cpLf_injective : Function.Injective cpLf := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [cpLf, lblB, zC]

def cpL : Fin 3 ↪ JX := ⟨cpLf, cpLf_injective⟩

def cpTf : Fin 3 → JX := ![.inr (.inl (0 : Fin 10)), .inl (.inl tC), .inl (.inl zC)]

theorem cpTf_injective : Function.Injective cpTf := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [cpTf, tC, zC]

def cpT : Fin 3 ↪ JX := ⟨cpTf, cpTf_injective⟩

theorem liftX {Kk L V : Type*} [DecidableEq Kk] (ι : Kk ↪ JX)
    (P : L → TM2.Stmt (fun _ : Kk => Bool) L V)
    (W : JX → List Bool) (S T : Kk → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : JX => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

theorem bank_inA (X : SrcU.JA → List Bool) (Y : DefaultWordLoop.LB → List Bool)
    (T : SrcU.JA → List Bool) :
    bank inA (Sum.elim X Y) T = Sum.elim T Y := by
  funext j
  cases j with
  | inl j => exact bank_at inA _ T j
  | inr j => exact bank_outside inA _ T (.inr j) (by rintro ⟨k, hk⟩; cases hk)

/-! ### Programs -/

def PU := fun l => stackStmt inA (SrcU.srcU l)
def PF1 := fun l => stackStmt ιFX (SrcF.armF l)
def PF2 := MatrixStage4ScalarPreparationOps.copyProgram cpL
def PF := BitMachineRawSequence.program PF1 PF2 BitMachineCopy.Label.scan
  (SrcF.d1, SrcF.d2) (none : Option Bool)
def PD1 := MatrixStage4ScalarPreparationOps.copyProgram cpT
def PD2 := fun l => stackStmt inA (SrcD.srcD l)
def PD := BitMachineRawSequence.program PD1 PD2 SrcD.srcDStart (none : Option Bool)
  SrcD.srcDCtl

abbrev ctlF := ((SrcF.d1, SrcF.d2), (none : Option Bool))
abbrev ctlD := ((none : Option Bool), SrcD.srcDCtl)
abbrev ctlQ := ((none : Option Bool), (ctlF, ctlD))

def QI := TagDispatch.ifProgram fwX PF PD (leftLabel (leftLabel (leftLabel ())))
  (leftLabel BitMachineCopy.Label.scan) ctlF ctlD

/-- The source arm for all three tags: one fixed program. -/
def srcX := TagDispatch.ifProgram fwX PU QI SrcU.srcUStart (.inl ()) SrcU.srcUCtl ctlQ

def srcXCtl := ((none : Option Bool), (SrcU.srcUCtl, ctlQ))

/-! ### The shared entry bank -/

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The shared entry bank of the three arms (`fw` = tagged column word ++ suffix). -/
def WXb (g : EncodedGraph.Graph) (r k : ℕ) (rowW fw : List Bool) : JX → List Bool :=
  Sum.elim (Sum.elim (BB [] fw (encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2)
      (encodeCode (outerCode q₁ q₂ s (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2))
      (u (s + 1)) [] [] [] [] [] [] [] (u s))
    (Sum.elim (SrcU.JJ0 g r) ![rowW, [], [], []]))
    (DefaultWordLoop.entry p q₁ s Q w k)

theorem WXb_fw (g : EncodedGraph.Graph) (r k : ℕ) (rowW fw fw' : List Bool) :
    Function.update (WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k rowW fw)
        fwX fw' = WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k rowW fw' := by
  simp only [WXb, fwX, Sum.update_elim_inl, SrcD.upd_fw]

theorem WXb_at_fw (g : EncodedGraph.Graph) (r k : ℕ) (rowW fw : List Bool) :
    WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k rowW fw fwX = fw := rfl

/-- The explicit composite clock, by tag. -/
def srcXBound (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r) (k : ℕ)
    (i : SourceConstruction.Items s (Fin g.vertices))
    (ξ₀ : Tail s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k))
    (O : List Bool) :
    TaggedColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k) → ℕ
  | .unrestricted Z => SrcU.srcUBound g hg hs r hq k i Z O + 1
  | .fixedTail _ =>
      ((1 + ((i.1.val + 1) + 1 + (CanonicalEndpointRankBridge.itemValue i.2 + 1) + 2) + 1) +
        ((1 + (p * 5 + 1) + (2 * p + 2) + (p + 1) + 2 + 1 + 5) +
          (k * (DefaultWordLoop.levelBound p s q₁ q₂ w Q k + 2) + 1) + 1) + 1) +
      (2 * (words p s q₁ q₂ w Q k).2.length + 2) + 1 + 1 + 1
  | .diagonal j => (2 * q₁ + 2) + SrcD.srcDBound g hg hs r hq k i ξ₀ j O + 1 + 1 + 1

/-- Segment (1): the source arm for every tag, ONE program on ONE bank. For
the fixed tail the column word is the default column word; its identity with
the encoded source column is the premise `hfix` (discharged at the canonical
widths and tails by `SrcF.fixed_source_value`, see `srcX_run_canonical`). -/
theorem srcX_run (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r) (k : ℕ)
    (i : SourceConstruction.Items s (Fin g.vertices))
    (uu : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q k)
    (ξ₀ : Tail s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k))
    (zt : TaggedColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k))
    (O : List Bool)
    (hfix : ∀ js : Fin s → OuterColumn q₁ q₂ s (Column (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q k),
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode
      (sourceColumn (SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
        (by omega) hq) i (forgetTag ξ₀ (.fixedTail js))) = (words p s q₁ q₂ w Q k).2) :
    let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k
    let activity := SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by omega) hq
    ∃ t ≤ srcXBound g hg hs r hq k i ξ₀ O zt, ∃ v F,
      ((advance srcX)^[t])
        (⟨some (.inl ()), srcXCtl,
          WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k ((prodCodec (defaultItemCodec g.vertices s) C.1).encode (i, uu))
            ((taggedColumnCodec q₁ q₂ s C.2).encode zt ++ O)⟩ :
          TM2.Cfg (fun _ : JX => Bool) _ _) = ⟨none, v, F⟩ ∧
      F lblX = C.2.encode (sourceColumn activity i (forgetTag ξ₀ zt)) ∧
      F srcAX = C.1.encode uu := by
  intro C activity
  let rowW := (prodCodec (defaultItemCodec g.vertices s) C.1).encode (i, uu)
  let col := (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2
  cases zt with
  | unrestricted Z =>
    obtain ⟨t1, ht1, v1, F1, l1, h1, h2, -, -, -⟩ := SrcU.srcU_run (w := w) (Q := Q)
      g hg hp hs r hq k i uu Z O
    have hW : ∀ kk, (Sum.elim (BB [] ((rawColumnCodec q₁ q₂ s C.2).encode Z ++ O)
        (encodeCode col) (encodeCode (outerCode q₁ q₂ s col)) (u (s + 1))
        [] [] [] [] [] [] [] (u s)) (Sum.elim (SrcU.JJ0 g r) ![rowW, [], [], []]) :
          SrcU.JA → List Bool) kk =
        Function.update (WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
          g r k rowW ((taggedColumnCodec q₁ q₂ s C.2).encode (.unrestricted Z) ++ O)) fwX
          ((rawColumnCodec q₁ q₂ s C.2).encode Z ++ O) (inA kk) := by
      intro kk
      rw [WXb_fw]
      rfl
    have l1' := liftX inA SrcU.srcU _ _ _ hW _ _ _ _ l1
    obtain ⟨t0, ht0, q0⟩ := TagDispatch.if_false fwX PU QI SrcU.srcUStart (.inl ())
      SrcU.srcUCtl ctlQ (WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
          g r k rowW ((taggedColumnCodec q₁ q₂ s C.2).encode (.unrestricted Z) ++ O))
      ((rawColumnCodec q₁ q₂ s C.2).encode Z ++ O) rfl t1 v1 _ l1'
    refine ⟨t0, ?_, _, _, q0, ?_, ?_⟩
    · show t0 ≤ SrcU.srcUBound g hg hs r hq k i Z O + 1
      omega
    · show bank inA _ F1 (inA (.inl lblB)) = _
      rw [bank_at]
      exact h1
    · show bank inA _ F1 (inA SrcU.srcA) = _
      rw [bank_at]
      exact h2
  | fixedTail js =>
    let tw := (piCodec (outerColumnCodec q₁ q₂ s C.2) s).encode js ++ O
    let W2 := WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k rowW tw
    obtain ⟨t1, ht1, v1, l1⟩ := SrcF.srcF_run (n := g.vertices) (p := p) (s := s) (q₁ := q₁)
      (q₂ := q₂) (w := w) (Q := Q) k i uu
    have hW : ∀ kk, (Sum.elim (DefaultWordLoop.entry p q₁ s Q w k)
        ![rowW, [], [], []] : SrcF.JF → List Bool) kk = W2 (ιFX kk) := by
      intro kk
      rcases kk with kk | kk
      · rfl
      · fin_cases kk <;> rfl
    have l1' := liftX ιFX SrcF.armF _ _ _ hW _ _ _ _ l1
    let W3 := bank ιFX W2 (Sum.elim (DefaultWordLoop.S q₁ s Q w (words p s q₁ q₂ w Q k).1
        (words p s q₁ q₂ w Q k).2 [])
      ![C.1.encode uu, List.replicate i.1.val true, [i.2.isRight],
        CanonicalEndpointRankMachine.unaryWord (CanonicalEndpointRankBridge.itemValue i.2)])
    have hz : W3 (cpL 2) = [] := by
      show bank ιFX W2 _ (.inl (.inl zC)) = []
      rw [bank_outside ιFX _ _ _ ιFX_range_z]
      rfl
    have h0 : W3 (cpL 0) = (words p s q₁ q₂ w Q k).2 := by
      show bank ιFX W2 _ (ιFX (.inl (.inl (3 : Fin 10)))) = _
      rw [bank_at]
      rfl
    have hl : W3 (cpL 1) = [] := by
      show bank ιFX W2 _ (.inl (.inl lblB)) = []
      rw [bank_outside ιFX _ _ _ ιFX_range_lbl]
      rfl
    have l2 := MatrixStage4ScalarPreparationOps.copy_run cpL W3 hz
    rw [h0, hl] at l2
    obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs PF1 PF2
      (leftLabel (leftLabel ())) BitMachineCopy.Label.scan (SrcF.d1, SrcF.d2) v1
      (none : Option Bool) none _ _ _ _ _ l1' l2
    obtain ⟨ta, hta, qa⟩ := TagDispatch.if_false fwX PF PD
      (leftLabel (leftLabel (leftLabel ()))) (leftLabel BitMachineCopy.Label.scan) ctlF ctlD
      (Function.update (WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        g r k rowW ((taggedColumnCodec q₁ q₂ s C.2).encode (.fixedTail js) ++ O)) fwX
        (false :: tw)) tw (by rw [Function.update_self]) u1 _ _
      (by rw [Function.update_idem, WXb_fw]; exact q1)
    obtain ⟨t0, ht0, q0⟩ := TagDispatch.if_true fwX PU QI SrcU.srcUStart (.inl ())
      SrcU.srcUCtl ctlQ (WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
          g r k rowW ((taggedColumnCodec q₁ q₂ s C.2).encode (.fixedTail js) ++ O))
      (false :: tw) rfl ta _ _ qa
    refine ⟨t0, ?_, _, _, q0, ?_, ?_⟩
    · show t0 ≤ ((1 + ((i.1.val + 1) + 1 + (CanonicalEndpointRankBridge.itemValue i.2 + 1) + 2) + 1) +
        ((1 + (p * 5 + 1) + (2 * p + 2) + (p + 1) + 2 + 1 + 5) +
          (k * (DefaultWordLoop.levelBound p s q₁ q₂ w Q k + 2) + 1) + 1) + 1) +
        (2 * (words p s q₁ q₂ w Q k).2.length + 2) + 1 + 1 + 1
      omega
    · show Function.update W3 (cpL 1) ((words p s q₁ q₂ w Q k).2 ++ []) (cpL 1) = _
      rw [Function.update_self, List.append_nil]
      exact (hfix js).symm
    · show Function.update W3 (cpL 1) ((words p s q₁ q₂ w Q k).2 ++ []) (ιFX (.inr 0)) = _
      rw [Function.update_of_ne (by simp [cpL, cpLf, ιFX, ιFXf, SrcU.srcA, lblB])]
      show bank ιFX W2 _ (ιFX (.inr 0)) = _
      rw [bank_at]
      rfl
  | diagonal j =>
    let cs := List.ofFn (fun a : Fin (q₁ + s + 1) => C.2.encode (j.2 a))
    let dw := List.replicate j.1.val true ++ false :: (cs.flatten ++ O)
    let W2 := WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k rowW dw
    have hz : W2 (cpT 2) = [] := rfl
    have ht : W2 (cpT 1) = [] := rfl
    have h0 : W2 (cpT 0) = u q₁ := rfl
    have l1 := MatrixStage4ScalarPreparationOps.copy_run cpT W2 hz
    rw [h0, ht, List.append_nil] at l1
    obtain ⟨t2, ht2, v2, F2, l2, h1, h2⟩ := SrcD.srcD_run (w := w) (Q := Q)
      g hg hp hs r hq k i uu ξ₀ j O (encodeCode (outerCode q₁ q₂ s col)) (u (s + 1))
    have hW : ∀ kk, (Sum.elim (BB [] dw (encodeCode col) (encodeCode (outerCode q₁ q₂ s col))
        (u (s + 1)) [] [] (u q₁) [] [] [] [] (u s))
        (Sum.elim (SrcU.JJ0 g r) ![rowW, [], [], []]) : SrcU.JA → List Bool) kk =
        Function.update W2 (cpT 1) (u q₁) (inA kk) := by
      intro kk
      have e : Function.update W2 (cpT 1) (u q₁) =
          Sum.elim (Sum.elim (BB [] dw (encodeCode col) (encodeCode (outerCode q₁ q₂ s col))
            (u (s + 1)) [] [] (u q₁) [] [] [] [] (u s))
            (Sum.elim (SrcU.JJ0 g r) ![rowW, [], [], []])) (DefaultWordLoop.entry p q₁ s Q w k) := by
        simp only [W2, WXb, cpT, cpTf, Function.Embedding.coeFn_mk, Matrix.cons_val_one,
          Matrix.cons_val_zero, Sum.update_elim_inl, OTBody.upd_t]
        rfl
      rw [e]
      rfl
    have l2' := liftX inA SrcD.srcD _ _ _ hW _ _ _ _ l2
    obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs PD1 PD2
      BitMachineCopy.Label.scan SrcD.srcDStart (none : Option Bool) none SrcD.srcDCtl v2
      _ _ _ _ _ l1 l2'
    have hdw : (taggedColumnCodec q₁ q₂ s C.2).encode (.diagonal j) ++ O =
        true :: true :: dw := by
      rw [OTTags.diag_word]
      simp only [dw, cs, List.cons_append, List.append_assoc]
      rfl
    obtain ⟨ta, hta, qa⟩ := TagDispatch.if_true fwX PF PD
      (leftLabel (leftLabel (leftLabel ()))) (leftLabel BitMachineCopy.Label.scan) ctlF ctlD
      (Function.update (WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        g r k rowW ((taggedColumnCodec q₁ q₂ s C.2).encode (.diagonal j) ++ O)) fwX
        (true :: dw)) dw (by rw [Function.update_self]) u1 _ _
      (by rw [Function.update_idem, WXb_fw]; exact q1)
    obtain ⟨t0, ht0, q0⟩ := TagDispatch.if_true fwX PU QI SrcU.srcUStart (.inl ())
      SrcU.srcUCtl ctlQ (WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
          g r k rowW ((taggedColumnCodec q₁ q₂ s C.2).encode (.diagonal j) ++ O))
      (true :: dw) (by rw [WXb_at_fw, hdw]) ta _ _ qa
    refine ⟨t0, ?_, _, _, q0, ?_, ?_⟩
    · have hl : (u q₁).length = q₁ := by simp [u]
      rw [hl] at hu1
      show t0 ≤ (2 * q₁ + 2) + SrcD.srcDBound g hg hs r hq k i ξ₀ j O + 1 + 1 + 1
      omega
    · show bank inA _ F2 (inA (.inl lblB)) = _
      rw [bank_at]
      exact h1
    · show bank inA _ F2 (inA SrcU.srcA) = _
      rw [bank_at]
      exact h2

end

#print axioms ιFXf_injective
#print axioms ιFX_range_z
#print axioms ιFX_range_lbl
#print axioms cpLf_injective
#print axioms cpTf_injective
#print axioms liftX
#print axioms bank_inA
#print axioms WXb_fw
#print axioms srcX_run

end Paper2.SrcX
