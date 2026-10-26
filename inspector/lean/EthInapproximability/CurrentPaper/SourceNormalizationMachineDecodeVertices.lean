import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeShift
import EthInapproximability.CurrentPaper.SourceNormalizationMachineOffsetWidth

/-! Complete unary vertex-count computation after copy-major endpoint shifting. -/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeVertices

open Turing BitMachineEncoding

abbrev Stack := SourceNormalizationMachineDecodeShift.Stack
abbrev Label := SourceNormalizationMachineDecodeShift.Label ⊕
  SourceNormalizationMachineOffsetWidth.Phase
abbrev Control := SourceNormalizationMachineDecodeShift.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def offsetStack : SourceNormalizationMachineOffsetWidth.Stack ↪ Stack where
  toFun k := match k.val with
    | 0 => SourceNormalizationMachineDecodeShift.shiftStack 7
    | 1 => SourceNormalizationMachineDecodeShift.shiftStack 8
    | 2 => SourceNormalizationMachineDecodeShift.shiftStack 1
    | _ => SourceNormalizationMachineDecodeShift.shiftStack 4
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [SourceNormalizationMachineDecodeShift.shiftStack]

def decodeControl (v : SourceNormalizationMachineDecodeShift.Control) : Control :=
  (v,none)

def afterShiftControl : SourceNormalizationMachineDecodeShift.Control :=
  SourceNormalizationMachineDecodeShift.shiftControl (false,none)

def offsetControl (v : Option Bool) : Control := (afterShiftControl,v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineInline.stmt Sum.inl decodeControl Prod.fst
      (some (.inr .scan)) (SourceNormalizationMachineDecodeShift.program l)
  | .inr l => BitMachineStackEmbedding.stmt offsetStack Sum.inr
      offsetControl Prod.snd none (SourceNormalizationMachineOffsetWidth.program l)

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def start (graphBits : List Bool) (originalN : ℕ) : Config :=
  BitMachineInline.cfg Sum.inl decodeControl (some (.inr .scan))
    (SourceNormalizationMachineDecodeShift.start graphBits originalN)

noncomputable def afterShift (g : EncodedGraph.Graph) (originalN : ℕ) : Config :=
  BitMachineInline.cfg Sum.inl decodeControl (some (.inr .scan))
    (BitMachineStackEmbedding.cfg SourceNormalizationMachineDecodeShift.shiftStack
      (SourceNormalizationMachineDecodeShift.afterDoubleHost g originalN).stk
      Sum.inr SourceNormalizationMachineDecodeShift.shiftControl none
      (SourceNormalizationMachineDecodeShift.shiftFinalCfg g originalN))

def localBits (g : EncodedGraph.Graph) : List Bool :=
  SourceNormalizationMachineDecodeShift.localBits g

def copies (g : EncodedGraph.Graph) (originalN : ℕ) : ℕ :=
  SourceNormalizationMachineDecodeShift.copies g originalN

def shiftedStream (g : EncodedGraph.Graph) (originalN : ℕ) : List Bool :=
  SourceNormalizationMachineShiftCopies.shiftedFrom
    (SourceNormalizationMachineDecodeShift.localIndices g)
    ((localBits g).count true) 0 (copies g originalN)

def offsetInitialCfg (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineOffsetWidth.Config :=
  SourceNormalizationMachineOffsetWidth.cfg (some .scan) none
    (localBits g) []
    (List.replicate ((copies g originalN - 1) * (localBits g).count true) true)
    (shiftedStream g originalN)

def offsetFinalCfg (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineOffsetWidth.Config :=
  SourceNormalizationMachineOffsetWidth.cfg none none
    (localBits g) []
    (List.replicate (copies g originalN * (localBits g).count true) true)
    (shiftedStream g originalN)

private theorem decode_program_eq (l : SourceNormalizationMachineDecodeShift.Label) :
    program (.inl l) = BitMachineInline.stmt Sum.inl decodeControl Prod.fst
      (some (.inr .scan)) (SourceNormalizationMachineDecodeShift.program l) := rfl

private theorem offset_program_eq (l : SourceNormalizationMachineOffsetWidth.Phase) :
    program (.inr l) = BitMachineStackEmbedding.stmt offsetStack Sum.inr
      offsetControl Prod.snd none (SourceNormalizationMachineOffsetWidth.program l) := rfl

theorem decode_stage (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecodeDouble.rankBound g originalN +
      2 * (g.edges.length + 1) + 2 +
      SourceNormalizationMachineDecodeShift.shiftCost g originalN,
      run t (start (EncodedGraph.encode g) originalN) =
        afterShift g originalN := by
  obtain ⟨a,ha,hr⟩ :=
    SourceNormalizationMachineDecodeShift.decode_shift_run g hg originalN
  obtain ⟨t,ht,he⟩ := BitMachineInline.outputs Sum.inl
    decodeControl Prod.fst (by intro v; rfl) (some (.inr .scan))
    SourceNormalizationMachineDecodeShift.program program decode_program_eq
    (SourceNormalizationMachineDecodeShift.start (EncodedGraph.encode g) originalN)
    a (by
      change (SourceNormalizationMachineDecodeShift.run a
        (SourceNormalizationMachineDecodeShift.start
          (EncodedGraph.encode g) originalN)).l = none
      rw [hr]
      rfl)
  change ((advance SourceNormalizationMachineDecodeShift.program)^[a]) _ = _ at hr
  rw [hr] at he
  exact ⟨t, ht.trans ha, he⟩

private theorem offset_initial_stacks (g : EncodedGraph.Graph) (originalN : ℕ) :
    ∀ k : SourceNormalizationMachineOffsetWidth.Stack,
      (offsetInitialCfg g originalN).stk k =
        (afterShift g originalN).stk (offsetStack k) := by
  intro k
  fin_cases k
  all_goals
    simp only [offsetInitialCfg, SourceNormalizationMachineOffsetWidth.cfg,
      afterShift, BitMachineInline.cfg, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, offsetStack]
    dsimp only [Function.Embedding.coeFn_mk]
    rw [BitMachineStackEmbedding.bank_at]
    rfl

private theorem offset_initial (g : EncodedGraph.Graph) (originalN : ℕ) :
    afterShift g originalN =
      BitMachineStackEmbedding.cfg offsetStack (afterShift g originalN).stk
        Sum.inr offsetControl none (offsetInitialCfg g originalN) := by
  have hs := BitMachineStackEmbedding.bank_eq_self offsetStack
    (afterShift g originalN).stk (offsetInitialCfg g originalN).stk
    (offset_initial_stacks g originalN)
  change (⟨some (.inr SourceNormalizationMachineOffsetWidth.Phase.scan),
    (afterShiftControl,none), (afterShift g originalN).stk⟩ : Config) =
    ⟨some (.inr SourceNormalizationMachineOffsetWidth.Phase.scan),
      (afterShiftControl,none),
      BitMachineStackEmbedding.bank offsetStack (afterShift g originalN).stk
        (offsetInitialCfg g originalN).stk⟩
  rw [hs]

private theorem offset_run (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineOffsetWidth.run (2 * (localBits g).length + 2)
      (offsetInitialCfg g originalN) = offsetFinalCfg g originalN := by
  have h := SourceNormalizationMachineOffsetWidth.add_width_run
    (localBits g) (shiftedStream g originalN)
    ((copies g originalN - 1) * (localBits g).count true)
  have hp : 0 < copies g originalN :=
    ParameterizedNP.GuardedSourceGraph.copyCount_pos originalN g.edges.length
  have hn : (copies g originalN - 1) * (localBits g).count true +
      (localBits g).count true =
      copies g originalN * (localBits g).count true := by
    have hc : copies g originalN - 1 + 1 = copies g originalN := by omega
    calc
      _ = (copies g originalN - 1 + 1) * (localBits g).count true := by ring
      _ = _ := by rw [hc]
  simpa only [offsetInitialCfg, offsetFinalCfg, hn] using h

theorem decode_vertices_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecodeDouble.rankBound g originalN +
      2 * (g.edges.length + 1) + 2 +
      SourceNormalizationMachineDecodeShift.shiftCost g originalN +
      2 * (localBits g).length + 2,
      run t (start (EncodedGraph.encode g) originalN) =
        BitMachineStackEmbedding.cfg offsetStack (afterShift g originalN).stk
          Sum.inr offsetControl none (offsetFinalCfg g originalN) := by
  obtain ⟨a,ha,hdecode⟩ := decode_stage g hg originalN
  have hlocal := offset_run g originalN
  obtain ⟨b,hb,hr⟩ := BitMachineStackEmbedding.outputs offsetStack
    (afterShift g originalN).stk Sum.inr offsetControl Prod.snd
    (by intro v; rfl) none
    SourceNormalizationMachineOffsetWidth.program program offset_program_eq
    (offsetInitialCfg g originalN) (2 * (localBits g).length + 2)
    (by
      change (SourceNormalizationMachineOffsetWidth.run
        (2 * (localBits g).length + 2) (offsetInitialCfg g originalN)).l = none
      rw [hlocal]
      rfl)
  change ((advance SourceNormalizationMachineOffsetWidth.program)^[2 * (localBits g).length + 2])
      _ = _ at hlocal
  rw [hlocal] at hr
  refine ⟨a + b, by omega, ?_⟩
  exact (run_add hdecode b).trans
    ((congrArg (run b) (offset_initial g originalN)).trans
      (by simpa only [run] using hr))

noncomputable def finalHost (g : EncodedGraph.Graph) (originalN : ℕ) : Config :=
  BitMachineStackEmbedding.cfg offsetStack (afterShift g originalN).stk
    Sum.inr offsetControl none (offsetFinalCfg g originalN)

theorem final_vertices (g : EncodedGraph.Graph) (originalN : ℕ) :
    (finalHost g originalN).stk (offsetStack 2) =
      List.replicate (SourceNormalizationNumeric.numericGraph g originalN).vertices true := by
  change BitMachineStackEmbedding.bank offsetStack _ _ (offsetStack 2) = _
  rw [BitMachineStackEmbedding.bank_at]
  change List.replicate
      (SourceNormalizationNumeric.repetitions g originalN *
        (SourceNormalizationNumeric.paddedSupport g).count true) true =
    List.replicate
      (SourceNormalizationNumeric.repetitions g originalN *
        ((SourceNormalizationNumeric.support g).count true + 2)) true
  rw [SourceNormalizationMachineDecodeRepeat.padded_width_eq_numeric]

theorem final_stream (g : EncodedGraph.Graph) (hg : g.Valid) (originalN : ℕ) :
    (finalHost g originalN).stk (offsetStack 3) =
      SourceNormalizationMachineMark.endpointStream
        (SourceNormalizationNumeric.endpoints
          (SourceNormalizationNumeric.numericGraph g originalN)) := by
  change BitMachineStackEmbedding.bank offsetStack _ _ (offsetStack 3) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact SourceNormalizationMachineDecodeShift.shifted_eq_numeric g hg originalN

end EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeVertices
