import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeVertices
import EthInapproximability.CurrentPaper.SourceNormalizationMachineEndpointWriter

/-! Physical composition of ordered normalization and canonical endpoint fields. -/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeWrite

open Turing BitMachineEncoding

abbrev Stack := SourceNormalizationMachineDecodeVertices.Stack ⊕
  SourceNormalizationMachineEndpointWriter.Stack
abbrev Label := SourceNormalizationMachineDecodeVertices.Label ⊕
  SourceNormalizationMachineEndpointWriter.Label
abbrev Control := SourceNormalizationMachineDecodeVertices.Control ×
  SourceNormalizationMachineEndpointWriter.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def decodeStack : SourceNormalizationMachineDecodeVertices.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def writerStack : SourceNormalizationMachineEndpointWriter.Stack ↪ Stack where
  toFun
    | .inl k => .inr (.inl k)
    | .inr k => if k = 0 then
        .inl (SourceNormalizationMachineDecodeVertices.offsetStack 3)
      else .inr (.inr k)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b => simpa using h
        | inr b => fin_cases b <;> simp at h
    | inr a =>
        cases b with
        | inl b => fin_cases a <;> simp at h
        | inr b => fin_cases a <;> fin_cases b <;> simp_all

noncomputable def decodeControl (v : SourceNormalizationMachineDecodeVertices.Control) : Control :=
  (v,(none,(SourceNormalizationMachineEndpointWriter.counter.initial,none)))

def afterDecodeControl : SourceNormalizationMachineDecodeVertices.Control :=
  (SourceNormalizationMachineDecodeVertices.afterShiftControl,none)

def writerControl (v : SourceNormalizationMachineEndpointWriter.Control) : Control :=
  (afterDecodeControl,v)

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt decodeStack Sum.inl
      decodeControl Prod.fst (some (.inr (.inl .read)))
      (SourceNormalizationMachineDecodeVertices.program l)
  | .inr l => BitMachineStackEmbedding.stmt writerStack Sum.inr
      writerControl Prod.snd none
      (SourceNormalizationMachineEndpointWriter.program l)

noncomputable def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

noncomputable def start (graphBits : List Bool) (originalN : ℕ) : Config :=
  ⟨(SourceNormalizationMachineDecodeVertices.start graphBits originalN).l.map Sum.inl,
    decodeControl (SourceNormalizationMachineDecodeVertices.start graphBits originalN).var,
    Sum.elim (SourceNormalizationMachineDecodeVertices.start graphBits originalN).stk
      (fun _ => [])⟩

noncomputable def afterDecode (g : EncodedGraph.Graph) (originalN : ℕ) : Config :=
  BitMachineStackEmbedding.cfg decodeStack
    (start (EncodedGraph.encode g) originalN).stk Sum.inl decodeControl
    (some (.inr (.inl .read)))
    (SourceNormalizationMachineDecodeVertices.finalHost g originalN)

private theorem decode_program_eq (l : SourceNormalizationMachineDecodeVertices.Label) :
    program (.inl l) = BitMachineStackEmbedding.stmt decodeStack Sum.inl
      decodeControl Prod.fst (some (.inr (.inl .read)))
      (SourceNormalizationMachineDecodeVertices.program l) := rfl

private theorem writer_program_eq (l : SourceNormalizationMachineEndpointWriter.Label) :
    program (.inr l) = BitMachineStackEmbedding.stmt writerStack Sum.inr
      writerControl Prod.snd none
      (SourceNormalizationMachineEndpointWriter.program l) := rfl

private theorem decode_initial (graphBits : List Bool) (originalN : ℕ) :
    BitMachineStackEmbedding.cfg decodeStack (start graphBits originalN).stk
      Sum.inl decodeControl (some (.inr (.inl .read)))
      (SourceNormalizationMachineDecodeVertices.start graphBits originalN) =
    start graphBits originalN := by
  have hb := BitMachineStackEmbedding.bank_eq_self decodeStack
    (start graphBits originalN).stk
    (SourceNormalizationMachineDecodeVertices.start graphBits originalN).stk
    (by intro k; rfl)
  change (⟨_,_, BitMachineStackEmbedding.bank decodeStack
    (start graphBits originalN).stk
    (SourceNormalizationMachineDecodeVertices.start graphBits originalN).stk⟩ :
    Config) = _
  rw [hb]
  rfl

theorem decode_stage (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecodeDouble.rankBound g originalN +
      2 * (g.edges.length + 1) + 2 +
      SourceNormalizationMachineDecodeShift.shiftCost g originalN +
      2 * (SourceNormalizationMachineDecodeVertices.localBits g).length + 2,
      run t (start (EncodedGraph.encode g) originalN) =
        afterDecode g originalN := by
  obtain ⟨a,ha,hr⟩ :=
    SourceNormalizationMachineDecodeVertices.decode_vertices_run g hg originalN
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs decodeStack
    (start (EncodedGraph.encode g) originalN).stk Sum.inl
    decodeControl Prod.fst (by intro v; rfl)
    (some (.inr (.inl .read)))
    SourceNormalizationMachineDecodeVertices.program program decode_program_eq
    (SourceNormalizationMachineDecodeVertices.start
      (EncodedGraph.encode g) originalN) a (by
      change (SourceNormalizationMachineDecodeVertices.run a
        (SourceNormalizationMachineDecodeVertices.start
          (EncodedGraph.encode g) originalN)).l = none
      rw [hr]
      rfl)
  change ((advance SourceNormalizationMachineDecodeVertices.program)^[a]) _ = _ at hr
  rw [hr] at he
  exact ⟨t, ht.trans ha, (decode_initial (EncodedGraph.encode g) originalN).symm ▸ he⟩

def numeric (g : EncodedGraph.Graph) (originalN : ℕ) : EncodedGraph.Graph :=
  SourceNormalizationNumeric.numericGraph g originalN

noncomputable def writerInitial (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineEndpointWriter.Config :=
  SourceNormalizationMachineEndpointWriter.start
    (SourceNormalizationMachineEndpointWriter.unaryEdges
      (numeric g originalN).edges)

private theorem afterDecode_at (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineDecodeVertices.Stack) :
    (afterDecode g originalN).stk (.inl k) =
      (SourceNormalizationMachineDecodeVertices.finalHost g originalN).stk k := by
  change BitMachineStackEmbedding.bank decodeStack _ _ (decodeStack k) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

private theorem afterDecode_extra (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineEndpointWriter.Stack) :
    (afterDecode g originalN).stk (.inr k) = [] := by
  have hk : ¬ ∃ j, decodeStack j = Sum.inr k := by simp [decodeStack]
  change BitMachineStackEmbedding.bank decodeStack
    (start (EncodedGraph.encode g) originalN).stk
    (SourceNormalizationMachineDecodeVertices.finalHost g originalN).stk
    (.inr k) = []
  rw [BitMachineStackEmbedding.bank_outside decodeStack _ _ _ hk]
  rfl

private theorem writer_initial_stacks (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∀ k : SourceNormalizationMachineEndpointWriter.Stack,
      (writerInitial g originalN).stk k =
        (afterDecode g originalN).stk (writerStack k) := by
  intro k
  cases k with
  | inl k =>
      rw [show writerStack (Sum.inl k) = Sum.inr (Sum.inl k) from rfl,
        afterDecode_extra]
      change SourceNormalizationMachineEndpointWriter.idleBank [] k = []
      rw [SourceNormalizationMachineEndpointWriter.idleBank,
        SourceUnaryBinaryCall.initial_bank]
      by_cases h : k = Sum.inr (0 : Fin 2) <;> simp [h]
  | inr k =>
      fin_cases k
      · change (writerInitial g originalN).stk (.inr 0) =
          (afterDecode g originalN).stk
            (.inl (SourceNormalizationMachineDecodeVertices.offsetStack 3))
        rw [afterDecode_at,
          SourceNormalizationMachineDecodeVertices.final_stream g hg originalN]
        change SourceNormalizationMachineEndpointWriter.unaryEdges
          (numeric g originalN).edges =
          SourceNormalizationMachineMark.endpointStream
            ((numeric g originalN).edges.flatMap fun p => [p.1,p.2])
        exact (SourceNormalizationMachineEndpointWriter.unaryEdges_eq_endpointStream
          (numeric g originalN).edges)
      all_goals
        change (writerInitial g originalN).stk (.inr _) =
          (afterDecode g originalN).stk (.inr (.inr _))
        rw [afterDecode_extra]
        rfl

private theorem writer_initial (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    afterDecode g originalN =
      BitMachineStackEmbedding.cfg writerStack (afterDecode g originalN).stk
        Sum.inr writerControl none (writerInitial g originalN) := by
  have hb := BitMachineStackEmbedding.bank_eq_self writerStack
    (afterDecode g originalN).stk (writerInitial g originalN).stk
    (writer_initial_stacks g hg originalN)
  change (⟨some (.inr (.inl SourceNormalizationMachineEndpointWriter.Admin.read)),
    (afterDecodeControl,
      (none,(SourceNormalizationMachineEndpointWriter.counter.initial,none))),
    (afterDecode g originalN).stk⟩ : Config) =
    ⟨some (.inr (.inl SourceNormalizationMachineEndpointWriter.Admin.read)),
      (afterDecodeControl,
        (none,(SourceNormalizationMachineEndpointWriter.counter.initial,none))),
      BitMachineStackEmbedding.bank writerStack (afterDecode g originalN).stk
        (writerInitial g originalN).stk⟩
  rw [hb]

noncomputable def finalHost (g : EncodedGraph.Graph) (originalN : ℕ) : Config :=
  BitMachineStackEmbedding.cfg writerStack (afterDecode g originalN).stk
    Sum.inr writerControl none
    (SourceNormalizationMachineEndpointWriter.cfg none
      (none,(SourceNormalizationMachineEndpointWriter.counter.initial,none))
      (SourceNormalizationMachineEndpointWriter.idleBank []) []
      (EncodedGraph.edgeFields (numeric g originalN).edges).reverse
      (List.replicate (numeric g originalN).edges.length true) [])

theorem decode_write_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecodeDouble.rankBound g originalN +
      2 * (g.edges.length + 1) + 2 +
      SourceNormalizationMachineDecodeShift.shiftCost g originalN +
      2 * (SourceNormalizationMachineDecodeVertices.localBits g).length + 2 +
      SourceNormalizationMachineEndpointWriter.edgesCost
        (numeric g originalN).edges + 1,
      run t (start (EncodedGraph.encode g) originalN) =
        finalHost g originalN := by
  obtain ⟨a,ha,hdecode⟩ := decode_stage g hg originalN
  obtain ⟨w,hw,hwriter⟩ :=
    SourceNormalizationMachineEndpointWriter.writer_run
      (numeric g originalN).edges
  have hwriter' : SourceNormalizationMachineEndpointWriter.run w
      (writerInitial g originalN) =
    SourceNormalizationMachineEndpointWriter.cfg none
      (none,(SourceNormalizationMachineEndpointWriter.counter.initial,none))
      (SourceNormalizationMachineEndpointWriter.idleBank []) []
      (EncodedGraph.edgeFields (numeric g originalN).edges).reverse
      (List.replicate (numeric g originalN).edges.length true) [] := by
    simpa only [writerInitial] using hwriter
  obtain ⟨b,hb,hr⟩ := BitMachineStackEmbedding.outputs writerStack
    (afterDecode g originalN).stk Sum.inr writerControl Prod.snd
    (by intro v; rfl) none
    SourceNormalizationMachineEndpointWriter.program program writer_program_eq
    (writerInitial g originalN) w (by
      change (SourceNormalizationMachineEndpointWriter.run w
        (writerInitial g originalN)).l = none
      rw [hwriter']
      rfl)
  change ((advance SourceNormalizationMachineEndpointWriter.program)^[w]) _ = _ at hwriter'
  rw [hwriter'] at hr
  refine ⟨a + b, by omega, ?_⟩
  exact (run_add hdecode b).trans
    ((congrArg (run b) (writer_initial g hg originalN)).trans
      (by simpa only [run, finalHost] using hr))

theorem final_reverse_payload (g : EncodedGraph.Graph) (originalN : ℕ) :
    (finalHost g originalN).stk (writerStack (.inr 1)) =
      (EncodedGraph.edgeFields (numeric g originalN).edges).reverse := by
  change BitMachineStackEmbedding.bank writerStack _ _ (writerStack (.inr 1)) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem final_edge_count (g : EncodedGraph.Graph) (originalN : ℕ) :
    (finalHost g originalN).stk (writerStack (.inr 2)) =
      List.replicate (numeric g originalN).edges.length true := by
  change BitMachineStackEmbedding.bank writerStack _ _ (writerStack (.inr 2)) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem final_vertex_count (g : EncodedGraph.Graph) (originalN : ℕ) :
    (finalHost g originalN).stk
      (.inl (SourceNormalizationMachineDecodeVertices.offsetStack 2)) =
      List.replicate (numeric g originalN).vertices true := by
  have hk : ¬ ∃ k : SourceNormalizationMachineEndpointWriter.Stack,
      writerStack k =
        (.inl (SourceNormalizationMachineDecodeVertices.offsetStack 2) : Stack) := by
    rintro ⟨k,hk⟩
    cases k with
    | inl k => cases hk
    | inr k => fin_cases k <;> simp [writerStack,
        SourceNormalizationMachineDecodeVertices.offsetStack,
        SourceNormalizationMachineDecodeShift.shiftStack] at hk
  change BitMachineStackEmbedding.bank writerStack
    (afterDecode g originalN).stk _
    (.inl (SourceNormalizationMachineDecodeVertices.offsetStack 2)) = _
  rw [BitMachineStackEmbedding.bank_outside writerStack _ _ _ hk,
    afterDecode_at,
    SourceNormalizationMachineDecodeVertices.final_vertices]
  rfl

end EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeWrite
