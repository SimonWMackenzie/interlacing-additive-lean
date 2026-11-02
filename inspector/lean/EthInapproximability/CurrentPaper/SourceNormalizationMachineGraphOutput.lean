import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeWrite
import EthInapproximability.CurrentPaper.SourceClauseMachine
import EthInapproximability.CurrentPaper.SourceUnaryBinaryCall

/-! Physical edge-count conversion and canonical graph-header serialization. -/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineGraphOutput

open Turing BitMachineEncoding

noncomputable abbrev counter := SourceUnaryBinaryCall.counter

abbrev Stack := SourceNormalizationMachineDecodeWrite.Stack ⊕
  (BitMachineIteration.Stack counter ⊕ Fin 2)
abbrev Label := SourceNormalizationMachineDecodeWrite.Label ⊕
  (BitMachineIteration.Label counter ⊕ SourceClauseMachine.Label)
abbrev Control := SourceNormalizationMachineDecodeWrite.Control ×
  (BitMachineIteration.Control counter × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def decodeStack : SourceNormalizationMachineDecodeWrite.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

noncomputable def converterStack : BitMachineIteration.Stack counter ↪ Stack where
  toFun k := if k = .inr (0 : Fin 2) then
      .inl (SourceNormalizationMachineDecodeWrite.writerStack (.inr 2))
    else .inr (.inl k)
  inj' := by
    intro a b h
    by_cases ha : a = .inr (0 : Fin 2)
    · subst a
      by_cases hb : b = .inr (0 : Fin 2)
      · subst b; rfl
      · simp [hb] at h
    · by_cases hb : b = .inr (0 : Fin 2)
      · subst b; simp [ha] at h
      · simpa [ha,hb] using h

noncomputable def finalizerStack : SourceClauseMachine.Stack ↪ Stack where
  toFun k := match k.val with
    | 0 => .inl (.inl (SourceNormalizationMachineDecodeVertices.offsetStack 2))
    | 1 => .inr (.inl (.inl counter.input))
    | 2 => .inl (SourceNormalizationMachineDecodeWrite.writerStack (.inr 1))
    | 3 => .inr (.inr 0)
    | _ => .inr (.inr 1)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [
      SourceNormalizationMachineDecodeWrite.writerStack]

noncomputable def afterWriteControl : SourceNormalizationMachineDecodeWrite.Control :=
  (SourceNormalizationMachineDecodeWrite.afterDecodeControl,
    (none,(counter.initial,none)))

noncomputable def decodeControl (v : SourceNormalizationMachineDecodeWrite.Control) : Control :=
  (v,((counter.initial,none),none))

noncomputable def converterControl (v : BitMachineIteration.Control counter) : Control :=
  (afterWriteControl,(v,none))

noncomputable def finalizerControl (v : Option Bool) : Control :=
  (afterWriteControl,((counter.initial,none),v))

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt decodeStack Sum.inl
      decodeControl Prod.fst (some (.inr (.inl (.inr .testFuel))))
      (SourceNormalizationMachineDecodeWrite.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt converterStack
      (fun l => .inr (.inl l)) converterControl
      (fun v => v.2.1) (some (.inr (.inr .payload)))
      (BitMachineIteration.program counter l)
  | .inr (.inr l) => BitMachineStackEmbedding.stmt finalizerStack
      (fun l => .inr (.inr l)) finalizerControl
      (fun v => v.2.2) none (SourceClauseMachine.program l)

noncomputable def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

noncomputable def start (graphBits : List Bool) (originalN : ℕ) : Config :=
  ⟨(SourceNormalizationMachineDecodeWrite.start graphBits originalN).l.map Sum.inl,
    decodeControl (SourceNormalizationMachineDecodeWrite.start graphBits originalN).var,
    Sum.elim (SourceNormalizationMachineDecodeWrite.start graphBits originalN).stk
      (fun _ => [])⟩

noncomputable def afterWrite (g : EncodedGraph.Graph) (originalN : ℕ) : Config :=
  BitMachineStackEmbedding.cfg decodeStack
    (start (EncodedGraph.encode g) originalN).stk Sum.inl decodeControl
    (some (.inr (.inl (.inr .testFuel))))
    (SourceNormalizationMachineDecodeWrite.finalHost g originalN)

private theorem decode_program_eq (l : SourceNormalizationMachineDecodeWrite.Label) :
    program (.inl l) = BitMachineStackEmbedding.stmt decodeStack Sum.inl
      decodeControl Prod.fst (some (.inr (.inl (.inr .testFuel))))
      (SourceNormalizationMachineDecodeWrite.program l) := rfl

private theorem converter_program_eq (l : BitMachineIteration.Label counter) :
    program (.inr (.inl l)) = BitMachineStackEmbedding.stmt converterStack
      (fun l => .inr (.inl l)) converterControl
      (fun v => v.2.1) (some (.inr (.inr .payload)))
      (BitMachineIteration.program counter l) := rfl

private theorem finalizer_program_eq (l : SourceClauseMachine.Label) :
    program (.inr (.inr l)) = BitMachineStackEmbedding.stmt finalizerStack
      (fun l => .inr (.inr l)) finalizerControl
      (fun v => v.2.2) none (SourceClauseMachine.program l) := rfl

private theorem decode_initial (graphBits : List Bool) (originalN : ℕ) :
    BitMachineStackEmbedding.cfg decodeStack (start graphBits originalN).stk
      Sum.inl decodeControl (some (.inr (.inl (.inr .testFuel))))
      (SourceNormalizationMachineDecodeWrite.start graphBits originalN) =
    start graphBits originalN := by
  have hb := BitMachineStackEmbedding.bank_eq_self decodeStack
    (start graphBits originalN).stk
    (SourceNormalizationMachineDecodeWrite.start graphBits originalN).stk
    (by intro k; rfl)
  change (⟨_,_, BitMachineStackEmbedding.bank decodeStack
    (start graphBits originalN).stk
    (SourceNormalizationMachineDecodeWrite.start graphBits originalN).stk⟩ :
    Config) = _
  rw [hb]
  rfl

theorem decode_stage (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecodeDouble.rankBound g originalN +
      2 * (g.edges.length + 1) + 2 +
      SourceNormalizationMachineDecodeShift.shiftCost g originalN +
      2 * (SourceNormalizationMachineDecodeVertices.localBits g).length + 2 +
      SourceNormalizationMachineEndpointWriter.edgesCost
        (SourceNormalizationMachineDecodeWrite.numeric g originalN).edges + 1,
      run t (start (EncodedGraph.encode g) originalN) =
        afterWrite g originalN := by
  obtain ⟨a,ha,hr⟩ :=
    SourceNormalizationMachineDecodeWrite.decode_write_run g hg originalN
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs decodeStack
    (start (EncodedGraph.encode g) originalN).stk Sum.inl
    decodeControl Prod.fst (by intro v; rfl)
    (some (.inr (.inl (.inr .testFuel))))
    SourceNormalizationMachineDecodeWrite.program program decode_program_eq
    (SourceNormalizationMachineDecodeWrite.start
      (EncodedGraph.encode g) originalN) a (by
      change (SourceNormalizationMachineDecodeWrite.run a
        (SourceNormalizationMachineDecodeWrite.start
          (EncodedGraph.encode g) originalN)).l = none
      rw [hr]
      rfl)
  change ((advance SourceNormalizationMachineDecodeWrite.program)^[a]) _ = _ at hr
  rw [hr] at he
  exact ⟨t, ht.trans ha, (decode_initial (EncodedGraph.encode g) originalN).symm ▸ he⟩

def numeric (g : EncodedGraph.Graph) (originalN : ℕ) : EncodedGraph.Graph :=
  SourceNormalizationMachineDecodeWrite.numeric g originalN

noncomputable def converterInitial (g : EncodedGraph.Graph) (originalN : ℕ) :
    BitMachineIteration.Config counter :=
  BitMachineIteration.ready counter []
    (List.replicate (numeric g originalN).edges.length true)

private theorem afterWrite_at (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineDecodeWrite.Stack) :
    (afterWrite g originalN).stk (.inl k) =
      (SourceNormalizationMachineDecodeWrite.finalHost g originalN).stk k := by
  change BitMachineStackEmbedding.bank decodeStack _ _ (decodeStack k) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

private theorem afterWrite_extra (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : BitMachineIteration.Stack counter ⊕ Fin 2) :
    (afterWrite g originalN).stk (.inr k) = [] := by
  have hk : ¬ ∃ j, decodeStack j = Sum.inr k := by simp [decodeStack]
  change BitMachineStackEmbedding.bank decodeStack
    (start (EncodedGraph.encode g) originalN).stk
    (SourceNormalizationMachineDecodeWrite.finalHost g originalN).stk
    (.inr k) = []
  rw [BitMachineStackEmbedding.bank_outside decodeStack _ _ _ hk]
  rfl

private theorem converter_initial_stacks (g : EncodedGraph.Graph)
    (originalN : ℕ) :
    ∀ k : BitMachineIteration.Stack counter,
      (converterInitial g originalN).stk k =
        (afterWrite g originalN).stk (converterStack k) := by
  intro k
  by_cases hk : k = .inr (0 : Fin 2)
  · subst k
    change (converterInitial g originalN).stk (.inr 0) =
      (afterWrite g originalN).stk
        (.inl (SourceNormalizationMachineDecodeWrite.writerStack (.inr 2)))
    rw [afterWrite_at,
      SourceNormalizationMachineDecodeWrite.final_edge_count]
    rfl
  · have he : converterStack k = .inr (.inl k) := by simp [converterStack,hk]
    rw [he, afterWrite_extra]
    rw [converterInitial, SourceUnaryBinaryCall.initial_bank]
    simp [hk]

private theorem converter_initial (g : EncodedGraph.Graph) (originalN : ℕ) :
    afterWrite g originalN =
      BitMachineStackEmbedding.cfg converterStack (afterWrite g originalN).stk
        (fun l => .inr (.inl l)) converterControl
        (some (.inr (.inr .payload))) (converterInitial g originalN) := by
  have hb := BitMachineStackEmbedding.bank_eq_self converterStack
    (afterWrite g originalN).stk (converterInitial g originalN).stk
    (converter_initial_stacks g originalN)
  change (⟨some (.inr (.inl (.inr BitMachineIteration.Admin.testFuel))),
    (afterWriteControl,((counter.initial,none),none)),
    (afterWrite g originalN).stk⟩ : Config) =
    ⟨some (.inr (.inl (.inr BitMachineIteration.Admin.testFuel))),
      (afterWriteControl,((counter.initial,none),none)),
      BitMachineStackEmbedding.bank converterStack (afterWrite g originalN).stk
        (converterInitial g originalN).stk⟩
  rw [hb]

noncomputable def afterConvert (g : EncodedGraph.Graph) (originalN : ℕ) : Config :=
  BitMachineStackEmbedding.cfg converterStack (afterWrite g originalN).stk
    (fun l => .inr (.inl l)) converterControl
    (some (.inr (.inr .payload)))
    (BitMachineIteration.finished counter (numeric g originalN).edges.length.bits)

theorem converter_stage (g : EncodedGraph.Graph) (originalN : ℕ) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient *
      ((numeric g originalN).edges.length + 1) ^ 2,
      run t (afterWrite g originalN) = afterConvert g originalN := by
  let input := List.replicate (numeric g originalN).edges.length true
  obtain ⟨a,ha,hr⟩ := SourceUnaryBinaryCall.raw_run input
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs converterStack
    (afterWrite g originalN).stk (fun l => .inr (.inl l))
    converterControl (fun v => v.2.1) (by intro v; rfl)
    (some (.inr (.inr .payload)))
    (BitMachineIteration.program counter) program converter_program_eq
    (converterInitial g originalN) a (by
      change (BitMachineIteration.run counter a (converterInitial g originalN)).l = none
      simpa only [converterInitial, input, List.length_replicate] using
        congrArg TM2.Cfg.l hr)
  have hr' : BitMachineIteration.run counter a (converterInitial g originalN) =
      BitMachineIteration.finished counter (numeric g originalN).edges.length.bits := by
    simpa only [converterInitial, input, List.length_replicate] using hr
  change ((advance (BitMachineIteration.program counter))^[a]) _ = _ at hr'
  rw [hr'] at he
  refine ⟨t, ?_, ?_⟩
  · simpa only [input, List.length_replicate] using ht.trans ha
  · exact (converter_initial g originalN).symm ▸ he

private theorem afterConvert_at (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : BitMachineIteration.Stack counter) :
    (afterConvert g originalN).stk (converterStack k) =
      (BitMachineIteration.finished counter
        (numeric g originalN).edges.length.bits).stk k := by
  change BitMachineStackEmbedding.bank converterStack _ _ (converterStack k) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

private theorem afterConvert_outside (g : EncodedGraph.Graph) (originalN : ℕ)
    (j : Stack) (hj : ¬ ∃ k, converterStack k = j) :
    (afterConvert g originalN).stk j = (afterWrite g originalN).stk j := by
  change BitMachineStackEmbedding.bank converterStack
    (afterWrite g originalN).stk _ j = _
  rw [BitMachineStackEmbedding.bank_outside converterStack _ _ j hj]

private theorem afterConvert_vertex (g : EncodedGraph.Graph) (originalN : ℕ) :
    (afterConvert g originalN).stk (finalizerStack 0) =
      List.replicate (numeric g originalN).vertices true := by
  have hk : ¬ ∃ k, converterStack k = finalizerStack 0 := by
    rintro ⟨k,hk⟩
    by_cases h : k = .inr (0 : Fin 2)
    · subst k
      simp [converterStack, finalizerStack,
        SourceNormalizationMachineDecodeWrite.writerStack,
        SourceNormalizationMachineDecodeVertices.offsetStack,
        SourceNormalizationMachineDecodeShift.shiftStack] at hk
    · simp [converterStack, h, finalizerStack] at hk
  rw [afterConvert_outside g originalN _ hk]
  change (afterWrite g originalN).stk
    (.inl (.inl (SourceNormalizationMachineDecodeVertices.offsetStack 2))) = _
  rw [afterWrite_at,
    SourceNormalizationMachineDecodeWrite.final_vertex_count]
  rfl

private theorem afterConvert_count (g : EncodedGraph.Graph) (originalN : ℕ) :
    (afterConvert g originalN).stk (finalizerStack 1) =
      (numeric g originalN).edges.length.bits := by
  have he : finalizerStack 1 = converterStack (.inl counter.input) := by
    simp [finalizerStack, converterStack]
  rw [he, afterConvert_at]
  rw [SourceUnaryBinaryCall.final_bank]
  simp

private theorem afterConvert_payload (g : EncodedGraph.Graph) (originalN : ℕ) :
    (afterConvert g originalN).stk (finalizerStack 2) =
      (EncodedGraph.edgeFields (numeric g originalN).edges).reverse := by
  have hk : ¬ ∃ k, converterStack k = finalizerStack 2 := by
    rintro ⟨k,hk⟩
    by_cases h : k = .inr (0 : Fin 2)
    · subst k
      simp [converterStack, finalizerStack,
        SourceNormalizationMachineDecodeWrite.writerStack] at hk
    · simp [converterStack, h, finalizerStack] at hk
  rw [afterConvert_outside g originalN _ hk]
  change (afterWrite g originalN).stk
    (.inl (SourceNormalizationMachineDecodeWrite.writerStack (.inr 1))) = _
  rw [afterWrite_at,
    SourceNormalizationMachineDecodeWrite.final_reverse_payload]
  rfl

private theorem afterConvert_scratch (g : EncodedGraph.Graph) (originalN : ℕ) :
    (afterConvert g originalN).stk (finalizerStack 3) = [] := by
  have hk : ¬ ∃ k, converterStack k = finalizerStack 3 := by
    rintro ⟨k,hk⟩
    by_cases h : k = .inr (0 : Fin 2) <;>
      simp [converterStack, finalizerStack, h] at hk
  rw [afterConvert_outside g originalN _ hk]
  change (afterWrite g originalN).stk (.inr (.inr 0)) = []
  rw [afterWrite_extra]

private theorem afterConvert_output (g : EncodedGraph.Graph) (originalN : ℕ) :
    (afterConvert g originalN).stk (finalizerStack 4) = [] := by
  have hk : ¬ ∃ k, converterStack k = finalizerStack 4 := by
    rintro ⟨k,hk⟩
    by_cases h : k = .inr (0 : Fin 2) <;>
      simp [converterStack, finalizerStack, h] at hk
  rw [afterConvert_outside g originalN _ hk]
  change (afterWrite g originalN).stk (.inr (.inr 1)) = []
  rw [afterWrite_extra]

def finalizerInitial (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceClauseMachine.Config :=
  SourceClauseMachine.cfg (some .payload) none
    (List.replicate (numeric g originalN).vertices true)
    (numeric g originalN).edges.length.bits
    (EncodedGraph.edgeFields (numeric g originalN).edges).reverse [] []

private theorem finalizer_initial_stacks (g : EncodedGraph.Graph)
    (originalN : ℕ) :
    ∀ k : SourceClauseMachine.Stack,
      (finalizerInitial g originalN).stk k =
        (afterConvert g originalN).stk (finalizerStack k) := by
  intro k
  fin_cases k
  · exact (afterConvert_vertex g originalN).symm
  · exact (afterConvert_count g originalN).symm
  · exact (afterConvert_payload g originalN).symm
  · exact (afterConvert_scratch g originalN).symm
  · exact (afterConvert_output g originalN).symm

private theorem finalizer_initial (g : EncodedGraph.Graph) (originalN : ℕ) :
    afterConvert g originalN =
      BitMachineStackEmbedding.cfg finalizerStack (afterConvert g originalN).stk
        (fun l => .inr (.inr l)) finalizerControl none
        (finalizerInitial g originalN) := by
  have hb := BitMachineStackEmbedding.bank_eq_self finalizerStack
    (afterConvert g originalN).stk (finalizerInitial g originalN).stk
    (finalizer_initial_stacks g originalN)
  change (⟨some (.inr (.inr SourceClauseMachine.Label.payload)),
    (afterWriteControl,((counter.initial,none),none)),
    (afterConvert g originalN).stk⟩ : Config) =
    ⟨some (.inr (.inr SourceClauseMachine.Label.payload)),
      (afterWriteControl,((counter.initial,none),none)),
      BitMachineStackEmbedding.bank finalizerStack (afterConvert g originalN).stk
        (finalizerInitial g originalN).stk⟩
  rw [hb]

def finalizerTime (g : EncodedGraph.Graph) (originalN : ℕ) : ℕ :=
  (EncodedGraph.edgeFields (numeric g originalN).edges).length +
    3 * (numeric g originalN).edges.length.bits.length +
    (numeric g originalN).vertices + 5

def finalizerFinal (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceClauseMachine.Config :=
  SourceClauseMachine.cfg none none [] [] [] []
    (EncodedGraph.encode (numeric g originalN))

theorem finalizer_local_run (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceClauseMachine.run (finalizerTime g originalN)
      (finalizerInitial g originalN) = finalizerFinal g originalN := by
  have h := SourceClauseMachine.finalize
    (numeric g originalN).vertices (numeric g originalN).edges.length
    (EncodedGraph.edgeFields (numeric g originalN).edges).reverse []
  simpa [finalizerTime, finalizerInitial, finalizerFinal,
    EncodedGraph.encode, List.append_assoc] using h

noncomputable def finalHost (g : EncodedGraph.Graph) (originalN : ℕ) : Config :=
  BitMachineStackEmbedding.cfg finalizerStack (afterConvert g originalN).stk
    (fun l => .inr (.inr l)) finalizerControl none
    (finalizerFinal g originalN)

noncomputable def totalBound (g : EncodedGraph.Graph) (originalN : ℕ) : ℕ :=
  SourceNormalizationMachineDecodeDouble.rankBound g originalN +
    2 * (g.edges.length + 1) + 2 +
    SourceNormalizationMachineDecodeShift.shiftCost g originalN +
    2 * (SourceNormalizationMachineDecodeVertices.localBits g).length + 2 +
    SourceNormalizationMachineEndpointWriter.edgesCost
      (numeric g originalN).edges + 1 +
    UnaryBinaryEncoding.coefficient * ((numeric g originalN).edges.length + 1) ^ 2 +
    finalizerTime g originalN

theorem graph_output_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ totalBound g originalN,
      run t (start (EncodedGraph.encode g) originalN) = finalHost g originalN := by
  obtain ⟨a,ha,hdecode⟩ := decode_stage g hg originalN
  obtain ⟨b,hb,hconvert⟩ := converter_stage g originalN
  have hbefore := (run_add hdecode b).trans hconvert
  have hlocal := finalizer_local_run g originalN
  obtain ⟨c,hc,hr⟩ := BitMachineStackEmbedding.outputs finalizerStack
    (afterConvert g originalN).stk (fun l => .inr (.inr l))
    finalizerControl (fun v => v.2.2) (by intro v; rfl) none
    SourceClauseMachine.program program finalizer_program_eq
    (finalizerInitial g originalN) (finalizerTime g originalN) (by
      change (SourceClauseMachine.run (finalizerTime g originalN)
        (finalizerInitial g originalN)).l = none
      rw [hlocal]
      rfl)
  change ((advance SourceClauseMachine.program)^[finalizerTime g originalN])
    _ = _ at hlocal
  rw [hlocal] at hr
  refine ⟨a + b + c, ?_, ?_⟩
  · unfold totalBound
    change a ≤ SourceNormalizationMachineDecodeDouble.rankBound g originalN +
      2 * (g.edges.length + 1) + 2 +
      SourceNormalizationMachineDecodeShift.shiftCost g originalN +
      2 * (SourceNormalizationMachineDecodeVertices.localBits g).length + 2 +
      SourceNormalizationMachineEndpointWriter.edgesCost
        (numeric g originalN).edges + 1 at ha
    omega
  · exact (run_add hbefore c).trans
      ((congrArg (run c) (finalizer_initial g originalN)).trans
        (by simpa only [run, finalHost] using hr))

theorem final_output (g : EncodedGraph.Graph) (originalN : ℕ) :
    (finalHost g originalN).stk (finalizerStack 4) =
      EncodedGraph.encode (numeric g originalN) := by
  change BitMachineStackEmbedding.bank finalizerStack _ _ (finalizerStack 4) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

end EthInapproximability.CurrentPaper.SourceNormalizationMachineGraphOutput
