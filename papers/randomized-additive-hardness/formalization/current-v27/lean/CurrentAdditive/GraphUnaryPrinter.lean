import EthInapproximability.CurrentPaper.SourceNormalizationMachineEndpointWriter
import EthInapproximability.CurrentPaper.SourceClauseMachine

/-!
Selected v39 `appendices/sources.tex:69-78`: serialization needed by labelled
graph copies. This fixed finite program takes unary vertex and endpoint banks,
computes the edge-count header itself, and prints the complete canonical word.
No final header or binary endpoint fields are supplied as input.
-/

namespace Paper2.CurrentAdditive.GraphUnaryPrinter

open EthInapproximability.CurrentPaper Turing BitMachineEncoding

open EthInapproximability.CurrentPaper
noncomputable abbrev counter := SourceUnaryBinaryCall.counter
abbrev Stack := SourceNormalizationMachineEndpointWriter.Stack ⊕ (BitMachineIteration.Stack counter ⊕ Fin 3)
abbrev Label := SourceNormalizationMachineEndpointWriter.Label ⊕ (BitMachineIteration.Label counter ⊕ SourceClauseMachine.Label)
abbrev Control := SourceNormalizationMachineEndpointWriter.Control × (BitMachineIteration.Control counter × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def writerStack : SourceNormalizationMachineEndpointWriter.Stack ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩

noncomputable def converterStack : BitMachineIteration.Stack counter ↪ Stack where
  toFun k := if k = .inr (0 : Fin 2) then .inl (.inr 2) else .inr (.inl k)
  inj' := by
    intro a b h
    by_cases ha : a = .inr (0 : Fin 2)
    · subst a
      by_cases hb : b = .inr (0 : Fin 2)
      · subst b; rfl
      · simp [hb] at h
    · by_cases hb : b = .inr (0 : Fin 2)
      · subst b; simp [ha] at h
      · simpa [ha, hb] using h

noncomputable def finalizerStack : SourceClauseMachine.Stack ↪ Stack where
  toFun k := match k.val with
    | 0 => .inr (.inr 0)
    | 1 => .inr (.inl (.inl counter.input))
    | 2 => .inl (.inr 1)
    | 3 => .inr (.inr 1)
    | _ => .inr (.inr 2)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

noncomputable def afterWriterControl : SourceNormalizationMachineEndpointWriter.Control := (none, (counter.initial, none))
noncomputable def writerControl (v : SourceNormalizationMachineEndpointWriter.Control) : Control :=
  (v, ((counter.initial, none), none))
noncomputable def converterControl (v : BitMachineIteration.Control counter) : Control :=
  (afterWriterControl, (v, none))
noncomputable def finalizerControl (v : Option Bool) : Control :=
  (afterWriterControl, ((counter.initial, none), v))

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt writerStack Sum.inl writerControl Prod.fst
      (some (.inr (.inl (.inr .testFuel)))) (SourceNormalizationMachineEndpointWriter.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt converterStack (fun l => .inr (.inl l))
      converterControl (fun v => v.2.1) (some (.inr (.inr .payload)))
      (BitMachineIteration.program counter l)
  | .inr (.inr l) => BitMachineStackEmbedding.stmt finalizerStack (fun l => .inr (.inr l))
      finalizerControl (fun v => v.2.2) none (SourceClauseMachine.program l)

noncomputable def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

noncomputable def start (g : EncodedGraph.Graph) : Config :=
  ⟨some (.inl (.inl .read)), writerControl afterWriterControl,
    Sum.elim (SourceNormalizationMachineEndpointWriter.start (SourceNormalizationMachineEndpointWriter.unaryEdges g.edges)).stk
      (Sum.elim (fun _ => []) ![List.replicate g.vertices true, [], []])⟩

def streamStack : Stack := .inl (.inr 0)
def vertexStack : Stack := .inr (.inr 0)

theorem start_stacks (g : EncodedGraph.Graph) (k : Stack) :
    (start g).stk k =
      if k = streamStack then SourceNormalizationMachineEndpointWriter.unaryEdges g.edges
      else if k = vertexStack then List.replicate g.vertices true else [] := by
  cases k with
  | inl k =>
      cases k with
      | inl k =>
          simp [start, streamStack, vertexStack,
            SourceNormalizationMachineEndpointWriter.start,
            SourceNormalizationMachineEndpointWriter.cfg,
            SourceNormalizationMachineEndpointWriter.idleBank,
            SourceUnaryBinaryCall.initial_bank]
      | inr k => fin_cases k <;> rfl
  | inr k =>
      cases k with
      | inl k => simp [start, streamStack, vertexStack]
      | inr k => fin_cases k <;> rfl

noncomputable def writerFinal (g : EncodedGraph.Graph) : SourceNormalizationMachineEndpointWriter.Config :=
  SourceNormalizationMachineEndpointWriter.cfg none afterWriterControl (SourceNormalizationMachineEndpointWriter.idleBank []) []
    (EncodedGraph.edgeFields g.edges).reverse
    (List.replicate g.edges.length true) []

noncomputable def afterWrite (g : EncodedGraph.Graph) : Config :=
  BitMachineStackEmbedding.cfg writerStack (start g).stk Sum.inl writerControl
    (some (.inr (.inl (.inr .testFuel)))) (writerFinal g)

private theorem start_embedding (g : EncodedGraph.Graph) :
    BitMachineStackEmbedding.cfg writerStack (start g).stk Sum.inl writerControl
      (some (.inr (.inl (.inr .testFuel))))
      (SourceNormalizationMachineEndpointWriter.start (SourceNormalizationMachineEndpointWriter.unaryEdges g.edges)) = start g := by
  have hb := BitMachineStackEmbedding.bank_eq_self writerStack (start g).stk
    (SourceNormalizationMachineEndpointWriter.start (SourceNormalizationMachineEndpointWriter.unaryEdges g.edges)).stk (by intro k; rfl)
  change (⟨some (.inl (.inl .read)), writerControl afterWriterControl,
    BitMachineStackEmbedding.bank writerStack (start g).stk
      (SourceNormalizationMachineEndpointWriter.start
        (SourceNormalizationMachineEndpointWriter.unaryEdges g.edges)).stk⟩ : Config) = _
  rw [hb]
  rfl

theorem writer_stage (g : EncodedGraph.Graph) :
    ∃ t ≤ SourceNormalizationMachineEndpointWriter.edgesCost g.edges + 1, run t (start g) = afterWrite g := by
  obtain ⟨a, ha, hr⟩ := SourceNormalizationMachineEndpointWriter.writer_run g.edges
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs writerStack (start g).stk Sum.inl
    writerControl Prod.fst (by intro v; rfl)
    (some (.inr (.inl (.inr .testFuel)))) SourceNormalizationMachineEndpointWriter.program program (by intro l; rfl)
    (SourceNormalizationMachineEndpointWriter.start (SourceNormalizationMachineEndpointWriter.unaryEdges g.edges)) a (by
      change (SourceNormalizationMachineEndpointWriter.run a _).l = none
      rw [hr]; rfl)
  change ((advance SourceNormalizationMachineEndpointWriter.program)^[a]) _ = _ at hr
  rw [hr] at he
  exact ⟨t, ht.trans ha, (start_embedding g).symm ▸ he⟩

@[simp] theorem afterWrite_at (g : EncodedGraph.Graph) (k : SourceNormalizationMachineEndpointWriter.Stack) :
    (afterWrite g).stk (.inl k) = (writerFinal g).stk k :=
  BitMachineStackEmbedding.bank_at writerStack _ _ k

@[simp] theorem afterWrite_extra (g : EncodedGraph.Graph)
    (k : BitMachineIteration.Stack counter ⊕ Fin 3) :
    (afterWrite g).stk (.inr k) = (start g).stk (.inr k) := by
  apply BitMachineStackEmbedding.bank_outside
  simp [writerStack]

noncomputable def converterInitial (g : EncodedGraph.Graph) : BitMachineIteration.Config counter :=
  BitMachineIteration.ready counter [] (List.replicate g.edges.length true)

private theorem converter_initial (g : EncodedGraph.Graph) :
    afterWrite g = BitMachineStackEmbedding.cfg converterStack (afterWrite g).stk
      (fun l => .inr (.inl l)) converterControl
      (some (.inr (.inr .payload))) (converterInitial g) := by
  have hb := BitMachineStackEmbedding.bank_eq_self converterStack (afterWrite g).stk
    (converterInitial g).stk (by
      intro k
      by_cases hk : k = .inr (0 : Fin 2)
      · subst k
        simp [converterStack, converterInitial, SourceUnaryBinaryCall.initial_bank,
          writerFinal, SourceNormalizationMachineEndpointWriter.cfg]
      · simp [converterStack, hk, converterInitial, SourceUnaryBinaryCall.initial_bank, start])
  change (⟨some (.inr (.inl (.inr .testFuel))),
    converterControl (counter.initial, none), (afterWrite g).stk⟩ : Config) =
    ⟨some (.inr (.inl (.inr .testFuel))), converterControl (counter.initial, none),
      BitMachineStackEmbedding.bank converterStack (afterWrite g).stk
        (converterInitial g).stk⟩
  rw [hb]

noncomputable def afterConvert (g : EncodedGraph.Graph) : Config :=
  BitMachineStackEmbedding.cfg converterStack (afterWrite g).stk
    (fun l => .inr (.inl l)) converterControl
    (some (.inr (.inr .payload))) (BitMachineIteration.finished counter g.edges.length.bits)

theorem converter_stage (g : EncodedGraph.Graph) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient * (g.edges.length + 1)^2,
      run t (afterWrite g) = afterConvert g := by
  obtain ⟨a, ha, hr⟩ := SourceUnaryBinaryCall.raw_run (List.replicate g.edges.length true)
  have hr' : BitMachineIteration.run counter a (converterInitial g) =
      BitMachineIteration.finished counter g.edges.length.bits := by
    simpa only [converterInitial, List.length_replicate] using hr
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs converterStack (afterWrite g).stk
    (fun l => .inr (.inl l)) converterControl (fun v => v.2.1)
    (by intro v; rfl) (some (.inr (.inr .payload)))
    (BitMachineIteration.program counter) program (by intro l; rfl) (converterInitial g) a (by
      change (BitMachineIteration.run counter a _).l = none
      rw [hr']; rfl)
  change ((advance (BitMachineIteration.program counter))^[a]) _ = _ at hr'
  rw [hr'] at he
  refine ⟨t, ?_, (converter_initial g).symm ▸ he⟩
  simpa only [List.length_replicate] using ht.trans ha

private theorem afterConvert_at (g : EncodedGraph.Graph) (k : BitMachineIteration.Stack counter) :
    (afterConvert g).stk (converterStack k) =
      (BitMachineIteration.finished counter g.edges.length.bits).stk k :=
  BitMachineStackEmbedding.bank_at converterStack _ _ k

private theorem afterConvert_outside (g : EncodedGraph.Graph) (j : Stack)
    (hj : ¬ ∃ k, converterStack k = j) :
    (afterConvert g).stk j = (afterWrite g).stk j :=
  BitMachineStackEmbedding.bank_outside converterStack _ _ j hj

def finalizerInitial (g : EncodedGraph.Graph) : SourceClauseMachine.Config :=
  SourceClauseMachine.cfg (some .payload) none (List.replicate g.vertices true)
    g.edges.length.bits (EncodedGraph.edgeFields g.edges).reverse [] []

private theorem finalizer_stacks (g : EncodedGraph.Graph) (k : SourceClauseMachine.Stack) :
    (finalizerInitial g).stk k = (afterConvert g).stk (finalizerStack k) := by
  fin_cases k
  · change (finalizerInitial g).stk 0 = (afterConvert g).stk (finalizerStack 0)
    have hn : ¬ ∃ k, converterStack k = finalizerStack 0 := by
      rintro ⟨k, hk⟩
      by_cases h : k = .inr (0 : Fin 2) <;>
        simp [converterStack, finalizerStack, h] at hk
    rw [afterConvert_outside g _ hn]
    simp [finalizerStack, start, finalizerInitial, SourceClauseMachine.cfg, SourceClauseMachine.contents]
  · change (finalizerInitial g).stk 1 = (afterConvert g).stk (finalizerStack 1)
    have he : finalizerStack 1 = converterStack (.inl counter.input) := by
      simp [finalizerStack, converterStack]
    rw [he, afterConvert_at, SourceUnaryBinaryCall.final_bank]
    simp [finalizerInitial, SourceClauseMachine.cfg, SourceClauseMachine.contents]
  · change (finalizerInitial g).stk 2 = (afterConvert g).stk (finalizerStack 2)
    have hn : ¬ ∃ k, converterStack k = finalizerStack 2 := by
      rintro ⟨k, hk⟩
      by_cases h : k = .inr (0 : Fin 2) <;>
        simp [converterStack, finalizerStack, h] at hk
    rw [afterConvert_outside g _ hn]
    simp [finalizerStack, finalizerInitial, SourceClauseMachine.cfg, SourceClauseMachine.contents, writerFinal, SourceNormalizationMachineEndpointWriter.cfg]
  · change (finalizerInitial g).stk 3 = (afterConvert g).stk (finalizerStack 3)
    have hn : ¬ ∃ k, converterStack k = finalizerStack 3 := by
      rintro ⟨k, hk⟩
      by_cases h : k = .inr (0 : Fin 2) <;>
        simp [converterStack, finalizerStack, h] at hk
    rw [afterConvert_outside g _ hn]
    simp [finalizerStack, start, finalizerInitial, SourceClauseMachine.cfg, SourceClauseMachine.contents]
  · change (finalizerInitial g).stk 4 = (afterConvert g).stk (finalizerStack 4)
    have hn : ¬ ∃ k, converterStack k = finalizerStack 4 := by
      rintro ⟨k, hk⟩
      by_cases h : k = .inr (0 : Fin 2) <;>
        simp [converterStack, finalizerStack, h] at hk
    rw [afterConvert_outside g _ hn]
    simp [finalizerStack, start, finalizerInitial, SourceClauseMachine.cfg, SourceClauseMachine.contents]

private theorem finalizer_initial (g : EncodedGraph.Graph) :
    afterConvert g = BitMachineStackEmbedding.cfg finalizerStack (afterConvert g).stk
      (fun l => .inr (.inr l)) finalizerControl none (finalizerInitial g) := by
  have hb := BitMachineStackEmbedding.bank_eq_self finalizerStack (afterConvert g).stk
    (finalizerInitial g).stk (finalizer_stacks g)
  change (⟨some (.inr (.inr .payload)), finalizerControl none,
    (afterConvert g).stk⟩ : Config) =
    ⟨some (.inr (.inr .payload)), finalizerControl none,
      BitMachineStackEmbedding.bank finalizerStack (afterConvert g).stk
        (finalizerInitial g).stk⟩
  rw [hb]

def finalizerTime (g : EncodedGraph.Graph) : ℕ :=
  (EncodedGraph.edgeFields g.edges).length +
    3 * g.edges.length.bits.length + g.vertices + 5

def finalizerFinal (g : EncodedGraph.Graph) : SourceClauseMachine.Config :=
  SourceClauseMachine.cfg none none [] [] [] [] (EncodedGraph.encode g)

theorem finalizer_local_run (g : EncodedGraph.Graph) :
    SourceClauseMachine.run (finalizerTime g) (finalizerInitial g) = finalizerFinal g := by
  have h := SourceClauseMachine.finalize g.vertices g.edges.length
    (EncodedGraph.edgeFields g.edges).reverse []
  simpa [finalizerTime, finalizerInitial, finalizerFinal,
    EncodedGraph.encode, List.append_assoc] using h

noncomputable def finalHost (g : EncodedGraph.Graph) : Config :=
  BitMachineStackEmbedding.cfg finalizerStack (afterConvert g).stk
    (fun l => .inr (.inr l)) finalizerControl none (finalizerFinal g)

noncomputable def totalBound (g : EncodedGraph.Graph) : ℕ :=
  SourceNormalizationMachineEndpointWriter.edgesCost g.edges + 1 +
    UnaryBinaryEncoding.coefficient * (g.edges.length + 1)^2 + finalizerTime g

/-- An actual finite program, for every graph including the empty graph.
Its only input is a unary vertex bank and the unary ordered endpoint stream. -/
theorem printer_run (g : EncodedGraph.Graph) :
    ∃ t ≤ totalBound g, run t (start g) = finalHost g := by
  obtain ⟨a, ha, hw⟩ := writer_stage g
  obtain ⟨b, hb, hc⟩ := converter_stage g
  have hbefore := (run_add hw b).trans hc
  have hlocal := finalizer_local_run g
  obtain ⟨c, hcb, hr⟩ := BitMachineStackEmbedding.outputs finalizerStack (afterConvert g).stk
    (fun l => .inr (.inr l)) finalizerControl (fun v => v.2.2)
    (by intro v; rfl) none SourceClauseMachine.program program (by intro l; rfl)
    (finalizerInitial g) (finalizerTime g) (by
      change (SourceClauseMachine.run _ _).l = none
      rw [hlocal]; rfl)
  change ((advance SourceClauseMachine.program)^[finalizerTime g]) _ = _ at hlocal
  rw [hlocal] at hr
  refine ⟨a + b + c, by unfold totalBound; omega, ?_⟩
  exact (run_add hbefore c).trans
    ((congrArg (run c) (finalizer_initial g)).trans hr)

theorem final_output (g : EncodedGraph.Graph) :
    (finalHost g).stk (finalizerStack 4) = EncodedGraph.encode g := by
  change BitMachineStackEmbedding.bank finalizerStack _ _ (finalizerStack 4) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem final_halts (g : EncodedGraph.Graph) : (finalHost g).l = none := rfl

#print axioms printer_run
#print axioms final_output

end Paper2.CurrentAdditive.GraphUnaryPrinter
