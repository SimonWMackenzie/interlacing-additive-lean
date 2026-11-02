import CurrentAdditive.GraphCopyFromUnary
import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecode

/-! Selected v39 sources.tex:69-78. Canonical original graph-code input joins
the computed-counter copy transformer through the actual physical decoder.
This theorem is for valid canonical source graphs, not malformed byte strings. -/

namespace Paper2.CurrentAdditive.GraphCopyEncoded

open EthInapproximability.CurrentPaper Turing BitMachineEncoding
open Paper2.CurrentAdditive.GraphCopyPadding

abbrev Stack := SourceNormalizationMachineDecode.Stack ⊕ (GraphCopyFromUnary.Stack ⊕ Fin 1)
abbrev Label := SourceNormalizationMachineDecode.Label ⊕ GraphCopyFromUnary.Label
abbrev Control := SourceNormalizationMachineDecode.Control × GraphCopyFromUnary.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def decodeStack : SourceNormalizationMachineDecode.Stack ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩

noncomputable def copyStack : GraphCopyFromUnary.Stack ↪ Stack where
  toFun k :=
    if k = GraphCopyFromUnary.originalNStack then .inr (.inr 0)
    else if k = GraphCopyFromUnary.originalMStack then .inl (.inr 1)
    else if k = GraphCopyFromUnary.originalStreamStack then .inl (.inr 4)
    else if k = GraphCopyFromUnary.originalVerticesStack then .inl (.inr 0)
    else .inr (.inl k)
  inj' := by
    intro a b h
    dsimp only at h
    split_ifs at h <;> simp_all [GraphCopyFromUnary.originalNStack,
      GraphCopyFromUnary.originalMStack, GraphCopyFromUnary.originalStreamStack,
      GraphCopyFromUnary.originalVerticesStack, GraphCopyCount.originalNStack,
      GraphCopyCount.payloadStack]

noncomputable def initialCopyControl : GraphCopyFromUnary.Control :=
  GraphCopyFromUnary.countControl (GraphCopyCount.countControl (false, ()))
noncomputable def decodeControl (v : SourceNormalizationMachineDecode.Control) : Control :=
  (v, initialCopyControl)
def copyControl (v : GraphCopyFromUnary.Control) : Control :=
  (SourceNormalizationMachineDecode.doneControl true, v)

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt decodeStack Sum.inl decodeControl Prod.fst
      (some (.inr (.inl (.inr (.inr ()))))) (SourceNormalizationMachineDecode.program l)
  | .inr l => BitMachineStackEmbedding.stmt copyStack Sum.inr copyControl Prod.snd
      none (GraphCopyFromUnary.program l)

noncomputable def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

noncomputable def start (bits : List Bool) (N : ℕ) : Config :=
  ⟨(SourceNormalizationMachineDecode.start bits).l.map Sum.inl,
    decodeControl (SourceNormalizationMachineDecode.start bits).var,
    Sum.elim (SourceNormalizationMachineDecode.start bits).stk
      (Sum.elim (fun _ => []) (fun _ => List.replicate N true))⟩

def decodeFinal (g : EncodedGraph.Graph) : SourceNormalizationMachineDecode.Config :=
  SourceNormalizationMachineDecode.cfg none (SourceNormalizationMachineDecode.doneControl true) {}
    (List.replicate g.vertices true) (List.replicate g.edges.length true) [] []
    (SourceNormalizationMachineDecode.endpointStream g) []

noncomputable def afterDecode (g : EncodedGraph.Graph) (N : ℕ) : Config :=
  BitMachineStackEmbedding.cfg decodeStack (start (EncodedGraph.encode g) N).stk
    Sum.inl decodeControl (some (.inr (.inl (.inr (.inr ()))))) (decodeFinal g)

private theorem decode_initial (bits : List Bool) (N : ℕ) :
    BitMachineStackEmbedding.cfg decodeStack (start bits N).stk
      Sum.inl decodeControl (some (.inr (.inl (.inr (.inr ())))))
      (SourceNormalizationMachineDecode.start bits) = start bits N := by
  have hb := BitMachineStackEmbedding.bank_eq_self decodeStack (start bits N).stk
    (SourceNormalizationMachineDecode.start bits).stk (by intro k; rfl)
  change (⟨some (.inl (.inr .capScan)),
    decodeControl (SourceNormalizationMachineDecode.start bits).var,
    BitMachineStackEmbedding.bank decodeStack (start bits N).stk
      (SourceNormalizationMachineDecode.start bits).stk⟩ : Config) = _
  rw [hb]
  rfl

theorem decode_stage (g : EncodedGraph.Graph) (hg : g.Valid) (N : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecode.graphCost g,
      run t (start (EncodedGraph.encode g) N) = afterDecode g N := by
  obtain ⟨a, ha, hr⟩ := SourceNormalizationMachineDecode.decode_valid_run g hg
  have hr' : SourceNormalizationMachineDecode.run a
      (SourceNormalizationMachineDecode.start (EncodedGraph.encode g)) = decodeFinal g := hr
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs decodeStack
    (start (EncodedGraph.encode g) N).stk Sum.inl decodeControl Prod.fst
    (by intro v; rfl) (some (.inr (.inl (.inr (.inr ())))))
    SourceNormalizationMachineDecode.program program (by intro l; rfl)
    (SourceNormalizationMachineDecode.start (EncodedGraph.encode g)) a (by
      change (SourceNormalizationMachineDecode.run a _).l = none
      rw [hr']; rfl)
  change ((advance SourceNormalizationMachineDecode.program)^[a]) _ = _ at hr'
  rw [hr'] at he
  exact ⟨t, ht.trans ha, (decode_initial (EncodedGraph.encode g) N).symm ▸ he⟩

@[simp] theorem afterDecode_at (g : EncodedGraph.Graph) (N : ℕ)
    (k : SourceNormalizationMachineDecode.Stack) :
    (afterDecode g N).stk (.inl k) = (decodeFinal g).stk k :=
  BitMachineStackEmbedding.bank_at decodeStack _ _ k

@[simp] theorem afterDecode_extra (g : EncodedGraph.Graph) (N : ℕ)
    (k : GraphCopyFromUnary.Stack ⊕ Fin 1) :
    (afterDecode g N).stk (.inr k) = (start (EncodedGraph.encode g) N).stk (.inr k) :=
  BitMachineStackEmbedding.bank_outside decodeStack _ _ _ (by simp [decodeStack])

private theorem original_stream (g : EncodedGraph.Graph) :
    SourceNormalizationMachineDecode.endpointStream g = GraphRepeatPrinter.originalStream g := by
  rw [SourceNormalizationMachineDecode.endpointStream_eq_mark]
  exact (Paper2.CurrentAdditive.GraphCopyMachineStages.unaryEdges_eq_endpointList g).symm

private theorem copy_stacks (g : EncodedGraph.Graph) (N : ℕ)
    (k : GraphCopyFromUnary.Stack) :
    (GraphCopyFromUnary.start g N).stk k = (afterDecode g N).stk (copyStack k) := by
  rw [GraphCopyFromUnary.start_stacks]
  by_cases hn : k = GraphCopyFromUnary.originalNStack
  · subst k
    change List.replicate N true = (afterDecode g N).stk (.inr (.inr 0))
    rw [afterDecode_extra]
    rfl
  · by_cases hm : k = GraphCopyFromUnary.originalMStack
    · subst k
      change List.replicate g.edges.length true = (afterDecode g N).stk (.inl (.inr 1))
      rw [afterDecode_at]
      rfl
    · by_cases hp : k = GraphCopyFromUnary.originalStreamStack
      · subst k
        change GraphRepeatPrinter.originalStream g = (afterDecode g N).stk (.inl (.inr 4))
        rw [afterDecode_at]
        exact (original_stream g).symm
      · by_cases hv : k = GraphCopyFromUnary.originalVerticesStack
        · subst k
          change List.replicate g.vertices true = (afterDecode g N).stk (.inl (.inr 0))
          rw [afterDecode_at]
          rfl
        · simp only [hn, hm, hp, hv, ↓reduceIte]
          have hk : copyStack k = Sum.inr (Sum.inl k) := by
            change (if k = GraphCopyFromUnary.originalNStack then Sum.inr (Sum.inr 0)
              else if k = GraphCopyFromUnary.originalMStack then Sum.inl (Sum.inr 1)
              else if k = GraphCopyFromUnary.originalStreamStack then Sum.inl (Sum.inr 4)
              else if k = GraphCopyFromUnary.originalVerticesStack then Sum.inl (Sum.inr 0)
              else Sum.inr (Sum.inl k)) = _
            simp only [hn, hm, hp, hv, ↓reduceIte]
          rw [hk, afterDecode_extra]
          rfl

private theorem copy_initial (g : EncodedGraph.Graph) (N : ℕ) :
    afterDecode g N = BitMachineStackEmbedding.cfg copyStack (afterDecode g N).stk
      Sum.inr copyControl none (GraphCopyFromUnary.start g N) := by
  have hb := BitMachineStackEmbedding.bank_eq_self copyStack (afterDecode g N).stk
    (GraphCopyFromUnary.start g N).stk (copy_stacks g N)
  change (⟨some (.inr (.inl (.inr (.inr ())))), copyControl initialCopyControl,
    (afterDecode g N).stk⟩ : Config) =
    ⟨some (.inr (.inl (.inr (.inr ())))), copyControl initialCopyControl,
      BitMachineStackEmbedding.bank copyStack (afterDecode g N).stk (GraphCopyFromUnary.start g N).stk⟩
  rw [hb]

noncomputable def finalHost (g : EncodedGraph.Graph) (N : ℕ) : Config :=
  BitMachineStackEmbedding.cfg copyStack (afterDecode g N).stk Sum.inr copyControl none
    (GraphCopyFromUnary.finalHost g N)

noncomputable def totalBound (g : EncodedGraph.Graph) (N : ℕ) : ℕ :=
  SourceNormalizationMachineDecode.graphCost g + GraphCopyFromUnary.totalBound g N

/-- The same fixed physical program for every N and valid nonempty original
graph g. Its only input data are the ORIGINAL canonical graph code and unary N. -/
theorem encoded_graph_copy_run (g : EncodedGraph.Graph) (hg : g.Valid) (N : ℕ)
    (hm : 0 < g.edges.length) :
    ∃ t ≤ totalBound g N, run t (start (EncodedGraph.encode g) N) = finalHost g N := by
  obtain ⟨a, ha, hra⟩ := decode_stage g hg N
  obtain ⟨b, hb, hrb⟩ := GraphCopyFromUnary.graph_copy_run g N hm
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs copyStack (afterDecode g N).stk
    Sum.inr copyControl Prod.snd (by intro v; rfl) none GraphCopyFromUnary.program program
    (by intro l; rfl) (GraphCopyFromUnary.start g N) b (by
      change (GraphCopyFromUnary.run b _).l = none
      rw [hrb]; rfl)
  change ((advance GraphCopyFromUnary.program)^[b]) _ = _ at hrb
  rw [hrb] at he
  refine ⟨a + t, by unfold totalBound; omega, ?_⟩
  exact (run_add hra t).trans ((congrArg (run t) (copy_initial g N)).trans he)

noncomputable def outputStack : Stack := copyStack GraphCopyFromUnary.outputStack

theorem final_output (g : EncodedGraph.Graph) (N : ℕ) :
    (finalHost g N).stk outputStack =
      EncodedGraph.encode (encodedCopies g (copies N g.edges.length)) := by
  change BitMachineStackEmbedding.bank copyStack _ _ (copyStack _) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact GraphCopyFromUnary.final_output g N

#print axioms encoded_graph_copy_run
#print axioms final_output

end Paper2.CurrentAdditive.GraphCopyEncoded
