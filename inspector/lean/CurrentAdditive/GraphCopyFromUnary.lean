import CurrentAdditive.GraphCopyCount
import CurrentAdditive.GraphRepeatPrinter

/-! Selected v39 sources.tex:69-78. The copy count and endpoint-field count
are now computed on tape from original N and m, before the physical repetition,
label shift, final vertex count, and complete canonical serializer. -/

namespace Paper2.CurrentAdditive.GraphCopyFromUnary

open EthInapproximability.CurrentPaper Turing BitMachineEncoding
open Paper2.CurrentAdditive.GraphCopyPadding

abbrev Stack := GraphCopyCount.Stack ⊕ (GraphRepeatPrinter.Stack ⊕ Fin 1)
abbrev Label := GraphCopyCount.Label ⊕ GraphRepeatPrinter.Label
abbrev Control := GraphCopyCount.Control × GraphRepeatPrinter.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def countStack : GraphCopyCount.Stack ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩

noncomputable def repeatStack : GraphRepeatPrinter.Stack ↪ Stack where
  toFun k :=
    if k = GraphRepeatPrinter.sourceStack then .inl GraphCopyCount.payloadStack
    else if k = GraphRepeatPrinter.copiesStack then .inl GraphCopyCount.copiesStack
    else if k = GraphRepeatPrinter.fieldsStack then .inl GraphCopyCount.fieldCountStack
    else if k = GraphRepeatPrinter.verticesStack then .inr (.inr 0) else .inr (.inl k)
  inj' := by
    intro a b h
    dsimp only at h
    split_ifs at h <;> simp_all [GraphRepeatPrinter.sourceStack,
      GraphRepeatPrinter.copiesStack, GraphRepeatPrinter.fieldsStack,
      GraphRepeatPrinter.verticesStack, GraphCopyCount.payloadStack,
      GraphCopyCount.copiesStack, GraphCopyCount.fieldCountStack]

noncomputable def countControl (v : GraphCopyCount.Control) : Control :=
  (v, GraphRepeatPrinter.repeatControl none)
def repeatControl (v : GraphRepeatPrinter.Control) : Control :=
  (GraphCopyCount.doubleControl none, v)

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt countStack Sum.inl countControl Prod.fst
      (some (.inr (.inl .next))) (GraphCopyCount.program l)
  | .inr l => BitMachineStackEmbedding.stmt repeatStack Sum.inr repeatControl Prod.snd
      none (GraphRepeatPrinter.program l)

noncomputable def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

noncomputable def start (g : EncodedGraph.Graph) (N : ℕ) : Config :=
  ⟨some (.inl (.inr (.inr ()))), countControl (GraphCopyCount.countControl (false, ())),
    Sum.elim (GraphCopyCount.start N g.edges.length (GraphRepeatPrinter.originalStream g)).stk
      (Sum.elim (fun _ => []) (fun _ => List.replicate g.vertices true))⟩

def originalNStack : Stack := .inl GraphCopyCount.originalNStack
def originalMStack : Stack := .inl (.inl (.inr 1))
def originalStreamStack : Stack := .inl GraphCopyCount.payloadStack
def originalVerticesStack : Stack := .inr (.inr 0)

theorem start_stacks (g : EncodedGraph.Graph) (N : ℕ) (k : Stack) :
    (start g N).stk k =
      if k = originalNStack then List.replicate N true
      else if k = originalMStack then List.replicate g.edges.length true
      else if k = originalStreamStack then GraphRepeatPrinter.originalStream g
      else if k = originalVerticesStack then List.replicate g.vertices true else [] := by
  cases k with
  | inl k =>
      cases k with
      | inl k =>
          cases k with
          | inl k => fin_cases k <;> rfl
          | inr k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | inr k =>
      cases k with
      | inl k => simp [start, originalNStack, originalMStack,
          originalStreamStack, originalVerticesStack]
      | inr k => fin_cases k <;> rfl

noncomputable def afterCount (g : EncodedGraph.Graph) (N : ℕ) : Config :=
  BitMachineStackEmbedding.cfg countStack (start g N).stk Sum.inl countControl
    (some (.inr (.inl .next)))
    (GraphCopyCount.finalHost N g.edges.length (GraphRepeatPrinter.originalStream g))

private theorem count_initial (g : EncodedGraph.Graph) (N : ℕ) :
    BitMachineStackEmbedding.cfg countStack (start g N).stk Sum.inl countControl
      (some (.inr (.inl .next)))
      (GraphCopyCount.start N g.edges.length (GraphRepeatPrinter.originalStream g)) = start g N := by
  have hb := BitMachineStackEmbedding.bank_eq_self countStack (start g N).stk
    (GraphCopyCount.start N g.edges.length (GraphRepeatPrinter.originalStream g)).stk
    (by intro k; rfl)
  change (⟨some (.inl (.inr (.inr ()))), countControl (GraphCopyCount.countControl (false, ())),
    BitMachineStackEmbedding.bank countStack (start g N).stk
      (GraphCopyCount.start N g.edges.length (GraphRepeatPrinter.originalStream g)).stk⟩ : Config) = _
  rw [hb]
  rfl

theorem count_stage (g : EncodedGraph.Graph) (N : ℕ) (hm : 0 < g.edges.length) :
    ∃ t ≤ 10 * N + 15 * g.edges.length + 16,
      run t (start g N) = afterCount g N := by
  obtain ⟨a, ha, hr⟩ := GraphCopyCount.preparation_run N g.edges.length hm
    (GraphRepeatPrinter.originalStream g)
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs countStack (start g N).stk
    Sum.inl countControl Prod.fst (by intro v; rfl) (some (.inr (.inl .next)))
    GraphCopyCount.program program (by intro l; rfl)
    (GraphCopyCount.start N g.edges.length (GraphRepeatPrinter.originalStream g)) a (by
      change (GraphCopyCount.run a _).l = none
      rw [hr]; rfl)
  change ((advance GraphCopyCount.program)^[a]) _ = _ at hr
  rw [hr] at he
  exact ⟨t, ht.trans ha, (count_initial g N).symm ▸ he⟩

@[simp] theorem afterCount_at (g : EncodedGraph.Graph) (N : ℕ) (k : GraphCopyCount.Stack) :
    (afterCount g N).stk (.inl k) =
      (GraphCopyCount.finalHost N g.edges.length (GraphRepeatPrinter.originalStream g)).stk k :=
  BitMachineStackEmbedding.bank_at countStack _ _ k

@[simp] theorem afterCount_extra (g : EncodedGraph.Graph) (N : ℕ)
    (k : GraphRepeatPrinter.Stack ⊕ Fin 1) :
    (afterCount g N).stk (.inr k) = (start g N).stk (.inr k) :=
  BitMachineStackEmbedding.bank_outside countStack _ _ _ (by simp [countStack])

private theorem repeat_stacks (g : EncodedGraph.Graph) (N : ℕ)
    (k : GraphRepeatPrinter.Stack) :
    (GraphRepeatPrinter.start g (copies N g.edges.length)).stk k =
      (afterCount g N).stk (repeatStack k) := by
  rw [GraphRepeatPrinter.start_stacks]
  by_cases hs : k = GraphRepeatPrinter.sourceStack
  · subst k
    change GraphRepeatPrinter.originalStream g =
      (afterCount g N).stk (.inl GraphCopyCount.payloadStack)
    rw [afterCount_at, GraphCopyCount.final_payload]
  · by_cases hc : k = GraphRepeatPrinter.copiesStack
    · subst k
      change List.replicate (copies N g.edges.length) true =
        (afterCount g N).stk (.inl GraphCopyCount.copiesStack)
      rw [afterCount_at, GraphCopyCount.final_copies]
    · by_cases hf : k = GraphRepeatPrinter.fieldsStack
      · subst k
        change List.replicate (2 * g.edges.length) true =
          (afterCount g N).stk (.inl GraphCopyCount.fieldCountStack)
        rw [afterCount_at, GraphCopyCount.final_fields]
      · by_cases hv : k = GraphRepeatPrinter.verticesStack
        · subst k
          change List.replicate g.vertices true = (afterCount g N).stk (.inr (.inr 0))
          rw [afterCount_extra]
          rfl
        · simp only [hs, hc, hf, hv, ↓reduceIte]
          have hk : repeatStack k = Sum.inr (Sum.inl k) := by
            change (if k = GraphRepeatPrinter.sourceStack then Sum.inl GraphCopyCount.payloadStack
              else if k = GraphRepeatPrinter.copiesStack then Sum.inl GraphCopyCount.copiesStack
              else if k = GraphRepeatPrinter.fieldsStack then Sum.inl GraphCopyCount.fieldCountStack
              else if k = GraphRepeatPrinter.verticesStack then Sum.inr (Sum.inr 0)
              else Sum.inr (Sum.inl k)) = _
            simp only [hs, hc, hf, hv, ↓reduceIte]
          rw [hk, afterCount_extra]
          rfl

private theorem repeat_initial (g : EncodedGraph.Graph) (N : ℕ) :
    afterCount g N = BitMachineStackEmbedding.cfg repeatStack (afterCount g N).stk
      Sum.inr repeatControl none (GraphRepeatPrinter.start g (copies N g.edges.length)) := by
  have hb := BitMachineStackEmbedding.bank_eq_self repeatStack (afterCount g N).stk
    (GraphRepeatPrinter.start g (copies N g.edges.length)).stk (repeat_stacks g N)
  change (⟨some (.inr (.inl .next)), repeatControl (GraphRepeatPrinter.repeatControl none),
    (afterCount g N).stk⟩ : Config) =
    ⟨some (.inr (.inl .next)), repeatControl (GraphRepeatPrinter.repeatControl none),
      BitMachineStackEmbedding.bank repeatStack (afterCount g N).stk
        (GraphRepeatPrinter.start g (copies N g.edges.length)).stk⟩
  rw [hb]

noncomputable def finalHost (g : EncodedGraph.Graph) (N : ℕ) : Config :=
  BitMachineStackEmbedding.cfg repeatStack (afterCount g N).stk Sum.inr repeatControl none
    (GraphRepeatPrinter.finalHost g (copies N g.edges.length))

noncomputable def totalBound (g : EncodedGraph.Graph) (N : ℕ) : ℕ :=
  10 * N + 15 * g.edges.length + 16 +
    GraphRepeatPrinter.totalBound g (copies N g.edges.length)

/-- A uniform finite Boolean-stack program whose input banks are only N,
the ORIGINAL vertex count, the ORIGINAL edge count, and ONE ORIGINAL unary
endpoint stream. Both repetition counters are physically computed. -/
theorem graph_copy_run (g : EncodedGraph.Graph) (N : ℕ) (hm : 0 < g.edges.length) :
    ∃ t ≤ totalBound g N, run t (start g N) = finalHost g N := by
  obtain ⟨a, ha, hra⟩ := count_stage g N hm
  have hc : 0 < copies N g.edges.length := by unfold copies; omega
  obtain ⟨b, hb, hrb⟩ := GraphRepeatPrinter.copy_printer_run g hm
    (copies N g.edges.length) hc
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs repeatStack (afterCount g N).stk
    Sum.inr repeatControl Prod.snd (by intro v; rfl) none
    GraphRepeatPrinter.program program (by intro l; rfl)
    (GraphRepeatPrinter.start g (copies N g.edges.length)) b (by
      change (GraphRepeatPrinter.run b _).l = none
      rw [hrb]; rfl)
  change ((advance GraphRepeatPrinter.program)^[b]) _ = _ at hrb
  rw [hrb] at he
  refine ⟨a + t, by unfold totalBound; omega, ?_⟩
  exact (run_add hra t).trans ((congrArg (run t) (repeat_initial g N)).trans he)

noncomputable def outputStack : Stack := repeatStack
  (GraphRepeatPrinter.shiftStack (GraphShiftPrinter.printerStack (GraphUnaryPrinter.finalizerStack 4)))

theorem final_output (g : EncodedGraph.Graph) (N : ℕ) :
    (finalHost g N).stk outputStack =
      EncodedGraph.encode (encodedCopies g (copies N g.edges.length)) := by
  change BitMachineStackEmbedding.bank repeatStack _ _ (repeatStack _) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact GraphRepeatPrinter.final_output g _

#print axioms graph_copy_run
#print axioms final_output

end Paper2.CurrentAdditive.GraphCopyFromUnary
