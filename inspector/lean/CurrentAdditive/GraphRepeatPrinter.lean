import CurrentAdditive.GraphShiftPrinter
import EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream

/-! Selected v39 sources.tex:69-78. This removes preloading of the repeated
endpoint stream: the physical repetition loop receives one original stream
and a unary copy-count bank, then joins the shift and complete graph printer. -/

namespace Paper2.CurrentAdditive.GraphRepeatPrinter

open EthInapproximability.CurrentPaper Turing BitMachineEncoding
open Paper2.CurrentAdditive.GraphCopyPadding
open Paper2.CurrentAdditive.GraphCopyMachineStages

abbrev Stack := SourceNormalizationMachineRepeatStream.Stack ⊕ GraphShiftPrinter.Stack
abbrev Label := SourceNormalizationMachineRepeatStream.Phase ⊕ GraphShiftPrinter.Label
abbrev Control := Option Bool × GraphShiftPrinter.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def repeatStack : SourceNormalizationMachineRepeatStream.Stack ↪ Stack :=
  ⟨Sum.inl, Sum.inl_injective⟩

noncomputable def shiftStack : GraphShiftPrinter.Stack ↪ Stack where
  toFun k := if k = .inl 0 then .inl 3 else .inr k
  inj' := by
    intro a b h
    by_cases ha : a = .inl 0 <;> by_cases hb : b = .inl 0 <;> simp_all

noncomputable def repeatControl (v : Option Bool) : Control :=
  (v, GraphShiftPrinter.shiftControl (false, none))
def shiftControl (v : GraphShiftPrinter.Control) : Control := (none, v)

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt repeatStack Sum.inl repeatControl Prod.fst
      (some (.inr (.inl .peek))) (SourceNormalizationMachineRepeatStream.program l)
  | .inr l => BitMachineStackEmbedding.stmt shiftStack Sum.inr shiftControl Prod.snd
      none (GraphShiftPrinter.program l)

noncomputable def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def originalStream (g : EncodedGraph.Graph) : List Bool :=
  SourceNormalizationMachineEndpointWriter.unaryEdges g.edges

theorem repeated_eq_copyInput (g : EncodedGraph.Graph) (c : ℕ) :
    SourceNormalizationMachineRepeatStream.repeated (originalStream g) c =
      SourceNormalizationMachineShiftCopies.copyInput (endpointList g) c := by
  rw [SourceNormalizationMachineRepeatStream.repeated_eq_flatMap_range,
    SourceNormalizationMachineShiftCopies.copyInput_eq_copy_major]
  simp only [originalStream, unaryEdges_eq_endpointList]

def repeatInitial (g : EncodedGraph.Graph) (c : ℕ) : SourceNormalizationMachineRepeatStream.Config :=
  SourceNormalizationMachineRepeatStream.cfg (some .next) none
    (originalStream g) [] (List.replicate c true) [] []

def repeatFinal (g : EncodedGraph.Graph) (c : ℕ) : SourceNormalizationMachineRepeatStream.Config :=
  SourceNormalizationMachineRepeatStream.cfg none none
    (originalStream g) [] []
    (SourceNormalizationMachineShiftCopies.copyInput (endpointList g) c) []

noncomputable def start (g : EncodedGraph.Graph) (c : ℕ) : Config :=
  ⟨some (.inl .next), repeatControl none,
    Sum.elim (repeatInitial g c).stk
      (fun k => if k = .inl 0 then [] else (GraphShiftPrinter.start g c).stk k)⟩

def sourceStack : Stack := .inl 0
def copiesStack : Stack := .inl 2
def fieldsStack : Stack := .inr (.inl 5)
def verticesStack : Stack := .inr (.inl 7)

theorem endpointList_length (g : EncodedGraph.Graph) :
    (endpointList g).length = 2 * g.edges.length := by
  change (g.edges.flatMap fun p => [p.1, p.2]).length = 2 * g.edges.length
  induction g.edges with
  | nil => rfl
  | cons p ps ih => simp [ih]; omega

theorem start_stacks (g : EncodedGraph.Graph) (c : ℕ) (k : Stack) :
    (start g c).stk k =
      if k = sourceStack then originalStream g
      else if k = copiesStack then List.replicate c true
      else if k = fieldsStack then List.replicate (2 * g.edges.length) true
      else if k = verticesStack then List.replicate g.vertices true else [] := by
  cases k with
  | inl k =>
      fin_cases k <;> rfl
  | inr k =>
      cases k with
      | inl k =>
          fin_cases k <;>
            simp [start, repeatInitial, SourceNormalizationMachineRepeatStream.cfg,
              sourceStack, copiesStack, fieldsStack, verticesStack, GraphShiftPrinter.start,
              GraphShiftPrinter.shiftInitial, SourceNormalizationMachineShiftCopies.cfg,
              endpointList_length]
      | inr k => simp [start, sourceStack, copiesStack, fieldsStack,
          verticesStack, GraphShiftPrinter.start]

noncomputable def afterRepeat (g : EncodedGraph.Graph) (c : ℕ) : Config :=
  BitMachineStackEmbedding.cfg repeatStack (start g c).stk Sum.inl repeatControl
    (some (.inr (.inl .peek))) (repeatFinal g c)

private theorem repeat_initial (g : EncodedGraph.Graph) (c : ℕ) :
    BitMachineStackEmbedding.cfg repeatStack (start g c).stk Sum.inl repeatControl
      (some (.inr (.inl .peek))) (repeatInitial g c) = start g c := by
  have hb := BitMachineStackEmbedding.bank_eq_self repeatStack (start g c).stk
    (repeatInitial g c).stk (by intro k; rfl)
  change (⟨some (.inl .next), repeatControl none,
    BitMachineStackEmbedding.bank repeatStack (start g c).stk (repeatInitial g c).stk⟩ : Config) = _
  rw [hb]
  rfl

theorem repeat_stage (g : EncodedGraph.Graph) (c : ℕ) :
    ∃ t ≤ c * (2 * (originalStream g).length + 3) + 1,
      run t (start g c) = afterRepeat g c := by
  have hr := SourceNormalizationMachineRepeatStream.repeat_run (originalStream g) [] [] c none
  have hr' : SourceNormalizationMachineRepeatStream.run
      (c * (2 * (originalStream g).length + 3) + 1) (repeatInitial g c) = repeatFinal g c := by
    simpa only [repeatInitial, repeatFinal, List.append_nil, repeated_eq_copyInput] using hr
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs repeatStack (start g c).stk
    Sum.inl repeatControl Prod.fst (by intro v; rfl) (some (.inr (.inl .peek)))
    SourceNormalizationMachineRepeatStream.program program (by intro l; rfl)
    (repeatInitial g c) (c * (2 * (originalStream g).length + 3) + 1) (by
      change (SourceNormalizationMachineRepeatStream.run _ _).l = none
      rw [hr']; rfl)
  change ((advance SourceNormalizationMachineRepeatStream.program)^[_]) _ = _ at hr'
  rw [hr'] at he
  exact ⟨t, ht, (repeat_initial g c).symm ▸ he⟩

@[simp] theorem afterRepeat_at (g : EncodedGraph.Graph) (c : ℕ)
    (k : SourceNormalizationMachineRepeatStream.Stack) :
    (afterRepeat g c).stk (.inl k) = (repeatFinal g c).stk k :=
  BitMachineStackEmbedding.bank_at repeatStack _ _ k

@[simp] theorem afterRepeat_extra (g : EncodedGraph.Graph) (c : ℕ)
    (k : GraphShiftPrinter.Stack) :
    (afterRepeat g c).stk (.inr k) =
      if k = .inl 0 then [] else (GraphShiftPrinter.start g c).stk k := by
  rw [show (afterRepeat g c).stk (.inr k) = (start g c).stk (.inr k) from
    BitMachineStackEmbedding.bank_outside repeatStack _ _ _ (by simp [repeatStack])]
  rfl

private theorem shift_stacks (g : EncodedGraph.Graph) (c : ℕ)
    (k : GraphShiftPrinter.Stack) :
    (GraphShiftPrinter.start g c).stk k = (afterRepeat g c).stk (shiftStack k) := by
  by_cases hk : k = .inl 0
  · subst k
    change (GraphShiftPrinter.start g c).stk (.inl 0) = (afterRepeat g c).stk (.inl 3)
    rw [afterRepeat_at]
    rfl
  · simp [shiftStack, hk]

private theorem shift_initial (g : EncodedGraph.Graph) (c : ℕ) :
    afterRepeat g c = BitMachineStackEmbedding.cfg shiftStack (afterRepeat g c).stk
      Sum.inr shiftControl none (GraphShiftPrinter.start g c) := by
  have hb := BitMachineStackEmbedding.bank_eq_self shiftStack (afterRepeat g c).stk
    (GraphShiftPrinter.start g c).stk (shift_stacks g c)
  change (⟨some (.inr (.inl .peek)), shiftControl (GraphShiftPrinter.shiftControl (false, none)),
    (afterRepeat g c).stk⟩ : Config) =
    ⟨some (.inr (.inl .peek)), shiftControl (GraphShiftPrinter.shiftControl (false, none)),
      BitMachineStackEmbedding.bank shiftStack (afterRepeat g c).stk (GraphShiftPrinter.start g c).stk⟩
  rw [hb]

noncomputable def finalHost (g : EncodedGraph.Graph) (c : ℕ) : Config :=
  BitMachineStackEmbedding.cfg shiftStack (afterRepeat g c).stk Sum.inr shiftControl none
    (GraphShiftPrinter.finalHost g c)

noncomputable def totalBound (g : EncodedGraph.Graph) (c : ℕ) : ℕ :=
  c * (2 * (originalStream g).length + 3) + 1 + GraphShiftPrinter.totalBound g c

/-- Copies an ordered original unary graph using a physical unary copy-count
bank. Its initial stream occurs only once, and no shifted endpoint is supplied. -/
theorem copy_printer_run (g : EncodedGraph.Graph) (hm : 0 < g.edges.length)
    (c : ℕ) (hc : 0 < c) :
    ∃ t ≤ totalBound g c, run t (start g c) = finalHost g c := by
  obtain ⟨a, ha, hra⟩ := repeat_stage g c
  obtain ⟨b, hb, hrb⟩ := GraphShiftPrinter.copy_printer_run g hm c hc
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs shiftStack (afterRepeat g c).stk
    Sum.inr shiftControl Prod.snd (by intro v; rfl) none
    GraphShiftPrinter.program program (by intro l; rfl) (GraphShiftPrinter.start g c) b (by
      change (GraphShiftPrinter.run b _).l = none
      rw [hrb]
      rfl)
  change ((advance GraphShiftPrinter.program)^[b]) _ = _ at hrb
  rw [hrb] at he
  refine ⟨a + t, by unfold totalBound; omega, ?_⟩
  exact (run_add hra t).trans ((congrArg (run t) (shift_initial g c)).trans he)

theorem final_output (g : EncodedGraph.Graph) (c : ℕ) :
    (finalHost g c).stk
      (shiftStack (GraphShiftPrinter.printerStack (GraphUnaryPrinter.finalizerStack 4))) =
      EncodedGraph.encode (encodedCopies g c) := by
  change BitMachineStackEmbedding.bank shiftStack _ _ (shiftStack _) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact GraphShiftPrinter.final_output g c

#print axioms copy_printer_run
#print axioms final_output

end Paper2.CurrentAdditive.GraphRepeatPrinter
