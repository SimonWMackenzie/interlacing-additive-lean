import CurrentAdditive.GraphCopyMachineStages
import CurrentAdditive.GraphUnaryPrinter

/-!
Selected v39 `appendices/sources.tex:69-78`. One fixed finite program shifts
the original labels copy by copy, computes the final vertex count by a charged
width scan, and invokes the literal canonical graph serializer. The initial
bank contains repeated ORIGINAL unary endpoint fields, not shifted fields.
-/

namespace Paper2.CurrentAdditive.GraphShiftPrinter

open EthInapproximability.CurrentPaper Turing BitMachineEncoding
open Paper2.CurrentAdditive.GraphCopyPadding
open Paper2.CurrentAdditive.GraphCopyMachineStages

abbrev Stack := SourceNormalizationMachineShiftCopies.Stack ⊕ GraphUnaryPrinter.Stack
abbrev Label := SourceNormalizationMachineShiftCopies.Phase ⊕
  (SourceNormalizationMachineOffsetWidth.Phase ⊕ GraphUnaryPrinter.Label)
abbrev Control := SourceNormalizationMachineShiftCopies.Control ×
  (Option Bool × GraphUnaryPrinter.Control)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def shiftStack : SourceNormalizationMachineShiftCopies.Stack ↪ Stack :=
  ⟨Sum.inl, Sum.inl_injective⟩

def offsetStack : SourceNormalizationMachineOffsetWidth.Stack ↪ Stack where
  toFun k := .inl (match k.val with | 0 => 7 | 1 => 8 | 2 => 1 | _ => 2)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

noncomputable def printerStack : GraphUnaryPrinter.Stack ↪ Stack where
  toFun k := if k = GraphUnaryPrinter.streamStack then .inl 4
    else if k = GraphUnaryPrinter.vertexStack then .inl 1 else .inr k
  inj' := by
    intro a b h
    by_cases ha : a = GraphUnaryPrinter.streamStack <;>
      by_cases h'a : a = GraphUnaryPrinter.vertexStack <;>
      by_cases hb : b = GraphUnaryPrinter.streamStack <;>
      by_cases h'b : b = GraphUnaryPrinter.vertexStack <;>
      simp_all [GraphUnaryPrinter.streamStack, GraphUnaryPrinter.vertexStack]

noncomputable def shiftControl (v : SourceNormalizationMachineShiftCopies.Control) : Control :=
  (v, (none, GraphUnaryPrinter.writerControl GraphUnaryPrinter.afterWriterControl))
noncomputable def offsetControl (v : Option Bool) : Control :=
  ((false, none), (v, GraphUnaryPrinter.writerControl GraphUnaryPrinter.afterWriterControl))
noncomputable def printerControl (v : GraphUnaryPrinter.Control) : Control :=
  ((false, none), (none, v))

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt shiftStack Sum.inl shiftControl Prod.fst
      (some (.inr (.inl .scan))) (SourceNormalizationMachineShiftCopies.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt offsetStack
      (fun l => .inr (.inl l)) offsetControl (fun v => v.2.1)
      (some (.inr (.inr (.inl (.inl .read)))))
      (SourceNormalizationMachineOffsetWidth.program l)
  | .inr (.inr l) => BitMachineStackEmbedding.stmt printerStack
      (fun l => .inr (.inr l)) printerControl (fun v => v.2.2) none
      (GraphUnaryPrinter.program l)

noncomputable def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def shiftInitial (g : EncodedGraph.Graph) (c : ℕ) :
    SourceNormalizationMachineShiftCopies.Config :=
  SourceNormalizationMachineShiftCopies.cfg (some .peek) (false, none)
    (SourceNormalizationMachineShiftCopies.copyInput (endpointList g) c)
    [] [] [] [] (List.replicate (endpointList g).length true) []
    (List.replicate g.vertices true) []

def shiftFinal (g : EncodedGraph.Graph) (c : ℕ) :
    SourceNormalizationMachineShiftCopies.Config :=
  SourceNormalizationMachineShiftCopies.cfg none (false, none) []
    (List.replicate ((c - 1) * g.vertices) true) [] []
    (SourceNormalizationMachineEndpointWriter.unaryEdges (encodedCopies g c).edges)
    [] (List.replicate (endpointList g).length true)
    (List.replicate g.vertices true) []

noncomputable def start (g : EncodedGraph.Graph) (c : ℕ) : Config :=
  ⟨some (.inl .peek), shiftControl (false, none),
    Sum.elim (shiftInitial g c).stk (fun _ => [])⟩

noncomputable def afterShift (g : EncodedGraph.Graph) (c : ℕ) : Config :=
  BitMachineStackEmbedding.cfg shiftStack (start g c).stk Sum.inl shiftControl
    (some (.inr (.inl .scan))) (shiftFinal g c)

private theorem shift_initial (g : EncodedGraph.Graph) (c : ℕ) :
    BitMachineStackEmbedding.cfg shiftStack (start g c).stk Sum.inl shiftControl
      (some (.inr (.inl .scan))) (shiftInitial g c) = start g c := by
  have hb := BitMachineStackEmbedding.bank_eq_self shiftStack (start g c).stk
    (shiftInitial g c).stk (by intro k; rfl)
  change (⟨some (.inl .peek), shiftControl (false, none),
    BitMachineStackEmbedding.bank shiftStack (start g c).stk (shiftInitial g c).stk⟩ : Config) = _
  rw [hb]
  rfl

def shiftBound (g : EncodedGraph.Graph) (c : ℕ) : ℕ :=
  SourceNormalizationMachineShiftCopies.copiesCost (endpointList g)
    (List.replicate g.vertices true) 0 c +
  (SourceNormalizationMachineEndpointWriter.unaryEdges (encodedCopies g c).edges).length + 2

theorem shift_stage (g : EncodedGraph.Graph) (hm : 0 < g.edges.length)
    (c : ℕ) (hc : 0 < c) :
    ∃ t ≤ shiftBound g c, run t (start g c) = afterShift g c := by
  obtain ⟨a, ha, hr⟩ := physical_shift_run g hm c hc
  have hr' : SourceNormalizationMachineShiftCopies.run a (shiftInitial g c) =
      shiftFinal g c := by
    simpa only [shiftInitial, shiftFinal, List.replicate_zero] using hr
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs shiftStack (start g c).stk
    Sum.inl shiftControl Prod.fst (by intro v; rfl) (some (.inr (.inl .scan)))
    SourceNormalizationMachineShiftCopies.program program (by intro l; rfl)
    (shiftInitial g c) a (by
      change (SourceNormalizationMachineShiftCopies.run a _).l = none
      rw [hr']; rfl)
  change ((advance SourceNormalizationMachineShiftCopies.program)^[a]) _ = _ at hr'
  rw [hr'] at he
  exact ⟨t, ht.trans ha, (shift_initial g c).symm ▸ he⟩

@[simp] theorem afterShift_at (g : EncodedGraph.Graph) (c : ℕ)
    (k : SourceNormalizationMachineShiftCopies.Stack) :
    (afterShift g c).stk (.inl k) = (shiftFinal g c).stk k :=
  BitMachineStackEmbedding.bank_at shiftStack _ _ k

@[simp] theorem afterShift_extra (g : EncodedGraph.Graph) (c : ℕ)
    (k : GraphUnaryPrinter.Stack) : (afterShift g c).stk (.inr k) = [] := by
  rw [show (afterShift g c).stk (.inr k) = (start g c).stk (.inr k) from
    BitMachineStackEmbedding.bank_outside shiftStack _ _ _ (by simp [shiftStack])]
  rfl

def offsetInitial (g : EncodedGraph.Graph) (c : ℕ) : SourceNormalizationMachineOffsetWidth.Config :=
  SourceNormalizationMachineOffsetWidth.cfg (some .scan) none
    (List.replicate g.vertices true) []
    (List.replicate ((c - 1) * g.vertices) true) []

def offsetFinal (g : EncodedGraph.Graph) (c : ℕ) : SourceNormalizationMachineOffsetWidth.Config :=
  SourceNormalizationMachineOffsetWidth.cfg none none
    (List.replicate g.vertices true) [] (List.replicate (c * g.vertices) true) []

private theorem offset_initial (g : EncodedGraph.Graph) (c : ℕ) :
    afterShift g c = BitMachineStackEmbedding.cfg offsetStack (afterShift g c).stk
      (fun l => .inr (.inl l)) offsetControl
      (some (.inr (.inr (.inl (.inl .read))))) (offsetInitial g c) := by
  have hb := BitMachineStackEmbedding.bank_eq_self offsetStack (afterShift g c).stk
    (offsetInitial g c).stk (by
      intro k
      fin_cases k <;>
        simp [offsetInitial, SourceNormalizationMachineOffsetWidth.cfg,
          offsetStack, shiftFinal, SourceNormalizationMachineShiftCopies.cfg])
  change (⟨some (.inr (.inl .scan)), offsetControl none,
    (afterShift g c).stk⟩ : Config) =
    ⟨some (.inr (.inl .scan)), offsetControl none,
      BitMachineStackEmbedding.bank offsetStack (afterShift g c).stk (offsetInitial g c).stk⟩
  rw [hb]

noncomputable def afterOffset (g : EncodedGraph.Graph) (c : ℕ) : Config :=
  BitMachineStackEmbedding.cfg offsetStack (afterShift g c).stk
    (fun l => .inr (.inl l)) offsetControl
    (some (.inr (.inr (.inl (.inl .read))))) (offsetFinal g c)

theorem offset_stage (g : EncodedGraph.Graph) (c : ℕ) (hc : 0 < c) :
    ∃ t ≤ 2 * g.vertices + 2, run t (afterShift g c) = afterOffset g c := by
  have hr := SourceNormalizationMachineOffsetWidth.add_width_run
    (List.replicate g.vertices true) [] ((c - 1) * g.vertices)
  have hm : (c - 1) * g.vertices + g.vertices = c * g.vertices := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  have hr' : SourceNormalizationMachineOffsetWidth.run (2 * g.vertices + 2)
      (offsetInitial g c) = offsetFinal g c := by
    simpa only [List.length_replicate, List.count_replicate_self, hm,
      offsetInitial, offsetFinal] using hr
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs offsetStack
    (afterShift g c).stk (fun l => .inr (.inl l)) offsetControl (fun v => v.2.1)
    (by intro v; rfl) (some (.inr (.inr (.inl (.inl .read)))))
    SourceNormalizationMachineOffsetWidth.program program (by intro l; rfl)
    (offsetInitial g c) (2 * g.vertices + 2) (by
      change (SourceNormalizationMachineOffsetWidth.run _ _).l = none
      rw [hr']; rfl)
  change ((advance SourceNormalizationMachineOffsetWidth.program)^[2 * g.vertices + 2]) _ = _ at hr'
  rw [hr'] at he
  exact ⟨t, ht, (offset_initial g c).symm ▸ he⟩

private theorem offset_at (g : EncodedGraph.Graph) (c : ℕ)
    (k : SourceNormalizationMachineOffsetWidth.Stack) :
    (afterOffset g c).stk (offsetStack k) = (offsetFinal g c).stk k :=
  BitMachineStackEmbedding.bank_at offsetStack _ _ k

private theorem offset_outside (g : EncodedGraph.Graph) (c : ℕ) (j : Stack)
    (hj : ¬ ∃ k, offsetStack k = j) :
    (afterOffset g c).stk j = (afterShift g c).stk j :=
  BitMachineStackEmbedding.bank_outside offsetStack _ _ j hj

private theorem printer_stacks (g : EncodedGraph.Graph) (c : ℕ)
    (k : GraphUnaryPrinter.Stack) :
    (GraphUnaryPrinter.start (encodedCopies g c)).stk k =
      (afterOffset g c).stk (printerStack k) := by
  rw [GraphUnaryPrinter.start_stacks]
  by_cases hs : k = GraphUnaryPrinter.streamStack
  · subst k
    change SourceNormalizationMachineEndpointWriter.unaryEdges (encodedCopies g c).edges =
      (afterOffset g c).stk (.inl 4)
    have hn : ¬ ∃ k, offsetStack k = Sum.inl (4 : Fin 9) := by
      rintro ⟨k, hk⟩
      fin_cases k <;> simp [offsetStack] at hk
    rw [offset_outside g c _ hn, afterShift_at]
    rfl
  · by_cases hv : k = GraphUnaryPrinter.vertexStack
    · subst k
      change List.replicate (encodedCopies g c).vertices true =
        (afterOffset g c).stk (.inl 1)
      have he : (Sum.inl (1 : Fin 9) : Stack) = offsetStack 2 := rfl
      rw [he, offset_at]
      rfl
    · simp only [hs, hv, ↓reduceIte]
      have hk : printerStack k = Sum.inr k := by
        change (if k = GraphUnaryPrinter.streamStack then Sum.inl 4
          else if k = GraphUnaryPrinter.vertexStack then Sum.inl 1 else Sum.inr k) = _
        simp only [hs, hv, ↓reduceIte]
      rw [hk]
      have hn : ¬ ∃ j, offsetStack j = Sum.inr k := by
        rintro ⟨j, hj⟩
        fin_cases j <;> simp [offsetStack] at hj
      rw [offset_outside g c _ hn, afterShift_extra]

private theorem printer_initial (g : EncodedGraph.Graph) (c : ℕ) :
    afterOffset g c = BitMachineStackEmbedding.cfg printerStack (afterOffset g c).stk
      (fun l => .inr (.inr l)) printerControl none
      (GraphUnaryPrinter.start (encodedCopies g c)) := by
  have hb := BitMachineStackEmbedding.bank_eq_self printerStack (afterOffset g c).stk
    (GraphUnaryPrinter.start (encodedCopies g c)).stk (printer_stacks g c)
  change (⟨some (.inr (.inr (.inl (.inl .read)))),
    printerControl (GraphUnaryPrinter.writerControl GraphUnaryPrinter.afterWriterControl),
    (afterOffset g c).stk⟩ : Config) =
    ⟨some (.inr (.inr (.inl (.inl .read)))),
      printerControl (GraphUnaryPrinter.writerControl GraphUnaryPrinter.afterWriterControl),
      BitMachineStackEmbedding.bank printerStack (afterOffset g c).stk
        (GraphUnaryPrinter.start (encodedCopies g c)).stk⟩
  rw [hb]

noncomputable def finalHost (g : EncodedGraph.Graph) (c : ℕ) : Config :=
  BitMachineStackEmbedding.cfg printerStack (afterOffset g c).stk
    (fun l => .inr (.inr l)) printerControl none
    (GraphUnaryPrinter.finalHost (encodedCopies g c))

noncomputable def totalBound (g : EncodedGraph.Graph) (c : ℕ) : ℕ :=
  shiftBound g c + (2 * g.vertices + 2) + GraphUnaryPrinter.totalBound (encodedCopies g c)

theorem copy_printer_run (g : EncodedGraph.Graph) (hm : 0 < g.edges.length)
    (c : ℕ) (hc : 0 < c) :
    ∃ t ≤ totalBound g c, run t (start g c) = finalHost g c := by
  obtain ⟨a, ha, hsa⟩ := shift_stage g hm c hc
  obtain ⟨b, hb, hoa⟩ := offset_stage g c hc
  have hbefore := (run_add hsa b).trans hoa
  obtain ⟨p, hp, hpr⟩ := GraphUnaryPrinter.printer_run (encodedCopies g c)
  obtain ⟨d, hd, he⟩ := BitMachineStackEmbedding.outputs printerStack
    (afterOffset g c).stk (fun l => .inr (.inr l)) printerControl
    (fun v => v.2.2) (by intro v; rfl) none GraphUnaryPrinter.program program
    (by intro l; rfl) (GraphUnaryPrinter.start (encodedCopies g c)) p (by
      change (GraphUnaryPrinter.run p _).l = none
      rw [hpr]
      exact GraphUnaryPrinter.final_halts _)
  change ((advance GraphUnaryPrinter.program)^[p]) _ = _ at hpr
  rw [hpr] at he
  refine ⟨a + b + d, by unfold totalBound; omega, ?_⟩
  exact (run_add hbefore d).trans
    ((congrArg (run d) (printer_initial g c)).trans he)

theorem final_output (g : EncodedGraph.Graph) (c : ℕ) :
    (finalHost g c).stk (printerStack (GraphUnaryPrinter.finalizerStack 4)) =
      EncodedGraph.encode (encodedCopies g c) := by
  change BitMachineStackEmbedding.bank printerStack _ _ (printerStack _) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact GraphUnaryPrinter.final_output _

#print axioms copy_printer_run
#print axioms final_output

end Paper2.CurrentAdditive.GraphShiftPrinter
