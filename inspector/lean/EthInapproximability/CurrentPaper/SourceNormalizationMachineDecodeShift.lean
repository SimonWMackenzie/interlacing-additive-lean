import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeDouble
import EthInapproximability.CurrentPaper.SourceNormalizationMachineShiftCopies

/-! The copy-major offset controller on the decoded and locally ranked graph. -/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeShift

open Turing BitMachineEncoding

def localIndices (g : EncodedGraph.Graph) : List ℕ :=
  (SourceNormalizationNumeric.paddedEndpoints g).map
    (SourceNormalizationMachineRanks.rankAt
      (SourceNormalizationNumeric.paddedSupport g))

theorem localIndices_length (g : EncodedGraph.Graph) :
    (localIndices g).length = 2 * (g.edges.length + 1) := by
  simp [localIndices, SourceNormalizationNumeric.paddedEndpoints,
    SourceNormalizationNumeric.endpoints_length]
  omega

theorem localIndices_ne_nil (g : EncodedGraph.Graph) : localIndices g ≠ [] := by
  intro h
  have hl := localIndices_length g
  rw [h] at hl
  simp at hl

private theorem endpointStream_append (xs ys : List ℕ) :
    SourceNormalizationMachineMark.endpointStream (xs ++ ys) =
      SourceNormalizationMachineMark.endpointStream xs ++
        SourceNormalizationMachineMark.endpointStream ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [SourceNormalizationMachineMark.endpointStream,
        List.append_assoc] using congrArg
          (List.append (EncodedGraph.unary x)) ih

private theorem endpointStream_flatMap {α : Type*} (xs : List α)
    (f : α → List ℕ) :
    SourceNormalizationMachineMark.endpointStream (xs.flatMap f) =
      xs.flatMap (fun x => SourceNormalizationMachineMark.endpointStream (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [endpointStream_append, ih]

theorem local_rank_stream_eq_copyInput (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineRanks.rankedStream
      (SourceNormalizationNumeric.paddedSupport g) 0
      (SourceNormalizationMachineDecodeRepeat.repeatedIndices g originalN) =
    SourceNormalizationMachineShiftCopies.copyInput
      (localIndices g) (SourceNormalizationNumeric.repetitions g originalN) := by
  rw [SourceNormalizationMachineShiftCopies.copyInput_eq_copy_major]
  unfold SourceNormalizationMachineRanks.rankedStream
    SourceNormalizationMachineDecodeRepeat.repeatedIndices localIndices
  simp only [Nat.add_zero, List.map_flatMap,
    endpointStream_flatMap, List.flatMap_map]

theorem shifted_eq_numeric (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    SourceNormalizationMachineShiftCopies.shiftedFrom
      (localIndices g)
      ((SourceNormalizationNumeric.paddedSupport g).count true) 0
      (SourceNormalizationNumeric.repetitions g originalN) =
    SourceNormalizationMachineMark.endpointStream
      (SourceNormalizationNumeric.endpoints
        (SourceNormalizationNumeric.numericGraph g originalN)) := by
  rw [SourceNormalizationMachineShiftCopies.shiftedFrom_eq_copy_major,
    SourceNormalizationMachineDecodeRepeat.padded_width_eq_numeric]
  rw [← SourceNormalizationMachineDecodeRepeat.rankedCopiedStream_eq_numeric
    g hg originalN]
  apply List.flatMap_congr
  intro k hk
  simp [SourceNormalizationMachineShiftCopies.shifted,
    SourceNormalizationMachineRanks.rankedStream, localIndices,
    List.map_map, Function.comp_def]

abbrev Stack := SourceNormalizationMachineDecodeDouble.Stack ⊕ Fin 6
abbrev Label := SourceNormalizationMachineDecodeDouble.Label ⊕
  SourceNormalizationMachineShiftCopies.Phase
abbrev Control := SourceNormalizationMachineDecodeDouble.Control ×
  SourceNormalizationMachineShiftCopies.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def doubleStack : SourceNormalizationMachineDecodeDouble.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def shiftStack : SourceNormalizationMachineShiftCopies.Stack ↪ Stack where
  toFun k := match k.val with
    | 0 => .inl (.inl (.inr 6))
    | 1 => .inr 0
    | 2 => .inr 1
    | 3 => .inr 2
    | 4 => .inr 3
    | 5 => .inl (.inr 1)
    | 6 => .inr 4
    | 7 => .inl (.inl (.inl (.inl (.inr 2))))
    | _ => .inr 5
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def initialShift : SourceNormalizationMachineShiftCopies.Control := (false,none)
def afterDoubleControl : SourceNormalizationMachineDecodeDouble.Control :=
  SourceNormalizationMachineDecodeDouble.doubleControl none
def decodeControl (v : SourceNormalizationMachineDecodeDouble.Control) : Control :=
  (v,initialShift)
def shiftControl (v : SourceNormalizationMachineShiftCopies.Control) : Control :=
  (afterDoubleControl,v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt doubleStack Sum.inl
      decodeControl Prod.fst
      (some (.inr SourceNormalizationMachineShiftCopies.Phase.peek))
      (SourceNormalizationMachineDecodeDouble.program l)
  | .inr l => BitMachineStackEmbedding.stmt shiftStack Sum.inr
      shiftControl Prod.snd none
      (SourceNormalizationMachineShiftCopies.program l)

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def start (graphBits : List Bool) (originalN : ℕ) : Config :=
  ⟨(SourceNormalizationMachineDecodeDouble.start graphBits originalN).l.map Sum.inl,
    decodeControl (SourceNormalizationMachineDecodeDouble.start graphBits originalN).var,
    Sum.elim (SourceNormalizationMachineDecodeDouble.start graphBits originalN).stk
      ![[],[],[],[],[],[]]⟩

private theorem double_program_eq (l : SourceNormalizationMachineDecodeDouble.Label) :
    program (.inl l) = BitMachineStackEmbedding.stmt doubleStack Sum.inl
      decodeControl Prod.fst
      (some (.inr SourceNormalizationMachineShiftCopies.Phase.peek))
      (SourceNormalizationMachineDecodeDouble.program l) := rfl

private theorem shift_program_eq (l : SourceNormalizationMachineShiftCopies.Phase) :
    program (.inr l) = BitMachineStackEmbedding.stmt shiftStack Sum.inr
      shiftControl Prod.snd none
      (SourceNormalizationMachineShiftCopies.program l) := rfl

def localBits (g : EncodedGraph.Graph) : List Bool :=
  SourceNormalizationNumeric.paddedSupport g

def copies (g : EncodedGraph.Graph) (originalN : ℕ) : ℕ :=
  SourceNormalizationNumeric.repetitions g originalN

def shiftInitialCfg (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineShiftCopies.Config :=
  SourceNormalizationMachineShiftCopies.cfg (some .peek) (false,none)
    (SourceNormalizationMachineShiftCopies.copyInput
      (localIndices g) (copies g originalN))
    [] [] [] [] (List.replicate (localIndices g).length true) []
    (localBits g) []

def shiftFinalCfg (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineShiftCopies.Config :=
  SourceNormalizationMachineShiftCopies.cfg none (false,none) []
    (List.replicate ((copies g originalN - 1) * (localBits g).count true) true)
    [] []
    (SourceNormalizationMachineShiftCopies.shiftedFrom
      (localIndices g) ((localBits g).count true) 0 (copies g originalN))
    [] (List.replicate (localIndices g).length true) (localBits g) []

def shiftCost (g : EncodedGraph.Graph) (originalN : ℕ) : ℕ :=
  SourceNormalizationMachineShiftCopies.copiesCost
    (localIndices g) (localBits g) 0 (copies g originalN) +
  (SourceNormalizationMachineShiftCopies.shiftedFrom
    (localIndices g) ((localBits g).count true) 0 (copies g originalN)).length + 2

private theorem double_initial (graphBits : List Bool) (originalN : ℕ) :
    BitMachineStackEmbedding.cfg doubleStack
      (start graphBits originalN).stk Sum.inl decodeControl
      (some (.inr SourceNormalizationMachineShiftCopies.Phase.peek))
      (SourceNormalizationMachineDecodeDouble.start graphBits originalN) =
        start graphBits originalN := by
  have hb := BitMachineStackEmbedding.bank_eq_self doubleStack
    (start graphBits originalN).stk
    (SourceNormalizationMachineDecodeDouble.start graphBits originalN).stk (by
      intro k
      rfl)
  change (⟨_,_, BitMachineStackEmbedding.bank doubleStack
    (start graphBits originalN).stk
    (SourceNormalizationMachineDecodeDouble.start graphBits originalN).stk⟩ : Config) = _
  rw [hb]
  rfl

noncomputable def afterDoubleHost (g : EncodedGraph.Graph) (originalN : ℕ) : Config :=
  BitMachineStackEmbedding.cfg doubleStack
    (start (EncodedGraph.encode g) originalN).stk Sum.inl decodeControl
    (some (.inr SourceNormalizationMachineShiftCopies.Phase.peek))
    (SourceNormalizationMachineDecodeDouble.finalHost g originalN)

private theorem double_stage (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecodeDouble.rankBound g originalN +
      2 * (g.edges.length + 1) + 2,
      run t (start (EncodedGraph.encode g) originalN) =
        afterDoubleHost g originalN := by
  obtain ⟨t,ht,he⟩ :=
    SourceNormalizationMachineDecodeDouble.decode_double_run g hg originalN
  obtain ⟨s,hs,hr⟩ := BitMachineStackEmbedding.outputs doubleStack
    (start (EncodedGraph.encode g) originalN).stk
    Sum.inl decodeControl Prod.fst (by intro v; rfl)
    (some (.inr SourceNormalizationMachineShiftCopies.Phase.peek))
    SourceNormalizationMachineDecodeDouble.program program double_program_eq
    (SourceNormalizationMachineDecodeDouble.start
      (EncodedGraph.encode g) originalN) t (by
      change (SourceNormalizationMachineDecodeDouble.run t
        (SourceNormalizationMachineDecodeDouble.start
          (EncodedGraph.encode g) originalN)).l = none
      rw [he]
      rfl)
  change ((advance SourceNormalizationMachineDecodeDouble.program)^[t]) _ = _ at he
  rw [he] at hr
  refine ⟨s, hs.trans ht, ?_⟩
  exact (congrArg (run s)
    (double_initial (EncodedGraph.encode g) originalN).symm).trans
    (by simpa only [run, afterDoubleHost,
      SourceNormalizationMachineDecodeDouble.finalHost] using hr)

private theorem afterDoubleHost_at (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineDecodeDouble.Stack) :
    (afterDoubleHost g originalN).stk (.inl k) =
      (SourceNormalizationMachineDecodeDouble.finalHost g originalN).stk k := by
  exact BitMachineStackEmbedding.bank_at doubleStack
    (start (EncodedGraph.encode g) originalN).stk
    (SourceNormalizationMachineDecodeDouble.finalHost g originalN).stk k

private theorem afterDoubleHost_extra (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : Fin 6) :
    (afterDoubleHost g originalN).stk (.inr k) = [] := by
  change BitMachineStackEmbedding.bank doubleStack
    (start (EncodedGraph.encode g) originalN).stk
    (SourceNormalizationMachineDecodeDouble.finalHost g originalN).stk
    (.inr k) = []
  rw [BitMachineStackEmbedding.bank_outside doubleStack
    (start (EncodedGraph.encode g) originalN).stk
    (SourceNormalizationMachineDecodeDouble.finalHost g originalN).stk
    (.inr k) (by
      rintro ⟨j,h⟩
      simp [doubleStack] at h)]
  fin_cases k <;> rfl

private theorem shift_initial_stacks (g : EncodedGraph.Graph) (originalN : ℕ) :
    ∀ k : SourceNormalizationMachineShiftCopies.Stack,
      (shiftInitialCfg g originalN).stk k =
        (afterDoubleHost g originalN).stk (shiftStack k) := by
  intro k
  fin_cases k <;>
    simp [shiftInitialCfg, SourceNormalizationMachineShiftCopies.cfg,
      shiftStack, afterDoubleHost_at, afterDoubleHost_extra,
      SourceNormalizationMachineDecodeDouble.final_counter,
      SourceNormalizationMachineDecodeDouble.final_support,
      localIndices_length, localBits]
  case «0» =>
    rw [SourceNormalizationMachineDecodeDouble.final_local_stream]
    exact (local_rank_stream_eq_copyInput g originalN).symm

private theorem shift_initial (g : EncodedGraph.Graph) (originalN : ℕ) :
    afterDoubleHost g originalN =
      BitMachineStackEmbedding.cfg shiftStack
        (afterDoubleHost g originalN).stk Sum.inr shiftControl none
        (shiftInitialCfg g originalN) := by
  have hb := BitMachineStackEmbedding.bank_eq_self shiftStack
    (afterDoubleHost g originalN).stk (shiftInitialCfg g originalN).stk
    (shift_initial_stacks g originalN)
  change (⟨some (.inr SourceNormalizationMachineShiftCopies.Phase.peek),
    decodeControl (SourceNormalizationMachineDecodeDouble.finalHost g originalN).var,
    (afterDoubleHost g originalN).stk⟩ : Config) =
    (⟨some (.inr SourceNormalizationMachineShiftCopies.Phase.peek),
      shiftControl (shiftInitialCfg g originalN).var,
      BitMachineStackEmbedding.bank shiftStack
        (afterDoubleHost g originalN).stk (shiftInitialCfg g originalN).stk⟩ : Config)
  rw [hb]
  rfl

/-- The single finite machine now parses and normalizes support, retains the
original SAT n, makes exactly the prescribed copies, and emits the exact
copy-major unary endpoint stream of the numeric normalized graph. -/
theorem decode_shift_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecodeDouble.rankBound g originalN +
      2 * (g.edges.length + 1) + 2 + shiftCost g originalN,
      run t (start (EncodedGraph.encode g) originalN) =
        BitMachineStackEmbedding.cfg shiftStack
          (afterDoubleHost g originalN).stk Sum.inr shiftControl none
          (shiftFinalCfg g originalN) := by
  obtain ⟨a,ha,hdouble⟩ := double_stage g hg originalN
  have hcopies : 0 < copies g originalN := by
    exact ParameterizedNP.GuardedSourceGraph.copyCount_pos
      originalN g.edges.length
  obtain ⟨b,hb,hshift⟩ :=
    SourceNormalizationMachineShiftCopies.copies_run
      (localIndices g) (localIndices_ne_nil g)
      (localBits g) (copies g originalN) 0 hcopies []
  have hshift' : SourceNormalizationMachineShiftCopies.run b
      (shiftInitialCfg g originalN) = shiftFinalCfg g originalN := by
    simpa only [shiftInitialCfg, shiftFinalCfg, Nat.zero_add,
      List.replicate_zero, List.append_nil] using hshift
  obtain ⟨c,hc,hr⟩ := BitMachineStackEmbedding.outputs shiftStack
    (afterDoubleHost g originalN).stk Sum.inr shiftControl Prod.snd
    (by intro v; rfl) none
    SourceNormalizationMachineShiftCopies.program program shift_program_eq
    (shiftInitialCfg g originalN) b (by
      change (SourceNormalizationMachineShiftCopies.run b
        (shiftInitialCfg g originalN)).l = none
      rw [hshift']
      rfl)
  change ((advance SourceNormalizationMachineShiftCopies.program)^[b]) _ = _ at hshift'
  rw [hshift'] at hr
  refine ⟨a + c, by simpa only [shiftCost] using
    (show a + c ≤ SourceNormalizationMachineDecodeDouble.rankBound g originalN +
      2 * (g.edges.length + 1) + 2 +
      (SourceNormalizationMachineShiftCopies.copiesCost
        (localIndices g) (localBits g) 0 (copies g originalN) +
        (SourceNormalizationMachineShiftCopies.shiftedFrom
          (localIndices g) ((localBits g).count true) 0
          (copies g originalN)).length + 2) by omega), ?_⟩
  exact (run_add hdouble c).trans
    ((congrArg (run c) (shift_initial g originalN)).trans
      (by simpa only [run] using hr))

theorem shifted_output_eq_numeric (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    (shiftFinalCfg g originalN).stk (4 : SourceNormalizationMachineShiftCopies.Stack) =
      SourceNormalizationMachineMark.endpointStream
        (SourceNormalizationNumeric.endpoints
          (SourceNormalizationNumeric.numericGraph g originalN)) := by
  exact shifted_eq_numeric g hg originalN

end EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeShift
