import Paper2.YaoSelectorReverse
import Paper2.YaoPayloadLoop
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-! One fixed finite-control Yao entry controller. Three already-checked
machine bodies share physical banks: selector gathering, strided payload
gathering, and binary indexed lookup. The bank permutations below are
static, with no input-dependent host transfer. -/

namespace Paper2.YaoEntryComposition

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.BitMachineSubroutine
open EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming
open Paper2.YaoLowerBound Paper2.YaoLowerBound.Materialization Paper2.YaoLookup

abbrev SelectorLabel := MatrixWordGather.Label
abbrev PayloadLabel := Paper2.YaoPayloadLoop.Label
abbrev QueryLabel := MatrixTemplateMachine.Label
abbrev Label := SelectorLabel ⊕ (PayloadLabel ⊕ QueryLabel)
abbrev Control := MatrixWordGather.Control ×
  (Paper2.YaoPayloadLoop.Control × MatrixTemplateMachine.Control)
abbrev Config := TM2.Cfg (fun _ : Fin 13 => Bool) Label Control

def selectorBank : ((Fin 7 ⊕ Fin 1) ⊕ Fin 5) ≃ Fin 13 :=
  (((finSumFinEquiv : Fin 7 ⊕ Fin 1 ≃ Fin 8).sumCongr
    (Equiv.refl (Fin 5))).trans finSumFinEquiv)

private def payloadPerm : Fin 13 ≃ Fin 13 where
  toFun i := ![8,1,2,3,4,6,7,10,9,12,11,0,5] i
  invFun i := ![11,1,2,3,4,12,5,6,0,8,7,10,9] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def payloadBank : (Paper2.YaoPayloadLoop.Stack ⊕ Fin 2) ≃ Fin 13 :=
  (((((finSumFinEquiv : Fin 7 ⊕ Fin 3 ≃ Fin 10).sumCongr
      (Equiv.refl (Fin 1))).trans finSumFinEquiv).sumCongr
      (Equiv.refl (Fin 2))).trans finSumFinEquiv).trans payloadPerm

private def queryPerm : Fin 13 ≃ Fin 13 where
  toFun i := ![5,6,7,11,12,0,1,2,3,4,8,9,10] i
  invFun i := ![5,6,7,8,9,0,1,2,10,11,12,3,4] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def queryBank : (MatrixTemplateMachine.Stack ⊕ Fin 8) ≃ Fin 13 :=
  ((((finSumFinEquiv : Fin 3 ⊕ Fin 2 ≃ Fin 5).sumCongr
      (Equiv.refl (Fin 8))).trans finSumFinEquiv).trans queryPerm)

def payloadLabels : PayloadLabel ⊕ (SelectorLabel ⊕ QueryLabel) ≃ Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def payloadControls :
    Paper2.YaoPayloadLoop.Control × (MatrixWordGather.Control × MatrixTemplateMachine.Control)
      ≃ Control where
  toFun s := (s.2.1, (s.1, s.2.2))
  invFun s := (s.2.1, (s.1, s.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def queryLabels : QueryLabel ⊕ (SelectorLabel ⊕ PayloadLabel) ≃ Label where
  toFun
    | .inl l => .inr (.inr l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inl l)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr l)
    | .inr (.inr l) => .inl l
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def queryControls :
    MatrixTemplateMachine.Control × (MatrixWordGather.Control × Paper2.YaoPayloadLoop.Control)
      ≃ Control where
  toFun s := (s.2.1, (s.2.2, s.1))
  invFun s := (s.2.2, (s.1, s.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def program : Label → TM2.Stmt (fun _ : Fin 13 => Bool) Label Control
  | .inl l => renameStmt selectorBank (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl (.inl (.inr .test)))) (MatrixWordGather.program l))
  | .inr (.inl l) => renameStmt payloadBank payloadLabels payloadControls
      (liftStmt (some (.inr (.inl .readBit))) (Paper2.YaoPayloadLoop.program l))
  | .inr (.inr l) => renameStmt queryBank queryLabels queryControls
      (liftStmt none (MatrixTemplateMachine.program l))

def cfg (label : Option Label) (s : Control)
    (sindex source selector countS pindex stride countP payload answer : List Bool) : Config :=
  ⟨label, s, ![sindex,[],[],source,[],selector,[],countS,pindex,stride,countP,payload,answer]⟩

def initialControl : Control :=
  ((MatrixWordGather.baseControl, false),
    ((MatrixStrideGather.baseControl, false), none),
      ((false,false),(false,false)))

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def selectorFrame (pindex stride countP payload answer : List Bool)
    (c : MatrixWordGather.Config) : Config :=
  renameCfg selectorBank (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl (.inl (.inr .test))))
      (((MatrixStrideGather.baseControl, false), none),
        ((false,false),(false,false)))
      (fun i : Fin 5 => ![pindex,stride,countP,payload,answer] i) c)

private theorem selector_input (start width : ℕ) (source pindex stride countP : List Bool) :
    selectorFrame pindex stride countP [] []
      (MatrixWordGather.cfg (some (.inr false)) false
        (List.replicate start true) source [] (List.replicate width true)) =
      cfg (some (.inl (.inr false))) initialControl
        (List.replicate start true) source [] (List.replicate width true)
        pindex stride countP [] [] := by
  apply congrArg (fun S =>
    (⟨some (.inl (.inr false)), initialControl, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem selector_output (endIndex : ℕ) (source selector pindex stride countP : List Bool) :
    selectorFrame pindex stride countP [] []
      (MatrixWordGather.cfg none false (List.replicate endIndex true)
        source selector []) =
      cfg (some (.inr (.inl (.inl (.inr .test))))) initialControl
        (List.replicate endIndex true) source selector []
        pindex stride countP [] [] := by
  apply congrArg (fun S =>
    (⟨some (.inr (.inl (.inl (.inr .test)))), initialControl, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem selector_stage (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1)))
    (pindex stride countP : List Bool) :
    ∃ steps ≤ b *
        (3 * (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g + b) +
          3 * bits.val.length + 10) + 1,
      run steps (cfg (some (.inl (.inr false))) initialControl
        (List.replicate (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g) true)
        bits.val [] (List.replicate b true) pindex stride countP [] []) =
      cfg (some (.inr (.inl (.inl (.inr .test))))) initialControl
        (List.replicate (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g + b) true)
        bits.val (Paper2.YaoPhysicalSlice.selectorWord t b lambda bits z g) []
        pindex stride countP [] [] := by
  obtain ⟨k, hk, hr⟩ := physical_selector_word t b lambda bits z g
  have hh : (((advance MatrixWordGather.program)^[k])
      (MatrixWordGather.cfg (some (.inr false)) false
        (List.replicate (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g) true)
        bits.val [] (List.replicate b true))).l = none := by
    change (MatrixWordGather.run k _).l = none
    rw [hr]; rfl
  obtain ⟨steps, hsteps, hrun⟩ := lift_outputs_renamed selectorBank
    (Equiv.refl _) (Equiv.refl _) MatrixWordGather.program program
    (some (.inl (.inl (.inr .test)))) (fun _ => rfl)
    (((MatrixStrideGather.baseControl, false), none),
      ((false,false),(false,false)))
    (fun i : Fin 5 => ![pindex,stride,countP,[],[]] i)
    (MatrixWordGather.cfg (some (.inr false)) false
      (List.replicate (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g) true)
      bits.val [] (List.replicate b true)) k hh
  change run steps (selectorFrame pindex stride countP [] [] _) =
    selectorFrame pindex stride countP [] [] _ at hrun
  change (((advance MatrixWordGather.program)^[k]) _) = _ at hr
  rw [hr, selector_input, selector_output] at hrun
  exact ⟨steps, hsteps.trans hk, hrun⟩

def payloadFrame (sindex selector : List Bool)
    (c : Paper2.YaoPayloadLoop.Config) : Config :=
  renameCfg payloadBank payloadLabels payloadControls
    (liftCfg (some (.inr (.inl .readBit)))
      ((MatrixWordGather.baseControl, false), ((false,false),(false,false)))
      (fun i : Fin 2 => ![sindex,selector] i) c)

private theorem payload_input (sindex selector : List Bool)
    (base count stride : ℕ) (source : List Bool) :
    payloadFrame sindex selector
      (Paper2.YaoPayloadLoop.cfg (some (.inl (.inr .test))) false none
        (List.replicate base true) source []
        (List.replicate count true) (List.replicate stride true) [] []) =
      cfg (some (.inr (.inl (.inl (.inr .test))))) initialControl
        sindex source selector [] (List.replicate base true)
        (List.replicate stride true) (List.replicate count true) [] [] := by
  apply congrArg (fun S =>
    (⟨some (.inr (.inl (.inl (.inr .test)))), initialControl, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem payload_output (sindex selector : List Bool)
    (finalIndex stride : ℕ) (source payload : List Bool) :
    payloadFrame sindex selector
      (Paper2.YaoPayloadLoop.cfg none false none
        (List.replicate finalIndex true) source [] []
        (List.replicate stride true) [] payload) =
      cfg (some (.inr (.inr (.inl .readBit)))) initialControl
        sindex source selector [] (List.replicate finalIndex true)
        (List.replicate stride true) [] payload [] := by
  apply congrArg (fun S =>
    (⟨some (.inr (.inr (.inl .readBit))), initialControl, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem payload_stage (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1))
    (sindex selector : List Bool) :
    ∃ steps ≤ (2 ^ b) *
        (3 * (Paper2.YaoPayloadLoop.payloadBase t b lambda l p +
          (2 ^ b) * Paper2.YaoPayloadLoop.payloadStride t) +
          3 * bits.val.length + 2 * Paper2.YaoPayloadLoop.payloadStride t + 12) +
        1 + ((2 ^ b) + 1),
      run steps (cfg (some (.inr (.inl (.inl (.inr .test))))) initialControl
        sindex bits.val selector []
        (List.replicate (Paper2.YaoPayloadLoop.payloadBase t b lambda l p) true)
        (List.replicate (Paper2.YaoPayloadLoop.payloadStride t) true)
        (List.replicate (2 ^ b) true) [] []) =
      cfg (some (.inr (.inr (.inl .readBit)))) initialControl
        sindex bits.val selector []
        (List.replicate (Paper2.YaoPayloadLoop.payloadBase t b lambda l p +
          (2 ^ b) * Paper2.YaoPayloadLoop.payloadStride t) true)
        (List.replicate (Paper2.YaoPayloadLoop.payloadStride t) true) []
        (Paper2.YaoPhysicalSlice.payloadSlice t b lambda bits l p) [] := by
  obtain ⟨k, hk, hr⟩ :=
    Paper2.YaoPayloadLoop.physical_prior_payload_slice t b lambda bits l p
  have hh : (((advance Paper2.YaoPayloadLoop.program)^[k])
      (Paper2.YaoPayloadLoop.cfg (some (.inl (.inr .test))) false none
        (List.replicate (Paper2.YaoPayloadLoop.payloadBase t b lambda l p) true)
        bits.val [] (List.replicate (2 ^ b) true)
        (List.replicate (Paper2.YaoPayloadLoop.payloadStride t) true) [] [])).l = none := by
    change (Paper2.YaoPayloadLoop.run k _).l = none
    rw [hr]; rfl
  obtain ⟨steps, hsteps, hrun⟩ := lift_outputs_renamed payloadBank
    payloadLabels payloadControls Paper2.YaoPayloadLoop.program program
    (some (.inr (.inl .readBit))) (fun _ => rfl)
    ((MatrixWordGather.baseControl, false), ((false,false),(false,false)))
    (fun i : Fin 2 => ![sindex,selector] i)
    (Paper2.YaoPayloadLoop.cfg (some (.inl (.inr .test))) false none
      (List.replicate (Paper2.YaoPayloadLoop.payloadBase t b lambda l p) true)
      bits.val [] (List.replicate (2 ^ b) true)
      (List.replicate (Paper2.YaoPayloadLoop.payloadStride t) true) [] []) k hh
  change run steps (payloadFrame sindex selector _) =
    payloadFrame sindex selector _ at hrun
  change (((advance Paper2.YaoPayloadLoop.program)^[k]) _) = _ at hr
  rw [hr, payload_input, payload_output] at hrun
  exact ⟨steps, hsteps.trans hk, hrun⟩

def queryFrame (sindex source pindex stride : List Bool)
    (c : MatrixTemplateMachine.Config) : Config :=
  renameCfg queryBank queryLabels queryControls
    (liftCfg none
      ((MatrixWordGather.baseControl, false),
        ((MatrixStrideGather.baseControl, false), none))
      (fun i : Fin 8 => ![sindex,[],[],source,[],pindex,stride,[]] i) c)

private theorem query_input (sindex source pindex stride bits row : List Bool) :
    queryFrame sindex source pindex stride
      (MatrixTemplateMachine.initial bits row []) =
      cfg (some (.inr (.inr (.inl .readBit)))) initialControl
        sindex source bits [] pindex stride [] row [] := by
  apply congrArg (fun S =>
    (⟨some (.inr (.inr (.inl .readBit))), initialControl, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem query_output (sindex source pindex stride : List Bool) (answer : Bool) :
    queryFrame sindex source pindex stride
      (MatrixTemplateMachine.cfg none ((false,false),(false,false)) [] [] [answer]) =
      cfg none initialControl sindex source [] [] pindex stride [] [] [answer] := by
  apply congrArg (fun S =>
    (⟨none, initialControl, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem query_stage {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v) (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda))
    (sindex pindex stride : List Bool) :
    ∃ steps ≤ 6 * paddedEdgeCount e + 3 * paddedEdgeBits e + 6,
      run steps (cfg (some (.inr (.inr (.inl .readBit)))) initialControl
        sindex bits.val (Paper2.YaoPhysicalSlice.selectorWord t (paddedEdgeBits e) lambda bits z g)
        [] pindex stride []
        (Paper2.YaoPhysicalSlice.payloadSlice t (paddedEdgeBits e) lambda bits l
          (positionEval (paddedEdgesEval edges) a vertex)) []) =
      cfg none initialControl sindex bits.val [] [] pindex stride [] []
        [matrixFromTape t lambda edges
          (readTape t (paddedEdgeBits e) lambda bits) (vertex,z) (g,a,l)] := by
  obtain ⟨k, hk, hr⟩ := Paper2.YaoPhysicalSlice.physical_matrix_entry
    t lambda edges bits vertex z g a l []
  have hh : (((advance MatrixTemplateMachine.program)^[k])
      (MatrixTemplateMachine.initial
        (Paper2.YaoPhysicalSlice.selectorWord t (paddedEdgeBits e) lambda bits z g)
        (Paper2.YaoPhysicalSlice.payloadSlice t (paddedEdgeBits e) lambda bits l
          (positionEval (paddedEdgesEval edges) a vertex)) [])).l = none := by
    change (MatrixTemplateMachine.run k _).l = none
    rw [hr]; rfl
  obtain ⟨steps, hsteps, hrun⟩ := lift_outputs_renamed queryBank
    queryLabels queryControls MatrixTemplateMachine.program program none
    (fun _ => rfl)
    ((MatrixWordGather.baseControl, false),
      ((MatrixStrideGather.baseControl, false), none))
    (fun i : Fin 8 => ![sindex,[],[],bits.val,[],pindex,stride,[]] i)
    (MatrixTemplateMachine.initial
      (Paper2.YaoPhysicalSlice.selectorWord t (paddedEdgeBits e) lambda bits z g)
      (Paper2.YaoPhysicalSlice.payloadSlice t (paddedEdgeBits e) lambda bits l
        (positionEval (paddedEdgesEval edges) a vertex)) []) k hh
  change run steps (queryFrame sindex bits.val pindex stride _) =
    queryFrame sindex bits.val pindex stride _ at hrun
  change (((advance MatrixTemplateMachine.program)^[k]) _) = _ at hr
  rw [hr, query_input, query_output] at hrun
  exact ⟨steps, hsteps.trans hk, hrun⟩

def selectorBudget (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) : ℕ :=
  b * (3 * (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g + b) +
    3 * bits.val.length + 10) + 1

def payloadBudget (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) : ℕ :=
  (2 ^ b) * (3 * (Paper2.YaoPayloadLoop.payloadBase t b lambda l p +
    (2 ^ b) * Paper2.YaoPayloadLoop.payloadStride t) +
    3 * bits.val.length + 2 * Paper2.YaoPayloadLoop.payloadStride t + 12) +
    1 + ((2 ^ b) + 1)

def entryInput {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v) (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda)) : Config :=
  let b := paddedEdgeBits e
  let p := positionEval (paddedEdgesEval edges) a vertex
  cfg (some (.inl (.inr false))) initialControl
    (List.replicate (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g) true)
    bits.val [] (List.replicate b true)
    (List.replicate (Paper2.YaoPayloadLoop.payloadBase t b lambda l p) true)
    (List.replicate (Paper2.YaoPayloadLoop.payloadStride t) true)
    (List.replicate (2 ^ b) true) [] []

def entryFinal {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v) (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda)) : Config :=
  let b := paddedEdgeBits e
  let p := positionEval (paddedEdgesEval edges) a vertex
  cfg none initialControl
    (List.replicate (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g + b) true)
    bits.val [] []
    (List.replicate (Paper2.YaoPayloadLoop.payloadBase t b lambda l p +
      (2 ^ b) * Paper2.YaoPayloadLoop.payloadStride t) true)
    (List.replicate (Paper2.YaoPayloadLoop.payloadStride t) true)
    [] []
    [matrixFromTape t lambda edges (readTape t b lambda bits)
      (vertex,z) (g,a,l)]

/-- One fixed finite-control 13-stack machine, on the *same literal flat
tape*, executes selector gather/reversal, forward strided payload gather,
then binary decoded lookup. All inter-stage banks align physically; the
proof applies no host-level list transfer between stages. The only
supplied input scalars are unary selector offset/count and payload
base/stride/count, and the typed edge position used to specify that base.
Their production from encoded labels is a separate obligation. -/
theorem physical_entry_combined {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v) (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda)) :
    ∃ steps ≤ selectorBudget t (paddedEdgeBits e) lambda bits z g +
      payloadBudget t (paddedEdgeBits e) lambda bits l
        (positionEval (paddedEdgesEval edges) a vertex) +
      (6 * paddedEdgeCount e + 3 * paddedEdgeBits e + 6),
      run steps (entryInput t lambda edges bits vertex z g a l) =
        entryFinal t lambda edges bits vertex z g a l := by
  let b := paddedEdgeBits e
  let p := positionEval (paddedEdgesEval edges) a vertex
  let sEnd := List.replicate
    (Paper2.YaoPreservedFlatSlice.selectorOffset t b lambda z g + b) true
  let pEnd := List.replicate
    (Paper2.YaoPayloadLoop.payloadBase t b lambda l p +
      (2 ^ b) * Paper2.YaoPayloadLoop.payloadStride t) true
  let stride := List.replicate (Paper2.YaoPayloadLoop.payloadStride t) true
  obtain ⟨ts, hts, hs⟩ := selector_stage t b lambda bits z g
    (List.replicate (Paper2.YaoPayloadLoop.payloadBase t b lambda l p) true)
    stride (List.replicate (2 ^ b) true)
  obtain ⟨tp, htp, hp⟩ := payload_stage t b lambda bits l p sEnd
    (Paper2.YaoPhysicalSlice.selectorWord t b lambda bits z g)
  obtain ⟨tq, htq, hq⟩ := query_stage t lambda edges bits vertex z g a l
    sEnd pEnd stride
  refine ⟨ts + tp + tq, ?_, ?_⟩
  · have hsel : ts ≤ selectorBudget t (paddedEdgeBits e) lambda bits z g := by
      simpa [selectorBudget, b] using hts
    have hpay : tp ≤ payloadBudget t (paddedEdgeBits e) lambda bits l
        (positionEval (paddedEdgesEval edges) a vertex) := by
      simpa [payloadBudget, b, p] using htp
    omega
  · change run (ts + tp + tq) (entryInput t lambda edges bits vertex z g a l) =
      entryFinal t lambda edges bits vertex z g a l
    have hs' := hs
    change run ts (entryInput t lambda edges bits vertex z g a l) = _ at hs'
    have h12 := run_add hs' tp
    rw [hp] at h12
    have h123 := run_add h12 tq
    rw [hq] at h123
    simpa [entryFinal, Nat.add_assoc, b, p, sEnd, pEnd, stride] using h123

#print axioms physical_entry_combined

end Paper2.YaoEntryComposition
