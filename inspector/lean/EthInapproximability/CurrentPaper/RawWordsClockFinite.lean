import EthInapproximability.CurrentPaper.RawWordsClockPoly

/-! # Segment 2 (caveat C1): finite packaging of the raw-word program

The frozen bank `Global = Cons ⊕ Aux` is infinite because of `Aux.nat r i`
(`i : ℕ`). A fixed program nevertheless names only finitely many cells: its
label type is finite and each statement is a finite tree. We restrict to the
referenced cells (plus the input cell), a `Finset` of `Global` fixed by the
program parameters `M, c` alone, and pull every statement back along the
retraction onto that subtype. Embedding the pulled-back program again gives
back the literal program (`stackStmt_restrict`), so the production
`BitMachineStackRun.run` transfers every run of the infinite-bank program to
the finite one with the same step count and the restricted bank. The finite
program is then a `BitMachine.Machine` through `BitMachineEncoding.ofFinite`.
This is a renaming of finitely many stack names, not a new instruction. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWordsClock

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.WeightedRawWords

noncomputable section

/-! ## Referenced stacks and pull-back along a retraction (generic) -/

section Generic

variable {K J L V : Type*} [DecidableEq K]

/-- The stacks named by one statement. -/
def refs : TM2.Stmt (fun _ : K => Bool) L V → Finset K
  | .push k _ q => insert k (refs q)
  | .peek k _ q => insert k (refs q)
  | .pop k _ q => insert k (refs q)
  | .load _ q => refs q
  | .branch _ q r => refs q ∪ refs r
  | .goto _ => ∅
  | .halt => ∅

/-- Rename every stack of a statement through `r`. -/
def pullStmt (r : K → J) : TM2.Stmt (fun _ : K => Bool) L V → TM2.Stmt (fun _ : J => Bool) L V
  | .push k f q => .push (r k) f (pullStmt r q)
  | .peek k f q => .peek (r k) f (pullStmt r q)
  | .pop k f q => .pop (r k) f (pullStmt r q)
  | .load f q => .load f (pullStmt r q)
  | .branch f q q' => .branch f (pullStmt r q) (pullStmt r q')
  | .goto f => .goto f
  | .halt => .halt

theorem stackStmt_pull [DecidableEq J] (e : J ↪ K) (r : K → J)
    (q : TM2.Stmt (fun _ : K => Bool) L V) (h : ∀ k ∈ refs q, e (r k) = k) :
    stackStmt e (pullStmt r q) = q := by
  induction q with
  | push k f q ih =>
      simp only [refs, Finset.mem_insert] at h
      simp only [pullStmt, stackStmt, h k (Or.inl rfl), ih (fun j hj => h j (Or.inr hj))]
  | peek k f q ih =>
      simp only [refs, Finset.mem_insert] at h
      simp only [pullStmt, stackStmt, h k (Or.inl rfl), ih (fun j hj => h j (Or.inr hj))]
  | pop k f q ih =>
      simp only [refs, Finset.mem_insert] at h
      simp only [pullStmt, stackStmt, h k (Or.inl rfl), ih (fun j hj => h j (Or.inr hj))]
  | load f q ih =>
      simp only [refs] at h
      simp only [pullStmt, stackStmt, ih h]
  | branch f q q' ih ih' =>
      simp only [refs, Finset.mem_union] at h
      simp only [pullStmt, stackStmt, ih (fun j hj => h j (Or.inl hj)),
        ih' (fun j hj => h j (Or.inr hj))]
  | goto f => rfl
  | halt => rfl

variable [Fintype L]

/-- The finite support of a program: the input cell and every referenced cell. -/
def support (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 : K) : Finset K :=
  insert i0 (Finset.univ.biUnion fun l => refs (P l))

/-- The finite stack type of the restricted program. -/
abbrev Cell (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 : K) : Type _ :=
  {k : K // k ∈ support P i0}

def baseCell (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 : K) : Cell P i0 :=
  ⟨i0, Finset.mem_insert_self _ _⟩

def retract (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 : K) (k : K) : Cell P i0 :=
  if h : k ∈ support P i0 then ⟨k, h⟩ else baseCell P i0

def cellEmb (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 : K) : Cell P i0 ↪ K :=
  Function.Embedding.subtype _

/-- The same program with its stacks renamed into the finite support. -/
def restrict (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 : K) :
    L → TM2.Stmt (fun _ : Cell P i0 => Bool) L V :=
  fun l => pullStmt (retract P i0) (P l)

theorem stackStmt_restrict (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 : K) (l : L) :
    stackStmt (cellEmb P i0) (restrict P i0 l) = P l := by
  apply stackStmt_pull
  intro k hk
  have hm : k ∈ support P i0 :=
    Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, hk⟩)
  simp [retract, hm, cellEmb]

/-- Every run of the literal program is a run of the restricted program with
the same step count, the same labels and controls, and the restricted bank. -/
theorem restrict_run (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 : K)
    (l0 l1 : Option L) (v0 v1 : V) (G B : K → List Bool) (t : ℕ)
    (h : ((advance P)^[t]) (⟨l0, v0, G⟩ : TM2.Cfg (fun _ : K => Bool) L V) = ⟨l1, v1, B⟩) :
    ((advance (restrict P i0))^[t])
        (⟨l0, v0, fun x => G x.val⟩ : TM2.Cfg (fun _ : Cell P i0 => Bool) L V) =
      ⟨l1, v1, fun x => B x.val⟩ := by
  have hP : (fun l => stackStmt (cellEmb P i0) (restrict P i0 l)) = P :=
    funext (stackStmt_restrict P i0)
  have hr := BitMachineStackRun.run (cellEmb P i0) G (restrict P i0)
    (⟨l0, v0, fun x => G x.val⟩ : TM2.Cfg (fun _ : Cell P i0 => Bool) L V) t
  rw [hP] at hr
  have hs : stackCfg (cellEmb P i0) G
      (⟨l0, v0, fun x => G x.val⟩ : TM2.Cfg (fun _ : Cell P i0 => Bool) L V) = ⟨l0, v0, G⟩ := by
    unfold stackCfg
    exact congrArg _ (bank_restrict (cellEmb P i0) G)
  rw [hs, h] at hr
  generalize hc : ((advance (restrict P i0))^[t])
    (⟨l0, v0, fun x => G x.val⟩ : TM2.Cfg (fun _ : Cell P i0 => Bool) L V) = c at hr
  rcases c with ⟨cl, cv, cS⟩
  unfold stackCfg at hr
  simp only [TM2.Cfg.mk.injEq] at hr
  obtain ⟨h1, h2, h3⟩ := hr
  subst h1 h2
  congr 1
  funext x
  rw [h3]
  exact (bank_at (cellEmb P i0) G cS x).symm

end Generic

/-! ## The raw-word program as a finite `BitMachine.Machine` -/

/-- Reducible name for the label type of a program. -/
abbrev LabelOf {K L V : Type*} (_P : L → TM2.Stmt (fun _ : K => Bool) L V) : Type _ := L
/-- Reducible name for the control type of a program. -/
abbrev CtrlOf {K L V : Type*} (_P : L → TM2.Stmt (fun _ : K => Bool) L V) : Type _ := V

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 100000 in
/-- The label type of `rawWordsKProgram M c` is finite (a fixed nested sum).
Irreducible: only its identity matters, never its evaluation. -/
@[irreducible] noncomputable def rawLabelFintype (M : BitMachine.Machine) (c : ℕ) :
    Fintype (LabelOf (rawWordsKProgram M c)) := by
  unfold LabelOf
  infer_instance

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 100000 in
/-- The control type of `rawWordsKProgram M c` is finite (a fixed nested product).
Irreducible: only its identity matters, never its evaluation. -/
@[irreducible] noncomputable def rawCtrlFintype (M : BitMachine.Machine) (c : ℕ) :
    Fintype (CtrlOf (rawWordsKProgram M c)) := by
  unfold CtrlOf
  infer_instance

variable (M : BitMachine.Machine) (c : ℕ)

/-- The finite set of referenced cells of the fixed program; it depends on
`M` and `c` only. -/
def rawSupport : Finset Global :=
  @support Global _ _ _ (rawLabelFintype M c) (rawWordsKProgram M c) (aux .input)

/-- The finite stack type of the packaged machine. -/
abbrev RawCell : Type := {x : Global // x ∈ rawSupport M c}

@[irreducible] noncomputable def rawCellFintype : Fintype (RawCell M c) :=
  Finset.Subtype.fintype _

def rawInputCell : RawCell M c := ⟨aux .input, Finset.mem_insert_self _ _⟩

/-- The restricted fixed program on the finite stack type. -/
def rawFinProgram : LabelOf (rawWordsKProgram M c) →
    TM2.Stmt (fun _ : RawCell M c => Bool) (LabelOf (rawWordsKProgram M c))
      (CtrlOf (rawWordsKProgram M c)) :=
  @restrict Global _ _ _ (rawLabelFintype M c) (rawWordsKProgram M c) (aux .input)

def rawStartLabel : LabelOf (rawWordsKProgram M c) :=
  BitMachineRawSequence.leftLabel (.inl (.scan 0))

def rawInitialCtrl : CtrlOf (rawWordsKProgram M c) :=
  (none, ((), ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M)))

/-- The three fixed finite renamings used by `ofFinite`. -/
noncomputable def ekRaw : RawCell M c ≃ Fin (@Fintype.card _ (rawCellFintype M c)) :=
  @Fintype.equivFin _ (rawCellFintype M c)
noncomputable def elRaw : LabelOf (rawWordsKProgram M c) ≃
    Fin (@Fintype.card _ (rawLabelFintype M c)) :=
  @Fintype.equivFin _ (rawLabelFintype M c)
noncomputable def evRaw : CtrlOf (rawWordsKProgram M c) ≃
    Fin (@Fintype.card _ (rawCtrlFintype M c)) :=
  @Fintype.equivFin _ (rawCtrlFintype M c)

/-- The fixed raw-word program as one finite Boolean-stack machine. The
input stack is the packet cell; `out` is any referenced cell chosen as the
designated output (the run theorems below state the whole final bank). -/
noncomputable def rawWordsMachine (out : RawCell M c) : BitMachine.Machine :=
  @BitMachineEncoding.ofFinite (RawCell M c) (LabelOf (rawWordsKProgram M c))
    (CtrlOf (rawWordsKProgram M c)) (rawCellFintype M c) (rawLabelFintype M c)
    (rawCtrlFintype M c) (rawInputCell M c) out (rawStartLabel M c) (rawInitialCtrl M c)
    (rawFinProgram M c)

theorem rawWordsMachine_stackCount (out : RawCell M c) :
    (rawWordsMachine M c out).stackCount = @Fintype.card _ (rawCellFintype M c) := rfl

/-- The renamed configuration of the restricted program, as a machine configuration. -/
noncomputable def rawCfg (out : RawCell M c)
    (x : TM2.Cfg (fun _ : RawCell M c => Bool) (LabelOf (rawWordsKProgram M c))
      (CtrlOf (rawWordsKProgram M c))) : (rawWordsMachine M c out).Config :=
  renameCfg (ekRaw M c) (elRaw M c) (evRaw M c) x

/-- The machine's initial configuration is the renamed restricted start. -/
theorem rawWordsMachine_init (out : RawCell M c) (bits : List Bool) :
    (rawWordsMachine M c out).init bits =
      rawCfg M c out ⟨some (rawStartLabel M c), rawInitialCtrl M c, fun x => startBank bits x.val⟩ := by
  have h := @ofFinite_init (RawCell M c) (LabelOf (rawWordsKProgram M c))
    (CtrlOf (rawWordsKProgram M c)) (rawCellFintype M c) (rawLabelFintype M c)
    (rawCtrlFintype M c) _ (rawInputCell M c) out (rawStartLabel M c) (rawInitialCtrl M c)
    (rawFinProgram M c) bits
  refine h.trans ?_
  unfold rawCfg rawInit
  congr 2
  funext x
  by_cases hx : x = rawInputCell M c
  · subst hx
    simp [rawInputCell, startBank]
  · have hv : x.val ≠ aux .input := by
      intro h
      apply hx
      exact Subtype.ext h
    rw [if_neg hx]
    simp [startBank, hv]

/-- The whole-bank run of the raw program transfers to the machine. -/
theorem rawWordsMachine_run_of (out : RawCell M c) (bits : List Bool) (t : ℕ)
    (v1 : CtrlOf (rawWordsKProgram M c)) (B : Global → List Bool)
    (h : ((advance (rawWordsKProgram M c))^[t])
      (⟨some (rawStartLabel M c), rawInitialCtrl M c, startBank bits⟩ :
        TM2.Cfg (fun _ : Global => Bool) (LabelOf (rawWordsKProgram M c))
          (CtrlOf (rawWordsKProgram M c))) = ⟨none, v1, B⟩) :
    (rawWordsMachine M c out).run t ((rawWordsMachine M c out).init bits) =
      rawCfg M c out ⟨none, v1, fun x => B x.val⟩ := by
  have hr := @restrict_run Global (LabelOf (rawWordsKProgram M c))
    (CtrlOf (rawWordsKProgram M c)) _ (rawLabelFintype M c) (rawWordsKProgram M c) (aux .input)
    _ _ _ _ _ _ t h
  rw [rawWordsMachine_init]
  have hrun := @ofFinite_run (RawCell M c) (LabelOf (rawWordsKProgram M c))
    (CtrlOf (rawWordsKProgram M c)) (rawCellFintype M c) (rawLabelFintype M c)
    (rawCtrlFintype M c) _ (rawInputCell M c) out (rawStartLabel M c) (rawInitialCtrl M c)
    (rawFinProgram M c)
    ⟨some (rawStartLabel M c), rawInitialCtrl M c, fun x => startBank bits x.val⟩ t
  refine hrun.trans ?_
  unfold rawCfg
  exact congrArg _ hr

/-- The level-0 exit bank of the frozen headline, as one function. -/
def exitK {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n : ℕ) : Global → List Bool :=
  Sum.elim
    (WeightedRawRowsSource.initialBank
      (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) 0)
      (EncodedETHSource.serializeGraph G) noW)
    (Function.update
      (masterBank n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)) c
        (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget
        (Fintype.card E))
      Aux.K (List.replicate (kValue M n) true))

/-- Segment 2 headline: the finite machine, started on the literal packet,
halts within the public polynomial clock with the whole restricted exit
bank of `level0_handoff_k` (renamed by the fixed finite equivalences). -/
theorem rawWordsMachine_run {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n : ℕ) (out : RawCell M c) :
    ∃ t ≤ rawC M c * (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ 128,
      (rawWordsMachine M c out).run t ((rawWordsMachine M c out).init
          (SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))) =
        rawCfg M c out ⟨none, (none, ((), ((level0Ctrl, (edgesCtrl, tailCtrl)), kCtrl M))),
            fun x => exitK M c G n x.val⟩ := by
  obtain ⟨t, ht, h⟩ := level0_handoff_k_poly M G n c
  exact ⟨t, ht, rawWordsMachine_run_of M c out
    (SourceOriginalBranchPackets.packet n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))) t _ _ h⟩

/-- `OutputsWithin` form for any designated output cell. -/
theorem rawWordsMachine_outputs {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n : ℕ)
    (out : RawCell M c) :
    (rawWordsMachine M c out).OutputsWithin
      (SourceOriginalBranchPackets.packet n
        (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))
      (exitK M c G n out.val)
      (rawC M c * (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ 128) := by
  obtain ⟨t, ht, h⟩ := rawWordsMachine_run M c G n out
  refine ⟨t, ht, ?_, ?_⟩
  · rw [h]
    rfl
  · rw [h]
    show (fun k => exitK M c G n ((ekRaw M c).symm k).val) ((ekRaw M c) out) = _
    simp only [Equiv.symm_apply_apply]

/-- The same machine statement with the clock in the input length (the
polynomial-time shape `C * (|input| + 1)^D`, `D = 128`). -/
theorem rawWordsMachine_outputs_input {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n : ℕ)
    (out : RawCell M c) :
    (rawWordsMachine M c out).OutputsWithin
      (SourceOriginalBranchPackets.packet n
        (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))
      (exitK M c G n out.val)
      (rawC M c * ((SourceOriginalBranchPackets.packet n
        (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ 128) := by
  obtain ⟨t, ht, h⟩ := level0_handoff_k_input_poly M G n c
  have hr := rawWordsMachine_run_of M c out
    (SourceOriginalBranchPackets.packet n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))) t _ _ h
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hr]
    rfl
  · rw [hr]
    show (fun k => exitK M c G n ((ekRaw M c).symm k).val) ((ekRaw M c) out) = _
    simp only [Equiv.symm_apply_apply]

#print axioms stackStmt_pull
#print axioms stackStmt_restrict
#print axioms restrict_run
#print axioms rawWordsMachine_init
#print axioms rawWordsMachine_run_of
#print axioms rawWordsMachine_run
#print axioms rawWordsMachine_outputs
#print axioms rawWordsMachine_outputs_input

end
end EthInapproximability.CurrentPaper.WeightedRawWordsClock
