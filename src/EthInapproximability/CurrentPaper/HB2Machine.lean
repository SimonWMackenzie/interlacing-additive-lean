import EthInapproximability.CurrentPaper.Emission
import EthInapproximability.CurrentPaper.RawWordsClockFinite

/-! Lane owner:b-weighted-level-10, unit 2, segment 3d-ii: the `BitMachine.Machine` wrapper and
`PhysicalLevelRun.HB2Physical`.

The bank `H7` is infinite (the frozen raw-word `Aux.nat r i`, `i : ℕ`), but the fixed program
`hb2Program` names only finitely many cells. As in the admitted `RawWordsClockFinite` (imported
here as the frozen private twin of `b-raw-words-clock-owner`, byte-identical modulo its import
line; the production module cannot be imported next to the bare raw-word chain), we restrict to the
referenced cells plus the input cell and the output cell `yc 8` (`supp2`), pull every statement back
with the admitted generic `WeightedRawWordsClock.pullStmt` / `stackStmt_pull`, and package the
restricted program with the admitted `BitMachineEncoding.ofFinite`. The designated output is the
emission cell `yc 8`. This is a renaming of finitely many stack names, not a new instruction.

`hb2_outputs`: the machine outputs exactly the `HB2Physical` word on the actual branch packet,
within `fuelShellBound + emitBound + 1` transitions.
`hb2_physical`: `PhysicalLevelRun.HB2Physical c A d Δ γ` for the ONE machine
`hb2Machine (actualMachine c A d) c W₀ w₀₀ v₀₀ W w₀ v₀`, from `hc : 1 ≤ c` and a per-instance premise
supplying the writer-22 specifications `hW₀`, `hW`, the round majorant `hT` and the public clock. -/

namespace EthInapproximability.CurrentPaper.HB2Machine

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Prep OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP StepP
open Level0Install
open RoundInstall (installProgram installCtrl)
open KShell (Bk)
open FuelShell Emission
open WeightedRawWordsClock (LabelOf CtrlOf refs pullStmt stackStmt_pull support)

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

/-! ## Restriction to a finite support containing the input and the output cell (generic) -/

section Generic

variable {K L V : Type*} [DecidableEq K] [Fintype L]

def supp2 (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 o : K) : Finset K :=
  insert o (support P i0)

abbrev Cell2 (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 o : K) : Type _ :=
  {k : K // k ∈ supp2 P i0 o}

def inCell2 (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 o : K) : Cell2 P i0 o :=
  ⟨i0, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩

def outCell2 (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 o : K) : Cell2 P i0 o :=
  ⟨o, Finset.mem_insert_self _ _⟩

def retract2 (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 o : K) (k : K) : Cell2 P i0 o :=
  if h : k ∈ supp2 P i0 o then ⟨k, h⟩ else inCell2 P i0 o

def emb2 (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 o : K) : Cell2 P i0 o ↪ K :=
  Function.Embedding.subtype _

def restrict2 (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 o : K) :
    L → TM2.Stmt (fun _ : Cell2 P i0 o => Bool) L V :=
  fun l => pullStmt (retract2 P i0 o) (P l)

theorem stackStmt_restrict2 (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 o : K) (l : L) :
    stackStmt (emb2 P i0 o) (restrict2 P i0 o l) = P l := by
  apply stackStmt_pull
  intro k hk
  have hm : k ∈ supp2 P i0 o :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, hk⟩))
  simp [retract2, hm, emb2]

/-- Every run of the literal program is a run of the restricted program with the same step
count, labels and controls, and the restricted bank (the proof of the admitted
`WeightedRawWordsClock.restrict_run`, for `supp2`). -/
theorem restrict2_run (P : L → TM2.Stmt (fun _ : K => Bool) L V) (i0 o : K)
    (l0 l1 : Option L) (v0 v1 : V) (G B : K → List Bool) (t : ℕ)
    (h : ((advance P)^[t]) (⟨l0, v0, G⟩ : TM2.Cfg (fun _ : K => Bool) L V) = ⟨l1, v1, B⟩) :
    ((advance (restrict2 P i0 o))^[t])
        (⟨l0, v0, fun x => G x.val⟩ : TM2.Cfg (fun _ : Cell2 P i0 o => Bool) L V) =
      ⟨l1, v1, fun x => B x.val⟩ := by
  have hP : (fun l => stackStmt (emb2 P i0 o) (restrict2 P i0 o l)) = P :=
    funext (stackStmt_restrict2 P i0 o)
  have hr := BitMachineStackRun.run (emb2 P i0 o) G (restrict2 P i0 o)
    (⟨l0, v0, fun x => G x.val⟩ : TM2.Cfg (fun _ : Cell2 P i0 o => Bool) L V) t
  rw [hP] at hr
  have hs : stackCfg (emb2 P i0 o) G
      (⟨l0, v0, fun x => G x.val⟩ : TM2.Cfg (fun _ : Cell2 P i0 o => Bool) L V) = ⟨l0, v0, G⟩ := by
    unfold stackCfg
    exact congrArg _ (bank_restrict (emb2 P i0 o) G)
  rw [hs, h] at hr
  generalize hc : ((advance (restrict2 P i0 o))^[t])
    (⟨l0, v0, fun x => G x.val⟩ : TM2.Cfg (fun _ : Cell2 P i0 o => Bool) L V) = c at hr
  rcases c with ⟨cl, cv, cS⟩
  unfold stackCfg at hr
  simp only [TM2.Cfg.mk.injEq] at hr
  obtain ⟨h1, h2, h3⟩ := hr
  subst h1 h2
  congr 1
  funext x
  rw [h3]
  exact (bank_at (emb2 P i0 o) G cS x).symm

end Generic

/-! ## The start bank is the packet alone -/

def inH7 : H7 := r7 (RoundInstall.mH .input)

theorem start_at (p : List Bool) :
    ext7 (ext6 (ext4 (H0 p) blank57) blank8) blank16 inH7 = p := by
  show ext4 (H0 p) blank57 (RoundInstall.mH .input) = p
  exact packet_cell p

theorem start_blank (p : List Bool) (k : H7) (hk : k ≠ inH7) :
    ext7 (ext6 (ext4 (H0 p) blank57) blank8) blank16 k = [] := by
  rcases k with ((((((x | x) | x) | x) | x) | x) | x)
  · rcases x with x | x | a
    · show WeightedRawWords.startBank p (Sum.inl x) = []
      simp [WeightedRawWords.startBank, WeightedRawWords.aux]
    · rfl
    · have ha : a ≠ .input := by
        rintro rfl
        exact hk rfl
      show WeightedRawWords.startBank p (Sum.inr a) = []
      simp [WeightedRawWords.startBank, WeightedRawWords.aux, ha]
  all_goals rfl

/-! ## The machine -/

variable (M : BitMachine.Machine)

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 200000 in
/-- The label type of `hb2Program` is finite (a fixed nested sum over finite label types). -/
@[irreducible] noncomputable def labFin [Fintype BStack] (c : ℕ) {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) :
    Fintype (LabelOf (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀)) := by
  unfold LabelOf
  infer_instance

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 200000 in
/-- The control type of `hb2Program` is finite (a fixed nested product of finite types). -/
@[irreducible] noncomputable def ctrlFin [Fintype BStack] (c : ℕ) {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) :
    Fintype (CtrlOf (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀)) := by
  unfold CtrlOf
  infer_instance

/-- The finite set of cells of the fixed program: every referenced cell, the input and `yc 8`. -/
def hbSupp [Fintype BStack] (c : ℕ) {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) : Finset H7 :=
  @supp2 H7 _ _ _ (labFin M c W₀ w₀₀ v₀₀ W w₀ v₀) (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀) inH7 (yc 8)

abbrev HCell [Fintype BStack] (c : ℕ) {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) : Type := {x : H7 // x ∈ hbSupp M c W₀ w₀₀ v₀₀ W w₀ v₀}

@[irreducible] noncomputable def cellFin [Fintype BStack] (c : ℕ) {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) : Fintype (HCell M c W₀ w₀₀ v₀₀ W w₀ v₀) :=
  Finset.Subtype.fintype _

def hbIn [Fintype BStack] (c : ℕ) {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) : HCell M c W₀ w₀₀ v₀₀ W w₀ v₀ :=
  @inCell2 H7 _ _ _ (labFin M c W₀ w₀₀ v₀₀ W w₀ v₀) (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀) inH7 (yc 8)

def hbOut [Fintype BStack] (c : ℕ) {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) : HCell M c W₀ w₀₀ v₀₀ W w₀ v₀ :=
  @outCell2 H7 _ _ _ (labFin M c W₀ w₀₀ v₀₀ W w₀ v₀) (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀) inH7 (yc 8)

def hbFin [Fintype BStack] (c : ℕ) {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) : LabelOf (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀) →
    TM2.Stmt (fun _ : HCell M c W₀ w₀₀ v₀₀ W w₀ v₀ => Bool) (LabelOf (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀))
      (CtrlOf (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀)) :=
  @restrict2 H7 _ _ _ (labFin M c W₀ w₀₀ v₀₀ W w₀ v₀) (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀) inH7 (yc 8)

def hbStart [Fintype BStack] (c : ℕ) {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) : LabelOf (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀) := (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))

def hbInit [Fintype BStack] (c : ℕ) {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) : CtrlOf (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀) := ((none, (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)), (none, ((), (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl)))))),
      (none, (none, (none, (none, (none, (none, (none, (none, none)))))))))

/-- ONE fixed finite Boolean-stack machine: input stack = the packet cell, output stack = `yc 8`. -/
noncomputable def hb2Machine [Fintype BStack] (c : ℕ) {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) : BitMachine.Machine :=
  @BitMachineEncoding.ofFinite (HCell M c W₀ w₀₀ v₀₀ W w₀ v₀) (LabelOf (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀))
    (CtrlOf (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀)) (cellFin M c W₀ w₀₀ v₀₀ W w₀ v₀) (labFin M c W₀ w₀₀ v₀₀ W w₀ v₀) (ctrlFin M c W₀ w₀₀ v₀₀ W w₀ v₀)
    (hbIn M c W₀ w₀₀ v₀₀ W w₀ v₀) (hbOut M c W₀ w₀₀ v₀₀ W w₀ v₀) (hbStart M c W₀ w₀₀ v₀₀ W w₀ v₀) (hbInit M c W₀ w₀₀ v₀₀ W w₀ v₀) (hbFin M c W₀ w₀₀ v₀₀ W w₀ v₀)

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem hb2_outputs [Fintype BStack] (c : ℕ) {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (G : EndpointGraph V E) (n : ℕ) (hc : 1 ≤ c) (hk : 1 ≤ WeightedRawWords.kValue M n)
    (T22₀ : ℕ) (hW₀ : Writer22Spec M W₀ w₀₀ v₀₀ T22₀ G n c) (T22 T : ℕ)
    (hW : ∀ j, 1 ≤ j → j < WeightedRawWords.kValue M n →
      Writer22SpecJ W w₀ v₀ T22 G c (EffectiveIteration.sourceDepth n)
        (yP G c (EffectiveIteration.sourceDepth n) j) j (MP G c (EffectiveIteration.sourceDepth n) j)
        (mSj (mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j)
        (MatrixMaterialization.rowMajor
          (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry))
    (hT : ∀ j, 1 ≤ j → j < WeightedRawWords.kValue M n →
      roundBoundP G c (EffectiveIteration.sourceDepth n) j (mb1 M G n c)
          (MatrixMaterialization.rowMajor
            (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry) T22 +
        installBoundP G c (EffectiveIteration.sourceDepth n) j + 1 ≤ T) :
    (hb2Machine M c W₀ w₀₀ v₀₀ W w₀ v₀).OutputsWithin
      (SourceOriginalBranchPackets.packet n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))
      (hb2Word G n c (WeightedRawWords.kValue M n))
      (fuelShellBound M G n c T22₀ T + emitBound G n c (WeightedRawWords.kValue M n) + 1) := by
  obtain ⟨t, ht, Y, hrun, hout, -⟩ :=
    hb2_bank_run M G n c hc hk W₀ w₀₀ v₀₀ T22₀ hW₀ W w₀ v₀ T22 T hW hT
  have hr := @restrict2_run H7 _ _ _ (labFin M c W₀ w₀₀ v₀₀ W w₀ v₀) (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀) inH7 (yc 8)
    _ _ _ _ _ _ t hrun
  set p := SourceOriginalBranchPackets.packet n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G)) with hp
  have hinit : rawInit (hbIn M c W₀ w₀₀ v₀₀ W w₀ v₀) (hbStart M c W₀ w₀₀ v₀₀ W w₀ v₀) (hbInit M c W₀ w₀₀ v₀₀ W w₀ v₀) p =
      (⟨some (hbStart M c W₀ w₀₀ v₀₀ W w₀ v₀), hbInit M c W₀ w₀₀ v₀₀ W w₀ v₀,
        fun x => ext7 (ext6 (ext4 (H0 p) blank57) blank8) blank16 x.val⟩ :
        TM2.Cfg (fun _ : HCell M c W₀ w₀₀ v₀₀ W w₀ v₀ => Bool) (LabelOf (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀))
          (CtrlOf (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀))) := by
    unfold rawInit
    congr 1
    funext x
    by_cases hx : x = hbIn M c W₀ w₀₀ v₀₀ W w₀ v₀
    · subst hx
      rw [if_pos rfl]
      exact (start_at p).symm
    · rw [if_neg hx]
      have hv : x.val ≠ inH7 := by
        intro h
        apply hx
        exact Subtype.ext h
      exact (start_blank p x.val hv).symm
  apply @outputsWithin_of_raw_run (HCell M c W₀ w₀₀ v₀₀ W w₀ v₀) (LabelOf (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀))
    (CtrlOf (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀)) (cellFin M c W₀ w₀₀ v₀₀ W w₀ v₀) (labFin M c W₀ w₀₀ v₀₀ W w₀ v₀) (ctrlFin M c W₀ w₀₀ v₀₀ W w₀ v₀) _
    (hbIn M c W₀ w₀₀ v₀₀ W w₀ v₀) (hbOut M c W₀ w₀₀ v₀₀ W w₀ v₀) (hbStart M c W₀ w₀₀ v₀₀ W w₀ v₀) (hbInit M c W₀ w₀₀ v₀₀ W w₀ v₀) (hbFin M c W₀ w₀₀ v₀₀ W w₀ v₀)
    p _ t _ ht
  · rw [hinit]
    exact congrArg (fun q => q.l) hr
  · rw [hinit]
    have ho := congrArg (fun q => q.stk (hbOut M c W₀ w₀₀ v₀₀ W w₀ v₀)) hr
    exact ho.trans hout

/-- `HB2Physical` for ONE fixed machine. Premises: `1 ≤ c`, and for every instance allowed by
`HB2Physical` the level-0 writer-22 specification, the per-level writer-22 specifications, one
round majorant `T`, and the public clock inequality for the literal run bound. -/
theorem hb2_physical [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (c A d Δ : ℕ) (γ : ℚ) (hc : 1 ≤ c)
    {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) (C₂ E₂ F₂ : ℕ)
    (hprem : ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : EndpointGraph V E) (n : ℕ),
      G.SourceCommon γ Δ → n ≤ Fintype.card E →
      Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
      1 ≤ ETHTailGrowth.repetitions c A d n →
      ∃ T22₀ T22 T : ℕ,
        Writer22Spec (CutoffBitMachine.actualMachine c A d) W₀ w₀₀ v₀₀ T22₀ G n c ∧
        (∀ j, 1 ≤ j → j < WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n →
          Writer22SpecJ W w₀ v₀ T22 G c (EffectiveIteration.sourceDepth n)
            (yP G c (EffectiveIteration.sourceDepth n) j) j
            (MP G c (EffectiveIteration.sourceDepth n) j)
            (mSj (mb1 (CutoffBitMachine.actualMachine c A d) G n c) G c
              (EffectiveIteration.sourceDepth n) j)
            (MatrixMaterialization.rowMajor
              (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry)) ∧
        (∀ j, 1 ≤ j → j < WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n →
          roundBoundP G c (EffectiveIteration.sourceDepth n) j
              (mb1 (CutoffBitMachine.actualMachine c A d) G n c)
              (MatrixMaterialization.rowMajor
                (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
                  (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry) T22 +
            installBoundP G c (EffectiveIteration.sourceDepth n) j + 1 ≤ T) ∧
        fuelShellBound (CutoffBitMachine.actualMachine c A d) G n c T22₀ T +
            emitBound G n c (WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n) + 1 ≤
          C₂ * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ E₂ *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ F₂) :
    PhysicalLevelRun.HB2Physical c A d Δ γ := by
  refine ⟨hb2Machine (CutoffBitMachine.actualMachine c A d) c W₀ w₀₀ v₀₀ W w₀ v₀, C₂, E₂, F₂, ?_⟩
  intro V E _ _ _ _ G n hcommon hlower hupper hrep
  obtain ⟨T22₀, T22, T, hW₀, hW, hT, hclock⟩ := hprem G n hcommon hlower hupper hrep
  have hk : 1 ≤ WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n := by
    rw [kValue_actual]; exact hrep
  have h := hb2_outputs (CutoffBitMachine.actualMachine c A d) c W₀ w₀₀ v₀₀ W w₀ v₀ G n hc hk
    T22₀ hW₀ T22 T hW hT
  have h' := BitMachine.outputsWithin_mono _ h hclock
  rw [kValue_actual] at h'
  exact h'

#print axioms stackStmt_restrict2
#print axioms restrict2_run
#print axioms start_blank
#print axioms hb2_outputs
#print axioms hb2_physical

end
end EthInapproximability.CurrentPaper.HB2Machine
