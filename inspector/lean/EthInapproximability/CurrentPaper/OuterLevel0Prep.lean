import EthInapproximability.CurrentPaper.WeightedLevel0Masters
import EthInapproximability.CurrentPaper.OuterStartBank
import EthInapproximability.CurrentPaper.ETHParameterScaleActual

/-! Lane owner:b-weighted-level-5, unit 2, segment 1 (1c-c-outer), piece B.

ONE fixed program `prepProgram M c` on the global stack
`HStack = GStack ⊕ (OStack ⊕ (SStack ⊕ Unit))` (GStack = owner-4 level-0 global
stack, OStack = the outer region of the admitted protected bridge, SStack = the
scale controller `ETHScaleActualComplete.Stack`, Unit = the copy temporary):

1. owner-4's `readyProgram M c` (frozen), lifted by `hG = Sum.inl`;
2. the admitted `ETHScaleActualComplete.program`, embedded by `sEmb`, whose six
   raw input cells ARE the level-0 master/writer cells holding the level-0 raw
   words (C, B, Y, writer 17 = rows, writer 27 = cols, E); the admitted run
   restores them (`actual_scale_run`, fourth conjunct) and writes unary
   `scale P0` into its answer cell; every other scale cell is fresh;
3. charged copies: scale answer -> outer-width input; master B, master C,
   writer 28 -> restoration-width inputs 0, 1, 2;
4. charged clear of the whole fresh scale region (clock by `run_growth` of
   the same scale run).

Exit bank (exact): `exitBank = Sum.elim (G4 L) (Sum.elim (outerTarget b c s lam) blank)`
where `G4 L` is owner-4's `readyProgram` exit and `outerTarget` is the closed
form of the outer region of the admitted `actualPhysicalStart` at level 0. -/

namespace EthInapproximability.CurrentPaper.OuterLevel0Prep

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

abbrev SStack := ETHScaleActualComplete.Stack
abbrev OStk := MatrixTableInterlaceProtectedBridge.OStack
abbrev HStack := GStack ⊕ (OStk ⊕ (SStack ⊕ Unit))

def hG : GStack ↪ HStack := ⟨Sum.inl, Sum.inl_injective⟩
def oc (o : OStk) : HStack := .inr (.inl o)
def fresh (x : SStack) : HStack := .inr (.inr (.inl x))
def tmpH : HStack := .inr (.inr (.inr ()))
def mcell (a : WeightedRawWords.Aux) : HStack := .inl (.inl (mc a))
def wcell (k : Fin 64) : HStack := .inl (.inl (wc k))

/-- The outer-width input cell and the restoration-width input cells. -/
def oIn : OStk := .inl MatrixOuterWidthMachine.inputStack
def rIn (i : Fin 4) : OStk := .inr (.inl (MatrixRestorationWidthMachine.inputStack i))

theorem wcell_ne_mcell (k : Fin 64) (a : WeightedRawWords.Aux) : wcell k ≠ mcell a :=
  fun h => wc_ne_mc k a (Sum.inl.inj (Sum.inl.inj h))
theorem wcell_inj {j k : Fin 64} (h : wcell j = wcell k) : j = k :=
  wc_inj (Sum.inl.inj (Sum.inl.inj h))
theorem mcell_inj {a b : WeightedRawWords.Aux} (h : mcell a = mcell b) : a = b := by
  have h' := Sum.inl.inj (Sum.inl.inj h)
  exact Sum.inr.inj (Sum.inr.inj h')

/-- Sources of the six raw scale inputs: C, B, Y, writer 17, writer 27, E. -/
def rawSrc : Fin 6 → HStack
  | 0 => mcell .C
  | 1 => mcell .B
  | 2 => mcell .Y
  | 3 => wcell 17
  | 4 => wcell 27
  | 5 => mcell .E

theorem rawSrc_inj : Function.Injective rawSrc := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | exact absurd (mcell_inj h) (by decide)
    | exact absurd (wcell_inj h) (by decide)
    | exact absurd h (wcell_ne_mcell _ _)
    | exact absurd h.symm (wcell_ne_mcell _ _)

def sMap : SStack → HStack
  | .inl (.inl j) => rawSrc j
  | .inl (.inr y) => fresh (.inl (.inr y))
  | .inr y => fresh (.inr y)

theorem sMap_inj : Function.Injective sMap := by
  intro a b h
  rcases a with (j | y) | y <;> rcases b with (j' | y') | y'
  · exact congrArg (fun j => Sum.inl (Sum.inl j)) (rawSrc_inj h)
  · exfalso; fin_cases j <;> cases h
  · exfalso; fin_cases j <;> cases h
  · exfalso; fin_cases j' <;> cases h
  · simpa [sMap, fresh] using h
  · cases h
  · exfalso; fin_cases j' <;> cases h
  · cases h
  · simpa [sMap, fresh] using h

def sEmb : SStack ↪ HStack := ⟨sMap, sMap_inj⟩

/-- Every fresh cell is outside the image of `sEmb` exactly at the six raw
positions; the answer cell is fresh. -/
theorem sEmb_answer : sEmb (.inr ScaleFinalScratch.answerKey) = fresh (.inr ScaleFinalScratch.answerKey) := rfl

/-! ## Component programs -/

def iL : Fin 3 ↪ HStack := ⟨![fresh (.inr ScaleFinalScratch.answerKey), oc oIn, tmpH], by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; cases h)⟩
def iB : Fin 3 ↪ HStack := ⟨![mcell .B, oc (rIn 0), tmpH], by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; cases h)⟩
def iC : Fin 3 ↪ HStack := ⟨![mcell .C, oc (rIn 1), tmpH], by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; cases h)⟩
def iS : Fin 3 ↪ HStack := ⟨![wcell 28, oc (rIn 2), tmpH], by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; cases h)⟩

def nS : ℕ := Fintype.card SStack
def cellsS (i : Fin nS) : HStack := fresh ((Fintype.equivFin SStack).symm i)
theorem cellsS_inj : Function.Injective cellsS := by
  intro a b h
  have h' := Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))
  exact (Fintype.equivFin SStack).symm.injective h'

variable (M : BitMachine.Machine)

def liftReady (c : ℕ) := fun l => stackStmt hG (readyProgram M c l)
def liftScale := fun l => stackStmt sEmb (ETHScaleActualComplete.program l)
def cpL := MatrixStage4ScalarPreparationOps.copyProgram iL
def cpB := MatrixStage4ScalarPreparationOps.copyProgram iB
def cpC := MatrixStage4ScalarPreparationOps.copyProgram iC
def cpS := MatrixStage4ScalarPreparationOps.copyProgram iS
def clearS := WeightedRawWords.clearProgram cellsS

def p67 := BitMachineRawSequence.program cpS clearS (0 : Fin (nS + 2))
  (none : Option Bool) ((), none)
def p57 := BitMachineRawSequence.program cpC p67
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool)
  ((none : Option Bool), ((), none))
def p47 := BitMachineRawSequence.program cpB p57
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool)
  ((none : Option Bool), ((none : Option Bool), ((), none)))
def p37 := BitMachineRawSequence.program cpL p47
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool)
  ((none : Option Bool), ((none : Option Bool), ((none : Option Bool), ((), none))))
def ctrl37 : Option Bool × (Option Bool × (Option Bool × (Option Bool × (Unit × Option Bool)))) :=
  (none, (none, (none, (none, ((), none)))))
def p27 := BitMachineRawSequence.program liftScale p37
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
  (ETHScaleActualComplete.oldControl, ETHScaleActualComplete.finalControl) ctrl37
def ctrl27 := ((ETHScaleActualComplete.oldControl, ETHScaleActualComplete.finalControl), ctrl37)

/-- ONE fixed program: level-0 ready frame, scale, four charged copies, clear. -/
def prepProgram (c : ℕ) := BitMachineRawSequence.program (liftReady M c) p27
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel ETHScaleActualComplete.oldStart))
  (((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))) ctrl27

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Level-0 parameter record (the physical step's `stepParameters` at level 0). -/
abbrev P0 (G : EndpointGraph V E) (n c : ℕ) : Parameters.Input :=
  Iteration.stepParameters G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix

def H0 (packet : List Bool) : HStack → List Bool := Sum.elim (G0 packet) (fun _ => [])
def K1 (L : GStack → List Bool) : HStack → List Bool := Sum.elim L (fun _ => [])

/-- The exact exit bank of `prepProgram`. -/
def exitBank (G : EndpointGraph V E) (n c : ℕ) (L : GStack → List Bool) : HStack → List Bool :=
  Sum.elim L (Sum.elim (OuterStartBank.outerTarget (EffectiveIteration.sourceDepth n) c
    (Parameters.bins (P0 G n c)) (Parameters.scale (P0 G n c))) (fun _ => []))

/-- The clock of `readyProgram` (literally the bound of owner-4 `level0_ready`). -/
def readyBound (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  cleanBound M G n c +
        ((2 * ProtectedFullBankBridgeScratch.actualRows G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix + 2) +
          ((2 * ProtectedFullBankBridgeScratch.actualCols G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix + 2) +
            (ProtectedFullBankBridgeScratch.actualRows G c (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix +
             ProtectedFullBankBridgeScratch.actualCols G c (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix + 4) + 1) + 1) + 1

/-- The clock of the scale stage, the four copies and the clear. -/
def outerBound (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  ETHScaleActualComplete.totalBound (P0 G n c) +
    ((2 * Parameters.scale (P0 G n c) + 2) +
      ((2 * EffectiveIteration.sourceDepth n + 2) +
        ((2 * c + 2) +
          ((2 * Parameters.bins (P0 G n c) + 2) +
            (nS * (ETHParameterScaleMachineInput.wordSize (P0 G n c) +
                BitMachineStackGrowth.perStep ETHScaleActualComplete.program *
                  ETHScaleActualComplete.totalBound (P0 G n c)) + nS + 2) + 1) + 1) + 1) + 1) + 1

def prepBound (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  readyBound M G n c + outerBound G n c + 1

theorem bank_hG (packet : List Bool) (S : GStack → List Bool) :
    bank hG (H0 packet) S = K1 S := by
  funext x
  rcases x with x | y
  · exact bank_at hG (H0 packet) S x
  · rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
    rfl

/-- The six level-0 raw words sit in the six aliased source cells. -/
theorem raw_words (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts M G n c F Q P) (j : Fin 6) :
    K1 (G4 (level0RowsBank M G n c F Q P)) (rawSrc j) =
      ETHParameterScaleMachineInput.words (P0 G n c) j := by
  have hv := WeightedLevel0Masters.masterC_values M G n c
  fin_cases j
  · show G4 (level0RowsBank M G n c F Q P) (Sum.inl (mc .C)) = _
    rw [WeightedLevel0Masters.ready_master M G n c F Q P .C
      (by intro h; cases h) (by intro h; cases h) (by intro m h; cases h)]
    exact hv.1
  · show G4 (level0RowsBank M G n c F Q P) (Sum.inl (mc .B)) = _
    rw [WeightedLevel0Masters.ready_master M G n c F Q P .B
      (by intro h; cases h) (by intro h; cases h) (by intro m h; cases h)]
    exact hv.2.1
  · show G4 (level0RowsBank M G n c F Q P) (Sum.inl (mc .Y)) = _
    rw [WeightedLevel0Masters.ready_master M G n c F Q P .Y
      (by intro h; cases h) (by intro h; cases h) (by intro m h; cases h)]
    exact hv.2.2.1
  · have h := ready_writer M G n c F Q P hf (.inl (.inl 17)) (by decide)
    have h' : G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 17)) = _ := h
    show G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 17)) = _
    rw [h']
    show MatrixWeightedOrderPreparation.sourceBank _ _ _ _ 17 = _
    rw [WeightedLevel0Target.sb_other _ _ _ _ 17 (by decide)]
    simp [MatrixWeightedEntryController.persistentBank, ETHParameterScaleMachineInput.words,
      Iteration.parameters]
    rfl
  · have h := ready_writer M G n c F Q P hf (.inl (.inl 27)) (by decide)
    have h' : G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 27)) = _ := h
    show G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 27)) = _
    rw [h']
    show MatrixWeightedOrderPreparation.sourceBank _ _ _ _ 27 = _
    rw [WeightedLevel0Target.sb_other _ _ _ _ 27 (by decide)]
    simp [MatrixWeightedEntryController.persistentBank, ETHParameterScaleMachineInput.words,
      Iteration.parameters]
    rfl
  · show G4 (level0RowsBank M G n c F Q P) (Sum.inl (mc .E)) = _
    rw [WeightedLevel0Masters.ready_master M G n c F Q P .E
      (by intro h; cases h) (by intro h; cases h) (by intro m h; cases h)]
    exact hv.2.2.2.1

/-- Writer 28 holds unary `bins P0`. -/
theorem writer28 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts M G n c F Q P) :
    G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 28)) =
      List.replicate (Parameters.bins (P0 G n c)) true := by
  have h := ready_writer M G n c F Q P hf (.inl (.inl 28)) (by decide)
  have h' : G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc 28)) = _ := h
  rw [h']
  show MatrixWeightedOrderPreparation.sourceBank _ _ _ _ 28 = _
  rw [WeightedLevel0Target.sb_other _ _ _ _ 28 (by decide)]
  simp [MatrixWeightedEntryController.persistentBank]
  rfl

/-- The scale controller's initial bank is exactly the global bank seen through `sEmb`. -/
theorem scale_initial (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts M G n c F Q P) (x : SStack) :
    ETHScaleActualComplete.initialBank (P0 G n c) x =
      K1 (G4 (level0RowsBank M G n c F Q P)) (sEmb x) := by
  rcases x with (j | y) | y
  · show _ = K1 (G4 (level0RowsBank M G n c F Q P)) (rawSrc j)
    rw [raw_words M G n c F Q P hf j]
    exact bank_at ETHScaleActualComplete.oldEmbed (fun _ => [])
      (ETHScaleGlobalLog.initial (P0 G n c)) (.inl j)
  · show _ = []
    exact bank_at ETHScaleActualComplete.oldEmbed (fun _ => [])
      (ETHScaleGlobalLog.initial (P0 G n c)) (.inr y)
  · show _ = []
    rw [ETHScaleActualComplete.initialBank, bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]

/-- Fresh cells of `sEmb` form exactly the non-raw positions. -/
theorem fresh_raw_outside (j : Fin 6) : ¬ ∃ x, sEmb x = fresh (.inl (.inl j)) := by
  rintro ⟨x, hx⟩
  rcases x with (j' | y) | y
  · fin_cases j' <;> cases hx
  · cases hx
  · cases hx

theorem fresh_bank (L : HStack → List Bool) (F : SStack → List Bool) (x : SStack) :
    bank sEmb L F (fresh x) = (match x with
      | .inl (.inl _) => L (fresh x)
      | _ => F x) := by
  rcases x with (j | y) | y
  · exact bank_outside _ _ _ _ (fresh_raw_outside j)
  · exact bank_at sEmb L F (.inl (.inr y))
  · exact bank_at sEmb L F (.inr y)

theorem outerTarget_cells (b c s lam : ℕ) (o : OStk) :
    OuterStartBank.outerTarget b c s lam o =
      if o = oIn then List.replicate lam true
      else if o = rIn 0 then List.replicate b true
      else if o = rIn 1 then List.replicate c true
      else if o = rIn 2 then List.replicate s true
      else [] := by
  rcases o with o | (o | o)
  · by_cases h : o = MatrixOuterWidthMachine.inputStack
    · subst h
      simp only [oIn, if_true]
      exact MatrixOuterWidthMachine.startCfg_input lam
    · have h1 : (Sum.inl o : OStk) ≠ oIn := fun e => h (Sum.inl.inj e)
      rw [if_neg h1, if_neg (by intro e; cases e), if_neg (by intro e; cases e),
        if_neg (by intro e; cases e)]
      exact MatrixOuterWidthMachine.startCfg_other_empty lam o h
  · rw [if_neg (by intro e; cases e)]
    by_cases h0 : o = MatrixRestorationWidthMachine.inputStack 0
    · subst h0
      simp only [rIn, if_true]
      exact MatrixRestorationWidthMachine.startCfg_input b c s 0 0
    have n0 : (Sum.inr (Sum.inl o) : OStk) ≠ rIn 0 := fun e => h0 (Sum.inl.inj (Sum.inr.inj e))
    rw [if_neg n0]
    by_cases h1 : o = MatrixRestorationWidthMachine.inputStack 1
    · subst h1
      simp only [rIn, if_true]
      exact MatrixRestorationWidthMachine.startCfg_input b c s 0 1
    have n1 : (Sum.inr (Sum.inl o) : OStk) ≠ rIn 1 := fun e => h1 (Sum.inl.inj (Sum.inr.inj e))
    rw [if_neg n1]
    by_cases h2 : o = MatrixRestorationWidthMachine.inputStack 2
    · subst h2
      simp only [rIn, if_true]
      exact MatrixRestorationWidthMachine.startCfg_input b c s 0 2
    have n2 : (Sum.inr (Sum.inl o) : OStk) ≠ rIn 2 := fun e => h2 (Sum.inl.inj (Sum.inr.inj e))
    rw [if_neg n2]
    by_cases h3 : o = MatrixRestorationWidthMachine.inputStack 3
    · subst h3
      exact MatrixRestorationWidthMachine.startCfg_input b c s 0 3
    change (MatrixRestorationWidthMachine.startCfg b c s 0).stk o = []
    rcases o with m | m
    · change MatrixRestorationWidthMachineProduct.inputBank b c s 0
        ((Fintype.equivFin (Fin 12)).symm m) = []
      have hm : ∀ i : Fin 4, (Fintype.equivFin (Fin 12)).symm m ≠ ⟨i.val, by omega⟩ := by
        intro i e
        have e' := congrArg (Fintype.equivFin (Fin 12)) e
        rw [Equiv.apply_symm_apply] at e'
        fin_cases i
        · exact h0 (congrArg Sum.inl e')
        · exact h1 (congrArg Sum.inl e')
        · exact h2 (congrArg Sum.inl e')
        · exact h3 (congrArg Sum.inl e')
      generalize (Fintype.equivFin (Fin 12)).symm m = j at hm
      fin_cases j
      · exact absurd rfl (hm 0)
      · exact absurd rfl (hm 1)
      · exact absurd rfl (hm 2)
      · exact absurd rfl (hm 3)
      all_goals rfl
    · exact MatrixRestorationWidthMachine.startCfg_post_empty b c s 0 m
  · rw [if_neg (by intro e; cases e), if_neg (by intro e; cases e),
      if_neg (by intro e; cases e), if_neg (by intro e; cases e)]
    rfl

#print axioms rawSrc_inj
#print axioms sMap_inj
#print axioms raw_words
#print axioms writer28
#print axioms scale_initial
#print axioms fresh_bank
#print axioms outerTarget_cells

end
end EthInapproximability.CurrentPaper.OuterLevel0Prep
