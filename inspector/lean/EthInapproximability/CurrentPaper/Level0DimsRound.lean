import EthInapproximability.CurrentPaper.Level0RoundClean
import EthInapproximability.CurrentPaper.NextDimsEmbedTN
import EthInapproximability.CurrentPaper.Level0DimsInputs
import EthInapproximability.CurrentPaper.Level0DimsInputs2

/-! Lane owner:b-weighted-level-8, unit 2, segment 2c splice: the rows/columns recompute
machine `NextDimsMachineTN` (owner-7) spliced into owner-6's level-0 round, between the cost
program and the admitted physical step `bridgeH`.

Global stack `H4 = H2 ⊕ Fin 57` (owner-6 `H2 = HStack ⊕ (Fin 16 ⊕ LogStack)` plus 57 fresh
cells: 55 for the dims machine's cells 9..63 — its two output cells 9, 10 land in `.inr 0`,
`.inr 1` — and two spare cells `.inr 55`, `.inr 56` reserved for the output harvest).

ONE fixed program `round4Program M c W w₀ v₀` = owner-5 `prepProgram M c` ; the writer-22
program `W` (owner-5 `Writer22Spec` the named premise) ; owner-6 `costProgram` (embedded by
`costEmb4`, inputs read in place) ; owner-7 `dimsProgram` (embedded by `dimsEmb`, inputs read in
place) ; owner-5 `bridgeH`; four charged handoffs (`BitMachineRawSequence.program`).

`dimsEmb` reads the nine dims inputs IN PLACE from the round bank:
`lam` = outer-width input `oc oIn` (scale P0), `s` = writer 28 (bins P0), `E` = master E,
`cols` = writer 27, `b` = master B, `c` = master C, `nv` = writer 18 (`4 * bins P0 * |V|`),
`rows` = writer 17, `t` = writer 16 (`bins P0 * familySize P0`); its 55 temporaries are fresh
cells, its log region is the cost machine's log region (blank again after the cost run).
The dims run happens BEFORE the bridge (the bridge region contains the writer region); its
outputs sit outside the bridge region, so the bridge leaves them unchanged.

`level0_dims_round`: from the branch packet, ONE run halts on the bank
`ext4 (bank pEmb S₂ z.stk) (D1 G n c)`, where masters C, B, Y, E hold the level-1 raw words
0, 1, 2, 5 and the two dims cells hold the level-1 raw words 3 (rows) and 4 (columns): all
six level-1 words. The clock is owner-6's round clock plus `dimsBound`. -/

namespace EthInapproximability.CurrentPaper.Level0DimsRound

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready
open OuterLevel0Prep OuterLevel0Run OuterLevel0Bridge OuterLevel0Full NextMasterWords
open CostUpdateStages CostUpdateMachine CostUpdateEmbed Level0CostRound Level0CostRun

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

abbrev H4 := H2 ⊕ Fin 57

def iH4 : HStack ↪ H4 := ⟨fun x => .inl (.inl x), fun _ _ h => Sum.inl.inj (Sum.inl.inj h)⟩

def blank57 : Fin 57 → List Bool := fun _ => []

/-- A bank on `H4`: `S` on `HStack`, blank on owner-6's cost cells, `D` on the fresh cells. -/
def ext4 (S : HStack → List Bool) (D : Fin 57 → List Bool) : H4 → List Bool :=
  Sum.elim (ext S) D

def lift4 {L V : Type} (P : L → TM2.Stmt (fun _ : HStack => Bool) L V) :
    L → TM2.Stmt (fun _ : H4 => Bool) L V :=
  fun l => stackStmt iH4 (P l)

theorem bank_ext4 (S T : HStack → List Bool) (D : Fin 57 → List Bool) :
    bank iH4 (ext4 S D) T = ext4 T D := by
  funext x
  rcases x with (x | x) | x
  · exact bank_at iH4 (ext4 S D) T x
  · rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
    rfl
  · rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
    rfl

theorem lift4_run {L V : Type} (P : L → TM2.Stmt (fun _ : HStack => Bool) L V)
    (l l' : Option L) (v v' : V) (S T : HStack → List Bool) (D : Fin 57 → List Bool) (t : ℕ)
    (h : ((advance P)^[t]) (⟨l, v, S⟩ : TM2.Cfg (fun _ : HStack => Bool) L V) = ⟨l', v', T⟩) :
    ((advance (lift4 P))^[t]) (⟨l, v, ext4 S D⟩ : TM2.Cfg (fun _ : H4 => Bool) L V) =
      ⟨l', v', ext4 T D⟩ := by
  have r := WeightedRawWords.region_run iH4 P ⟨l, v, S⟩ ⟨l', v', T⟩ t h (ext4 S D) (fun _ => rfl)
  dsimp only at r
  rw [bank_ext4] at r
  exact r

theorem elim_update_inl {α β : Type} [DecidableEq α] [DecidableEq β]
    (A : α → List Bool) (D : β → List Bool) (y : α) (u : List Bool) :
    Function.update (Sum.elim A D) (.inl y) u = Sum.elim (Function.update A y u) D := by
  funext z
  rcases z with z | z
  · by_cases h : z = y
    · subst h
      rw [Function.update_self]
      show u = Function.update A z u z
      rw [Function.update_self]
    · rw [Function.update_of_ne (fun e => h (Sum.inl.inj e))]
      show A z = Function.update A y u z
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by intro e; cases e)]
    rfl

theorem elim_update_inr {α β : Type} [DecidableEq α] [DecidableEq β]
    (A : α → List Bool) (D : β → List Bool) (y : β) (u : List Bool) :
    Function.update (Sum.elim A D) (.inr y) u = Sum.elim A (Function.update D y u) := by
  funext z
  rcases z with z | z
  · rw [Function.update_of_ne (by intro e; cases e)]
    rfl
  · by_cases h : z = y
    · subst h
      rw [Function.update_self]
      show u = Function.update D z u z
      rw [Function.update_self]
    · rw [Function.update_of_ne (fun e => h (Sum.inr.inj e))]
      show D z = Function.update D y u z
      rw [Function.update_of_ne h]

theorem ext4_update (S : HStack → List Bool) (D : Fin 57 → List Bool) (x : HStack)
    (u : List Bool) :
    Function.update (ext4 S D) (.inl (.inl x)) u = ext4 (Function.update S x u) D := by
  unfold ext4
  rw [elim_update_inl, ext_update]

theorem ext4_update_fresh (S : HStack → List Bool) (D : Fin 57 → List Bool) (i : Fin 57)
    (u : List Bool) :
    Function.update (ext4 S D) (.inr i) u = ext4 S (Function.update D i u) := by
  unfold ext4
  rw [elim_update_inr]

/-! ## The cost machine in `H4` (owner-6 `costEmb` followed by `Sum.inl`) -/

def costEmb4 : CS ↪ H4 := ⟨fun x => .inl (costEmb x), fun _ _ h => costEmb.injective (Sum.inl.inj h)⟩

theorem costEmb4_cell5 : costEmb4 (cell 5) = .inl (.inl (mcell .Y)) := rfl

/-! ## The dims machine in `H4` -/

/-- The nine dims inputs, read in place: `lam s E cols b c nv rows t`. -/
def dsrc : Fin 9 → HStack :=
  ![oc oIn, wcell 28, mcell .E, wcell 27, mcell .B, mcell .C, wcell 18, wcell 17, wcell 16]

theorem dsrc_inj : Function.Injective dsrc := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | (exfalso; cases h; done)
    | exact absurd (mcell_inj h) (by decide)
    | exact absurd (wcell_inj h) (by decide)
    | exact absurd h (wcell_ne_mcell _ _)
    | exact absurd h.symm (wcell_ne_mcell _ _)

def dimsMap : NextDimsStages.DS 64 → H4
  | .inl k => if h : k.val < 9 then .inl (.inl (dsrc ⟨k.val, h⟩))
      else .inr ⟨k.val - 9, by have := k.isLt; omega⟩
  | .inr l => .inl (.inr (.inr l))

theorem dimsMap_inj : Function.Injective dimsMap := by
  intro a b h
  rcases a with ⟨a, ha⟩ | a <;> rcases b with ⟨b, hb⟩ | b
  · by_cases h1 : a < 9 <;> by_cases h2 : b < 9
    · simp only [dimsMap, dif_pos h1, dif_pos h2] at h
      have := dsrc_inj (Sum.inl.inj (Sum.inl.inj h))
      simp only [Fin.mk.injEq] at this
      subst this; rfl
    · simp only [dimsMap, dif_pos h1, dif_neg h2] at h
      cases h
    · simp only [dimsMap, dif_neg h1, dif_pos h2] at h
      cases h
    · simp only [dimsMap, dif_neg h1, dif_neg h2] at h
      have := congrArg Fin.val (Sum.inr.inj h)
      simp only at this
      have e : a = b := by omega
      subst e; rfl
  · by_cases h1 : a < 9
    · simp only [dimsMap, dif_pos h1] at h; cases h
    · simp only [dimsMap, dif_neg h1] at h; cases h
  · by_cases h2 : b < 9
    · simp only [dimsMap, dif_pos h2] at h; cases h
    · simp only [dimsMap, dif_neg h2] at h; cases h
  · simp only [dimsMap] at h
    exact congrArg Sum.inr (Sum.inr.inj (Sum.inr.inj (Sum.inl.inj h)))

def dimsEmb : NextDimsStages.DS 64 ↪ H4 := ⟨dimsMap, dimsMap_inj⟩

theorem dimsEmb_nine : dimsEmb (NextDimsStages.cell 9) = (.inr 0 : H4) := rfl
theorem dimsEmb_ten : dimsEmb (NextDimsStages.cell 10) = (.inr 1 : H4) := rfl

/-! ## One-sided value lemmas for the dims start vector -/

theorem S0_0 (x : NextDimsMachineTN.DimIn) (h : 0 < 64) :
    NextDimsMachineTN.S0 x ⟨0, h⟩ = x.lam := rfl
theorem S0_1 (x : NextDimsMachineTN.DimIn) (h : 1 < 64) :
    NextDimsMachineTN.S0 x ⟨1, h⟩ = x.s := rfl
theorem S0_2 (x : NextDimsMachineTN.DimIn) (h : 2 < 64) :
    NextDimsMachineTN.S0 x ⟨2, h⟩ = x.E := rfl
theorem S0_3 (x : NextDimsMachineTN.DimIn) (h : 3 < 64) :
    NextDimsMachineTN.S0 x ⟨3, h⟩ = x.cols := rfl
theorem S0_4 (x : NextDimsMachineTN.DimIn) (h : 4 < 64) :
    NextDimsMachineTN.S0 x ⟨4, h⟩ = x.b := rfl
theorem S0_5 (x : NextDimsMachineTN.DimIn) (h : 5 < 64) :
    NextDimsMachineTN.S0 x ⟨5, h⟩ = x.c := rfl
theorem S0_6 (x : NextDimsMachineTN.DimIn) (h : 6 < 64) :
    NextDimsMachineTN.S0 x ⟨6, h⟩ = x.nv := rfl
theorem S0_7 (x : NextDimsMachineTN.DimIn) (h : 7 < 64) :
    NextDimsMachineTN.S0 x ⟨7, h⟩ = x.rows := rfl
theorem S0_8 (x : NextDimsMachineTN.DimIn) (h : 8 < 64) :
    NextDimsMachineTN.S0 x ⟨8, h⟩ = x.t := rfl

theorem S0_tmp (x : NextDimsMachineTN.DimIn) (k : ℕ) (hk : k < 64) (h9 : ¬ k < 9) :
    NextDimsMachineTN.S0 x ⟨k, hk⟩ = 0 := by
  interval_cases k <;> first | omega | rfl

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The dims inputs at level 0: `dimsIn P0 |V| (bins P0 * familySize P0)`. -/
abbrev dx (G : EndpointGraph V E) (n c : ℕ) : NextDimsMachineTN.DimIn :=
  NextDimsEmbedTN.dimsIn (P0 G n c) (Fintype.card V)
    (Parameters.bins (P0 G n c) * EffectiveIteration.familySize (P0 G n c))

theorem P0_fields (G : EndpointGraph V E) (n c : ℕ) :
    (P0 G n c).edges = Fintype.card E ∧ (P0 G n c).nextDepth = EffectiveIteration.sourceDepth n ∧
      (P0 G n c).sourceConstant = c := ⟨rfl, rfl, rfl⟩

theorem w22_ne_wcell (k : Fin 64) (hk : k ≠ 22) : w22 ≠ wcell k := by
  intro e
  have e' : (Sum.inl (Sum.inl (wc 22)) : HStack) = Sum.inl (Sum.inl (wc k)) := e
  exact hk (wc_inj (Sum.inl.inj (Sum.inl.inj e'))).symm

/-- A persistent writer cell `k ≠ 22` of the cost-updated bank is the ready bank's writer `k`. -/
theorem S2_wcell (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (k : Fin 64) (hk : k ≠ 22) :
    S2 M G n c F Q P (wcell k) = G4 (level0RowsBank M G n c F Q P) (Sum.inl (wc k)) := by
  dsimp only [S2, S22]
  rw [Function.update_of_ne (wcell_ne_mcell k .Y),
    Function.update_of_ne (w22_ne_wcell k hk).symm] <;> rfl

/-- The dims machine's start bank shows through `dimsEmb` in the cost-updated round bank. -/
theorem level0_dims_inputs (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts M G n c F Q P) (y : NextDimsStages.DS 64) :
    ext4 (S2 M G n c F Q P) blank57 (dimsEmb y) =
      NextDimsStages.U (NextDimsMachineTN.S0 (dx G n c)) y := by
  obtain ⟨hC, hB, hE⟩ := exit_masters M G n c F Q P
    (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits
  rcases y with ⟨k, hk⟩ | l
  · by_cases h9 : k < 9
    · have hm : dimsEmb (.inl ⟨k, hk⟩) = .inl (.inl (dsrc ⟨k, h9⟩)) := by
        show dimsMap (.inl ⟨k, hk⟩) = _
        simp only [dimsMap, dif_pos h9]
      rw [hm]
      show S2 M G n c F Q P (dsrc ⟨k, h9⟩) = NextDimsStages.U _ (NextDimsStages.cell ⟨k, hk⟩)
      rw [NextDimsStages.U_cell]
      interval_cases k
      · -- lam: outer-width input, unary scale P0
        show S2 M G n c F Q P (oc oIn) = _
        rw [S0_0]
        simp only [dx, NextDimsEmbedTN.dimsIn]
        dsimp only [S2, S22]
        rw [Function.update_of_ne (by intro e; cases e),
          Function.update_of_ne (w22_ne_oc oIn).symm]
        show OuterStartBank.outerTarget (EffectiveIteration.sourceDepth n) c
          (Parameters.bins (P0 G n c)) (Parameters.scale (P0 G n c)) oIn = _
        rw [outerTarget_cells, if_pos rfl]
      · -- s: writer 28
        show S2 M G n c F Q P (wcell 28) = _
        rw [S0_1]
        simp only [dx, NextDimsEmbedTN.dimsIn]
        rw [S2_wcell M G n c F Q P 28 (by decide)]
        exact writer28 M G n c F Q P hf
      · -- E: master E
        show S2 M G n c F Q P (mcell .E) = _
        rw [S0_2]
        simp only [dx, NextDimsEmbedTN.dimsIn]
        dsimp only [S2]
        rw [Function.update_of_ne (mcell_Y_ne .E (by decide)), (P0_fields G n c).1]
        exact hE
      · -- cols: writer 27
        show S2 M G n c F Q P (wcell 27) = _
        rw [S0_3]
        simp only [dx, NextDimsEmbedTN.dimsIn]
        rw [S2_wcell M G n c F Q P 27 (by decide)]
        exact Level0DimsInputs.writer27 M G n c F Q P hf
      · -- b: master B
        show S2 M G n c F Q P (mcell .B) = _
        rw [S0_4]
        simp only [dx, NextDimsEmbedTN.dimsIn]
        dsimp only [S2]
        rw [Function.update_of_ne (mcell_Y_ne .B (by decide)), (P0_fields G n c).2.1]
        exact hB
      · -- c: master C
        show S2 M G n c F Q P (mcell .C) = _
        rw [S0_5]
        simp only [dx, NextDimsEmbedTN.dimsIn]
        dsimp only [S2]
        rw [Function.update_of_ne (mcell_Y_ne .C (by decide)), (P0_fields G n c).2.2]
        exact hC
      · -- nv: writer 18
        show S2 M G n c F Q P (wcell 18) = _
        rw [S0_6]
        simp only [dx, NextDimsEmbedTN.dimsIn]
        rw [S2_wcell M G n c F Q P 18 (by decide)]
        exact Level0DimsInputs2.writer18 M G n c F Q P hf
      · -- rows: writer 17
        show S2 M G n c F Q P (wcell 17) = _
        rw [S0_7]
        simp only [dx, NextDimsEmbedTN.dimsIn]
        rw [S2_wcell M G n c F Q P 17 (by decide)]
        exact Level0DimsInputs.writer17 M G n c F Q P hf
      · -- t: writer 16
        show S2 M G n c F Q P (wcell 16) = _
        rw [S0_8]
        simp only [dx, NextDimsEmbedTN.dimsIn]
        rw [S2_wcell M G n c F Q P 16 (by decide)]
        exact Level0DimsInputs.writer16 M G n c F Q P hf
    · have hm : dimsEmb (.inl ⟨k, hk⟩) = .inr ⟨k - 9, by omega⟩ := by
        show dimsMap (.inl ⟨k, hk⟩) = _
        simp only [dimsMap, dif_neg h9]
      rw [hm]
      show ([] : List Bool) = NextDimsStages.U _ (NextDimsStages.cell ⟨k, hk⟩)
      rw [NextDimsStages.U_cell, S0_tmp _ k hk h9] <;> rfl
  · show ([] : List Bool) = NextDimsStages.U _ (.inr l)
    rw [NextDimsStages.U_log]

#print axioms level0_dims_inputs

/-- The two dims output cells after the run. -/
def D1 (G : EndpointGraph V E) (n c : ℕ) : Fin 57 → List Bool :=
  Function.update (Function.update blank57 0
      (List.replicate (EffectiveIteration.nextRows (P0 G n c)) true)) 1
    (List.replicate (EffectiveIteration.nextColumns (P0 G n c) (Fintype.card V)) true)

theorem rp_one (G : EndpointGraph V E) (n c : ℕ) :
    rp G n c (0 + 1) = EffectiveIteration.nextInput (P0 G n c) (Fintype.card V) := by
  have h := EffectiveIteration.runParameters_succ G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) 0
  have hrp : EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)) 0 = P0 G n c := rfl
  rw [hrp] at h
  exact h

/-- Word 3 (rows) of level 1 is the dims machine's rows output. -/
theorem D1_rows (G : EndpointGraph V E) (n c : ℕ) :
    D1 G n c 0 = ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 3 := by
  show _ = List.replicate (rp G n c (0 + 1)).rows true
  rw [rp_one]
  unfold D1
  rw [Function.update_of_ne (show (0 : Fin 57) ≠ 1 by decide), Function.update_self] <;> rfl

/-- Word 4 (columns) of level 1 is the dims machine's columns output. -/
theorem D1_cols (G : EndpointGraph V E) (n c : ℕ) :
    D1 G n c 1 = ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 4 := by
  show _ = List.replicate (rp G n c (0 + 1)).columns true
  rw [rp_one]
  unfold D1
  rw [Function.update_self] <;> rfl

theorem D1_spare (G : EndpointGraph V E) (n c : ℕ) (i : Fin 57) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    D1 G n c i = [] := by
  unfold D1
  rw [Function.update_of_ne h1, Function.update_of_ne h0] <;> rfl

/-! ## The round -/

/-- ONE fixed level-0 round program: prep ; writer 22 ; cost update ; dims recompute ;
physical step. -/
def round4Program (c : ℕ) {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW)
    (w₀ : LW) (v₀ : VW) :=
  BitMachineRawSequence.program (lift4 (prepProgram M c))
    (BitMachineRawSequence.program (lift4 W)
      (BitMachineRawSequence.program (costOn costEmb4)
        (BitMachineRawSequence.program (NextDimsEmbedTN.dimsOn dimsEmb) (lift4 bridgeH)
          MatrixTableInterlaceProtectedBridge.start NextDimsMachineTN.dimsCtrl bridgeCtrl)
        (BitMachineRawSequence.leftLabel NextDimsMachineTN.dimsStart) costCtrl
        (NextDimsMachineTN.dimsCtrl, bridgeCtrl))
      (BitMachineRawSequence.leftLabel costStart) v₀
      (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))
    (BitMachineRawSequence.leftLabel w₀)
    ((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27)
    (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))

theorem level0_dims_round [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (G : EndpointGraph V E) (n c : ℕ) (hc : 1 ≤ c) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T22 : ℕ)
    (hW : Writer22Spec M W w₀ v₀ T22 G n c) :
    ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
    ∃ Q : WeightedGraphQJoined.Stack → List Bool,
    ∃ P : ChosenPrimeRaw.Stack → List Bool,
    ∃ t ≤ prepBound M G n c +
        (T22 + (costBound (Parameters.scale (P0 G n c)) (EffectiveIteration.sourceDepth n) c
            (Parameters.bins (P0 G n c)) (Fintype.card E)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget +
          (NextDimsMachineTN.dimsBound (dx G n c) +
            ProtectedFullBankBridgeScratch.actualPhysicalBudget G c
              (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix + 1) + 1) + 1) + 1,
      ∃ z : MatrixTableInterlaceProtectedBridge.Config,
        ((advance (round4Program M c W w₀ v₀))^[t])
          ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl (.scan 0))))))))),
            (((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))),
            ext4 (H0 (SourceOriginalBranchPackets.packet n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))) blank57⟩ =
          ⟨none, (((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, z.var)))),
            ext4 (bank pEmb (S2 M G n c F Q P) z.stk) (D1 G n c)⟩ ∧
        z.stk (.inr MatrixTableInterlaceOuterJoin.secondOutput) =
          ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix ∧
        level0Facts M G n c F Q P ∧
        bank pEmb (S2 M G n c F Q P) z.stk (mcell .C) =
          ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 0 ∧
        bank pEmb (S2 M G n c F Q P) z.stk (mcell .B) =
          ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 1 ∧
        bank pEmb (S2 M G n c F Q P) z.stk (mcell .Y) =
          ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 2 ∧
        D1 G n c 0 = ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 3 ∧
        D1 G n c 1 = ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 4 ∧
        bank pEmb (S2 M G n c F Q P) z.stk (mcell .E) =
          ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 5 ∧
        ∀ x : BStack, (z.stk x).length ≤
          ((ProtectedFullBankBridgeScratch.actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk x).length +
            BitMachineStackGrowth.perStep bridgeH * ProtectedFullBankBridgeScratch.actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix := by
  obtain ⟨F, Q, P, t1, ht1, h1, hf⟩ := level0_prep_run M G n c
  obtain ⟨t2, ht2, v₁, h2⟩ := hW F Q P hf
  -- cost update (owner-6 machine, inputs read in place)
  obtain ⟨t3, ht3, h3⟩ := cost_embedded costEmb4 (ext4 (S22 M G n c F Q P) blank57)
    (Parameters.scale (P0 G n c)) (EffectiveIteration.sourceDepth n) c
    (Parameters.bins (P0 G n c)) (Fintype.card E)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget
    (fun x => level0_cost_inputs M G n c F Q P hf x)
  rw [costEmb4_cell5, level0_cost_word G n c hc, ext4_update] at h3
  -- dims recompute (owner-7 machine, inputs read in place)
  obtain ⟨t35, ht35, h35⟩ := NextDimsEmbedTN.next_dims_embedded dimsEmb
    (ext4 (S2 M G n c F Q P) blank57) (P0 G n c) (Fintype.card V)
    (level0_dims_inputs M G n c F Q P hf)
  rw [dimsEmb_nine, dimsEmb_ten, ext4_update_fresh, ext4_update_fresh] at h35
  -- physical step (owner-5)
  have hS : ∀ x : BStack, x ≠ .inl (.inl (.inl 22)) →
      S2 M G n c F Q P (pEmb x) = exitBank G n c (G4 (level0RowsBank M G n c F Q P)) (pEmb x) := by
    intro x hx
    dsimp only [S2, S22]
    rw [Function.update_of_ne (fun e => mcell_outside .Y ⟨x, e⟩)]
    exact Function.update_of_ne (fun e => hx (pEmb.injective e)) _ _
  have h22 : S2 M G n c F Q P (pEmb (.inl (.inl (.inl 22)))) =
      (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits := by
    dsimp only [S2, S22]
    rw [Function.update_of_ne (fun e => mcell_outside .Y ⟨_, e⟩)]
    exact Function.update_self _ _ _
  obtain ⟨t4, ht4, z, h4, hl, hout⟩ :=
    level0_physical_handoff M G n c F Q P hf (S2 M G n c F Q P) hS h22
  have hstart : ∀ k : BStack, (ProtectedFullBankBridgeScratch.actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk k = S2 M G n c F Q P (pEmb k) := by
    intro k
    rcases k with w | o
    · rw [OuterStartBank.actualPhysicalStart_writer]
      by_cases hw : w = .inl (.inl 22)
      · subst hw
        rw [WeightedLevel0WriterRun.writer_start_22, h22]
      · rw [hS (.inl w) (by intro e; exact hw (Sum.inl.inj e))]
        exact (ready_writer M G n c F Q P hf w hw).symm
    · rw [OuterStartBank.actualPhysicalStart_outer, hS (.inr o) (by intro e; cases e)]
      rfl
  have hgrow : ∀ x : BStack, (z.stk x).length ≤
      ((ProtectedFullBankBridgeScratch.actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk x).length +
        BitMachineStackGrowth.perStep bridgeH * ProtectedFullBankBridgeScratch.actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix := by
    intro x
    have hg := BitMachineStackGrowth.run_growth bridgeH
      (⟨some MatrixTableInterlaceProtectedBridge.start,
        ((MatrixWeightedOrderPreparation.initial, MatrixWeightedOrderWriter.writerInitial),
          (OuterStartBank.outerVar, none)), S2 M G n c F Q P⟩ :
        TM2.Cfg (fun _ : HStack => Bool) MatrixTableInterlaceProtectedBridge.Label
          MatrixTableInterlaceProtectedBridge.Control) t4 (pEmb x)
    rw [h4] at hg
    dsimp only at hg
    rw [bank_at, ← hstart x] at hg
    have hm := Nat.mul_le_mul_left (BitMachineStackGrowth.perStep bridgeH) ht4
    omega
  rw [hl] at h4
  have h1' := lift4_run (prepProgram M c) _ _ _ _ _ _ blank57 t1 h1
  have h2' := lift4_run W _ _ _ _ _ _ blank57 t2 h2
  have h4' := lift4_run bridgeH _ _ _ _ _ _ (D1 G n c) t4 h4
  obtain ⟨u35, hu35, q35⟩ := BitMachineRawSequence.runs (NextDimsEmbedTN.dimsOn dimsEmb)
    (lift4 bridgeH) _ _ _ _ _ _ _ _ _ _ _ h35 h4'
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs (costOn costEmb4) _
    _ _ _ _ _ _ _ _ _ _ _ h3 q35
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs (lift4 W) _
    _ _ _ _ _ _ _ _ _ _ _ h2' q3
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs (lift4 (prepProgram M c)) _
    _ _ _ _ _ _ _ _ _ _ _ h1' q2
  obtain ⟨hC, hB, hE⟩ := exit_masters M G n c F Q P
    (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits
  have hC' : S2 M G n c F Q P (mcell .C) = List.replicate c true := by
    dsimp only [S2]
    rw [Function.update_of_ne (mcell_Y_ne .C (by decide))]
    exact hC
  have hB' : S2 M G n c F Q P (mcell .B) =
      List.replicate (EffectiveIteration.sourceDepth n) true := by
    dsimp only [S2]
    rw [Function.update_of_ne (mcell_Y_ne .B (by decide))]
    exact hB
  have hE' : S2 M G n c F Q P (mcell .E) = List.replicate (Fintype.card E) true := by
    dsimp only [S2]
    rw [Function.update_of_ne (mcell_Y_ne .E (by decide))]
    exact hE
  obtain ⟨mC, mB, mE⟩ := bridge_next_masters G c (EffectiveIteration.sourceDepth n) 0
    (S2 M G n c F Q P) z.stk hC' hB' hE'
  have mY : bank pEmb (S2 M G n c F Q P) z.stk (mcell .Y) =
      ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 2 := by
    rw [bank_master]
    exact Function.update_self _ _ _
  have ht35' : t35 ≤ NextDimsMachineTN.dimsBound (dx G n c) := ht35
  refine ⟨F, Q, P, u1, by omega, z, ?_, hout, hf, mC, mB, mY, D1_rows G n c, D1_cols G n c,
    mE, hgrow⟩
  exact q1

#print axioms level0_dims_round

end
end EthInapproximability.CurrentPaper.Level0DimsRound
