import EthInapproximability.CurrentPaper.NextMasterWords
import EthInapproximability.CurrentPaper.CostUpdateEmbed

/-! Lane owner:b-weighted-level-6, unit 2, segment 2b, piece 4: the cost-word
update INSIDE the level-0 round.

Global stack `H2 = HStack ⊕ (Fin 16 ⊕ LogStack)` (owner-5 `HStack` plus the
cost machine's sixteen temporaries and its log region). ONE fixed program
`roundProgram M c W w₀ v₀` = owner-5 `prepProgram M c` ; the writer-22 program
`W` (parameter, owner-5 `Writer22Spec` the named premise) ; the fixed cost
program `costOn costEmb` ; the embedded admitted physical step `bridgeH`
(owner-5), each lifted by `Sum.inl` where needed, three charged handoffs.

The cost program reads its six inputs IN PLACE: `lam = scale P0` in the outer
width input `oc oIn` (written by owner-5's prep from the admitted scale run),
`b` in master B, `c` in master C, `s = bins P0` in writer 28, `|E|` in master E,
and `y = y₀` in master Y (the level-0 cost word); it rewrites master Y to the
level-1 cost word `words (runParameters … 1) 2` (via owner-5
`NextCostWords.cost_word_succ`) and restores everything else. Master Y is
outside the bridge region, so the admitted physical step then runs from a
bank satisfying owner-5 `level0_physical_handoff`'s premises and leaves master
Y (and C, B, E) unchanged.

`level0_round`: from the branch packet, ONE run reaches a halted configuration
whose bank is `ext (bank pEmb S₂ z.stk)` with `S₂` = the prep exit with writer
22 = `d.rawBits` and master Y = the level-1 cost word; in it masters C, B, Y,
E hold the level-1 raw words 0, 1, 2, 5; clock
`prepBound + (T22 + (costBound … + actualPhysicalBudget + 1) + 1) + 1`.
Premises: `hW : Writer22Spec …` (owner-5) and `hc : 1 ≤ c`. -/

namespace EthInapproximability.CurrentPaper.Level0CostRound

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready
open OuterLevel0Prep OuterLevel0Run OuterLevel0Bridge OuterLevel0Full NextMasterWords
open CostUpdateStages CostUpdateMachine CostUpdateEmbed

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

abbrev H2 := HStack ⊕ (Fin 16 ⊕ CostUpdateStages.LogStack)

def hInl : HStack ↪ H2 := ⟨Sum.inl, Sum.inl_injective⟩

def ext (S : HStack → List Bool) : H2 → List Bool := Sum.elim S (fun _ => [])

def lift {L V : Type} (P : L → TM2.Stmt (fun _ : HStack => Bool) L V) :
    L → TM2.Stmt (fun _ : H2 => Bool) L V :=
  fun l => stackStmt hInl (P l)

theorem bank_ext (S T : HStack → List Bool) : bank hInl (ext S) T = ext T := by
  funext x
  rcases x with x | x
  · exact bank_at hInl (ext S) T x
  · rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
    rfl

theorem lift_run {L V : Type} (P : L → TM2.Stmt (fun _ : HStack => Bool) L V)
    (l l' : Option L) (v v' : V) (S T : HStack → List Bool) (t : ℕ)
    (h : ((advance P)^[t]) (⟨l, v, S⟩ : TM2.Cfg (fun _ : HStack => Bool) L V) = ⟨l', v', T⟩) :
    ((advance (lift P))^[t]) (⟨l, v, ext S⟩ : TM2.Cfg (fun _ : H2 => Bool) L V) =
      ⟨l', v', ext T⟩ := by
  have r := WeightedRawWords.region_run hInl P ⟨l, v, S⟩ ⟨l', v', T⟩ t h (ext S) (fun _ => rfl)
  dsimp only at r
  rw [bank_ext] at r
  exact r

theorem ext_update (S : HStack → List Bool) (x : HStack) (u : List Bool) :
    Function.update (ext S) (.inl x) u = ext (Function.update S x u) := by
  funext y
  rcases y with y | y
  · by_cases h : y = x
    · subst h
      rw [Function.update_self]
      show u = Function.update S y u y
      rw [Function.update_self]
    · rw [Function.update_of_ne (fun e => h (Sum.inl.inj e))]
      show S y = Function.update S x u y
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by intro e; cases e)]
    rfl

/-! ## The cost machine's cells in `H2` -/

/-- The six input cells, read in place: outer-width input, masters B, C,
writer 28, master E, master Y. -/
def srcCell : Fin 6 → HStack := ![oc oIn, mcell .B, mcell .C, wcell 28, mcell .E, mcell .Y]

theorem srcCell_inj : Function.Injective srcCell := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | (exfalso; cases h; done)
    | exact absurd (mcell_inj h) (by decide)
    | exact absurd h (wcell_ne_mcell _ _)
    | exact absurd h.symm (wcell_ne_mcell _ _)

def costMap : CS → H2
  | .inl k => if h : k.val < 6 then .inl (srcCell ⟨k.val, h⟩) else .inr (.inl ⟨k.val - 6, by omega⟩)
  | .inr l => .inr (.inr l)

theorem costMap_inj : Function.Injective costMap := by
  intro a b h
  rcases a with ⟨a, ha⟩ | a <;> rcases b with ⟨b, hb⟩ | b
  · by_cases h1 : a < 6 <;> by_cases h2 : b < 6
    · simp only [costMap, dif_pos h1, dif_pos h2] at h
      have := srcCell_inj (Sum.inl.inj h)
      simp only [Fin.mk.injEq] at this
      subst this; rfl
    · simp only [costMap, dif_pos h1, dif_neg h2] at h
      cases h
    · simp only [costMap, dif_neg h1, dif_pos h2] at h
      cases h
    · simp only [costMap, dif_neg h1, dif_neg h2] at h
      have := congrArg Fin.val (Sum.inl.inj (Sum.inr.inj h))
      simp only at this
      have e : a = b := by omega
      subst e; rfl
  · by_cases h1 : a < 6
    · simp only [costMap, dif_pos h1] at h; cases h
    · simp only [costMap, dif_neg h1] at h; cases h
  · by_cases h2 : b < 6
    · simp only [costMap, dif_pos h2] at h; cases h
    · simp only [costMap, dif_neg h2] at h; cases h
  · simp only [costMap] at h
    exact congrArg Sum.inr (Sum.inr.inj (Sum.inr.inj h))

def costEmb : CS ↪ H2 := ⟨costMap, costMap_inj⟩

theorem costEmb_cell5 : costEmb (cell 5) = .inl (mcell .Y) := rfl

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The writer-22 exit bank (owner-5 `Writer22Spec` target). -/
abbrev S22 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    HStack → List Bool :=
  Function.update (exitBank G n c (G4 (level0RowsBank M G n c F Q P))) w22
    (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits

theorem w22_ne_oc (o : OStk) : w22 ≠ oc o := by
  intro e; cases e

theorem w22_ne_w28 : w22 ≠ wcell 28 := by
  intro e
  have e' : (Sum.inl (Sum.inl (wc 22)) : HStack) = Sum.inl (Sum.inl (wc 28)) := e
  have := wc_inj (Sum.inl.inj (Sum.inl.inj e'))
  exact absurd this (by decide)

theorem st_v0 (a b c s e y : ℕ) : st a b c s e y 0 0 0 0 0 0 0 0 0 0 0 0 0 = a := rfl
theorem st_v1 (a b c s e y : ℕ) : st a b c s e y 0 0 0 0 0 0 0 0 0 0 0 0 1 = b := rfl
theorem st_v2 (a b c s e y : ℕ) : st a b c s e y 0 0 0 0 0 0 0 0 0 0 0 0 2 = c := rfl
theorem st_v3 (a b c s e y : ℕ) : st a b c s e y 0 0 0 0 0 0 0 0 0 0 0 0 3 = s := rfl
theorem st_v4 (a b c s e y : ℕ) : st a b c s e y 0 0 0 0 0 0 0 0 0 0 0 0 4 = e := rfl
theorem st_v5 (a b c s e y : ℕ) : st a b c s e y 0 0 0 0 0 0 0 0 0 0 0 0 5 = y := rfl
theorem st_tmp (a b c s e y : ℕ) (k : ℕ) (hk : k < 22) (h6 : ¬ k < 6) :
    st a b c s e y 0 0 0 0 0 0 0 0 0 0 0 0 ⟨k, hk⟩ = 0 := by
  interval_cases k <;> first | omega | rfl

/-- The cost machine's start bank shows through `costEmb` in the level-0 bank. -/
theorem level0_cost_inputs (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts M G n c F Q P) (x : CS) :
    ext (S22 M G n c F Q P) (costEmb x) =
      U (st (Parameters.scale (P0 G n c)) (EffectiveIteration.sourceDepth n) c
        (Parameters.bins (P0 G n c)) (Fintype.card E)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget
        0 0 0 0 0 0 0 0 0 0 0 0) x := by
  obtain ⟨hC, hB, hE⟩ := exit_masters M G n c F Q P
    (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits
  rcases x with ⟨k, hk⟩ | l
  · by_cases h6 : k < 6
    · have hm : costEmb (.inl ⟨k, hk⟩) = .inl (srcCell ⟨k, h6⟩) := by
        show costMap (.inl ⟨k, hk⟩) = _
        simp only [costMap, dif_pos h6]
      rw [hm]
      show S22 M G n c F Q P (srcCell ⟨k, h6⟩) = U _ (cell ⟨k, hk⟩)
      rw [U_cell]
      interval_cases k
      · -- outer-width input: unary scale P0
        show S22 M G n c F Q P (oc oIn) = _
        dsimp only [S22]
        rw [show (⟨0, hk⟩ : Fin 22) = 0 from rfl, st_v0,
          Function.update_of_ne (w22_ne_oc oIn).symm]
        show OuterStartBank.outerTarget (EffectiveIteration.sourceDepth n) c
          (Parameters.bins (P0 G n c)) (Parameters.scale (P0 G n c)) oIn = _
        rw [outerTarget_cells, if_pos rfl]
      · show S22 M G n c F Q P (mcell .B) = _
        rw [show (⟨1, hk⟩ : Fin 22) = 1 from rfl, st_v1]
        exact hB
      · show S22 M G n c F Q P (mcell .C) = _
        rw [show (⟨2, hk⟩ : Fin 22) = 2 from rfl, st_v2]
        exact hC
      · show S22 M G n c F Q P (wcell 28) = _
        dsimp only [S22]
        rw [show (⟨3, hk⟩ : Fin 22) = 3 from rfl, st_v3,
          Function.update_of_ne w22_ne_w28.symm]
        exact writer28 M G n c F Q P hf
      · show S22 M G n c F Q P (mcell .E) = _
        rw [show (⟨4, hk⟩ : Fin 22) = 4 from rfl, st_v4]
        exact hE
      · show S22 M G n c F Q P (mcell .Y) = _
        dsimp only [S22]
        rw [show (⟨5, hk⟩ : Fin 22) = 5 from rfl, st_v5,
          Function.update_of_ne (w22_ne_mcell _).symm]
        show G4 (level0RowsBank M G n c F Q P) (Sum.inl (mc .Y)) = _
        rw [WeightedLevel0Masters.ready_master M G n c F Q P .Y
          (by intro h; cases h) (by intro h; cases h) (by intro m h; cases h)]
        exact (WeightedLevel0Masters.masterC_values M G n c).2.2.1
    · have hm : costEmb (.inl ⟨k, hk⟩) = .inr (.inl ⟨k - 6, by omega⟩) := by
        show costMap (.inl ⟨k, hk⟩) = _
        simp only [costMap, dif_neg h6]
      rw [hm, U_cell, st_tmp _ _ _ _ _ _ k hk h6]
      rfl
  · show ext (S22 M G n c F Q P) (.inr (.inr l)) = U _ (.inr l)
    rw [U_log]
    rfl

/-- The level-1 cost word, from the level-0 data (owner-5 `cost_word_succ` at `j = 0`). -/
theorem level0_cost_word (G : EndpointGraph V E) (n c : ℕ) (hc : 1 ≤ c) :
    List.replicate (costTarget (Parameters.scale (P0 G n c)) (EffectiveIteration.sourceDepth n) c
        (Parameters.bins (P0 G n c)) (Fintype.card E)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget) true =
      ETHParameterScaleMachineInput.words
        (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) (0 + 1)) 2 := by
  have hw := NextCostWords.cost_word_succ G c (EffectiveIteration.sourceDepth n) 0
    (IterationComplete.sourceDepth_pos n) hc
  have hrp : EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)) 0 = P0 G n c := rfl
  rw [hrp] at hw
  rw [hw]
  have hcost : (P0 G n c).cost = (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget + 0 :=
    rfl
  unfold costTarget
  rw [hcost]
  simp only [Nat.add_zero]

#print axioms srcCell_inj
#print axioms costMap_inj
#print axioms level0_cost_inputs
#print axioms level0_cost_word

end
end EthInapproximability.CurrentPaper.Level0CostRound
