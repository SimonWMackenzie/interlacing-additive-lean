import EthInapproximability.CurrentPaper.EntryPrepBudget
import EthInapproximability.CurrentPaper.OuterLevel0Full

/-!
# Segment 6 (interface split): the matrix-word input cell of the writer-22 slot

Lane owner:b-stage4-entry-program-6 (Paper B, unit 2, map item 3), under root
decision R6 (10:40): the row-major matrix word `rowMajor M.entry` is an explicit
NAMED input cell of the writer-22 program, so that the level lane can bind it
(at level `j+1`: the retained output word of the previous round).

For level 0 the named cell is any known-blank cell `blankCell z` of the prep exit
(`EntryPrepBudget.exit_blank_all`). The admitted `OuterLevel0Full.Writer22Spec`
splits, with ONE charged handoff (`BitMachineRawSequence.runs`), into

* `SeedTableSpec z W₁ …`: from the exact prep exit bank, `W₁` halts on the same
  bank with the named cell set to `seedWord n = rowMajor (seedState b).matrix.entry`
  (every other cell restored);
* `Writer22From z W₂ …`: from that bank, `W₂` halts on the prep exit bank with
  writer 22 set to `d.rawBits` and the named cell consumed (blank again).

`writer22_split` proves `SeedTableSpec ∧ Writer22From → Writer22Spec` for the
sequenced program with clock `T₁ + T₂ + 1`. Pure composition: nothing is
restated from the admitted modules, nothing is assumed about `W₁`, `W₂`.
`seed_entry` records the literal entry of the level-0 matrix (MSB-first binary
row index), for the producer `W₁` (which is n-dependent, see
`EntryPrepBudget.seed_word_length_lower`).
-/

namespace EthInapproximability.CurrentPaper.EntryWriter22Split

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The level-0 matrix word. -/
def seedWord (n : ℕ) : List Bool :=
  MatrixMaterialization.rowMajor
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix.entry

/-- The level-0 writer-22 word (the word of `OuterLevel0Full.Writer22Spec`). -/
abbrev word22 (G : EndpointGraph V E) (n c : ℕ) : List Bool :=
  (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits

/-- The prep exit bank. -/
noncomputable abbrev S0 (G : EndpointGraph V E) (n c : ℕ) (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    HStack → List Bool :=
  exitBank G n c (G4 (level0RowsBank Mm G n c F Q P))

/-- Interface 1 (the level-0 matrix-word producer): the named cell gets `seedWord n`. -/
def SeedTableSpec (z : EntryPrepBudget.BlankIdx) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (G : EndpointGraph V E) (n c : ℕ) : Prop :=
  ∀ (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool),
    level0Facts Mm G n c F Q P →
    ∃ t ≤ T, ∃ v₁ : VW,
      ((advance W)^[t]) ⟨some w₀, v₀, S0 Mm G n c F Q P⟩ =
        ⟨none, v₁, Function.update (S0 Mm G n c F Q P) (EntryPrepBudget.blankCell z) (seedWord n)⟩

/-- Interface 2 (the writer-22 program with the matrix word as a named input cell):
from the prep exit bank with the named cell holding the matrix word, halt on the prep
exit bank with writer 22 set to the table word (named cell blank again). -/
def Writer22From (z : EntryPrepBudget.BlankIdx) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T : ℕ)
    (G : EndpointGraph V E) (n c : ℕ) : Prop :=
  ∀ (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool),
    level0Facts Mm G n c F Q P →
    ∃ t ≤ T, ∃ v₁ : VW,
      ((advance W)^[t])
          ⟨some w₀, v₀, Function.update (S0 Mm G n c F Q P) (EntryPrepBudget.blankCell z)
            (seedWord n)⟩ =
        ⟨none, v₁, Function.update (S0 Mm G n c F Q P) OuterLevel0Full.w22 (word22 G n c)⟩

theorem writer22_split (z : EntryPrepBudget.BlankIdx) {L1 V1 L2 V2 : Type}
    (W₁ : L1 → TM2.Stmt (fun _ : HStack => Bool) L1 V1) (w₁ : L1) (v₁ : V1) (T₁ : ℕ)
    (W₂ : L2 → TM2.Stmt (fun _ : HStack => Bool) L2 V2) (w₂ : L2) (v₂ : V2) (T₂ : ℕ)
    (G : EndpointGraph V E) (n c : ℕ)
    (h₁ : SeedTableSpec Mm z W₁ w₁ v₁ T₁ G n c) (h₂ : Writer22From Mm z W₂ w₂ v₂ T₂ G n c) :
    OuterLevel0Full.Writer22Spec Mm (BitMachineRawSequence.program W₁ W₂ w₂ v₁ v₂)
      (BitMachineRawSequence.leftLabel w₁) (v₁, v₂) (T₁ + T₂ + 1) G n c := by
  intro F Q P hf
  obtain ⟨t₁, ht₁, u₁, r₁⟩ := h₁ F Q P hf
  obtain ⟨t₂, ht₂, u₂, r₂⟩ := h₂ F Q P hf
  obtain ⟨t, ht, r⟩ := BitMachineRawSequence.runs W₁ W₂ w₁ w₂ v₁ u₁ v₂ u₂
    (S0 Mm G n c F Q P)
    (Function.update (S0 Mm G n c F Q P) (EntryPrepBudget.blankCell z) (seedWord n))
    (Function.update (S0 Mm G n c F Q P) OuterLevel0Full.w22 (word22 G n c)) t₁ t₂ r₁ r₂
  exact ⟨t, by omega, (v₁, u₂), r⟩

/-- The level-0 matrix entry: row `x` is the MSB-first binary expansion of `x`. -/
theorem seed_entry (b : ℕ) (x : Fin (Iteration.seedMatrix b).rows)
    (y : Fin (Iteration.seedMatrix b).columns) :
    (Iteration.seedMatrix b).entry x y =
      x.val.testBit (IndexSeed.width b - 1 - y.val) := by
  simp only [Iteration.seedMatrix, Iteration.number, Iteration.Numbering.tuple,
    Iteration.Numbering.fin, IndexSeed.seed, Equiv.trans_apply, Equiv.coe_fn_mk,
    Equiv.refl_apply, Equiv.piCongrLeft_refl]
  have key : ∀ k : Fin 2, finTwoEquiv k = decide (k.val = 1) := by decide
  rw [key, finFunctionFinEquiv_symm_apply_val, Nat.testBit_eq_decide_div_mod_eq, Fin.val_rev]
  have hw : IndexSeed.width b - (y.val + 1) = IndexSeed.width b - 1 - y.val := by omega
  rw [hw]

#print axioms writer22_split
#print axioms seed_entry

end EthInapproximability.CurrentPaper.EntryWriter22Split
