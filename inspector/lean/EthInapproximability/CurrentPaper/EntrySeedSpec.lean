import EthInapproximability.CurrentPaper.SeedTable
import EthInapproximability.CurrentPaper.EntryWriter22Split
import EthInapproximability.CurrentPaper.EntryLevelWords

/-!
# Segment 5/6: the level-0 matrix word produced on the prep exit bank

Lane owner:b-stage4-entry-program-6 (Paper B, unit 2, map item 3).

* `seed_word_rows`: the level-0 matrix word `rowMajor (seedMatrix b).entry` is
  literally `SeedLoop.rows (width b) (2 ^ width b - 1)` (row `y` = MSB-first bits of `y`).
* `seed_table_spec`: the fixed program `SeedTable.program (wcell 27) tmpH (mcell .N) oCell`
  discharges `EntryWriter22Split.SeedTableSpec zO` on the ACTUAL prep exit bank, with the
  public clock `SeedTable.bound (width (sourceDepth n))`: the counter's unary width is
  read from writer 27 (`cy = M.columns = width b`, owner-5 `exit_writer_words`), every
  scratch cell is known blank there (`P6Budget`), and the exit bank is EXACT (only the
  named cell `oCell = blankCell zO` changes, to the matrix word).
* `level0_writer22_of_from`: hence `OuterLevel0Full.Writer22Spec` follows from the single
  remaining interface `Writer22From zO …` (the writer-22 program with the matrix word as
  the named input cell `oCell`), with clock `bound + T₂ + 1`.
-/

namespace EthInapproximability.CurrentPaper.EntrySeedSpec

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open SeedLoop

/-! ## The word identity -/

theorem bitsLE_getElem (w y i : ℕ) (h : i < (bitsLE w y).length) :
    (bitsLE w y)[i] = y.testBit i := by
  induction w generalizing y i with
  | zero => simp [bitsLE] at h
  | succ w ih =>
      cases i with
      | zero => simp [bitsLE, Nat.testBit_zero]
      | succ i =>
          simp only [bitsLE, List.getElem_cons_succ]
          rw [ih, Nat.testBit_succ]

theorem row_eq (w y : ℕ) :
    (bitsLE w y).reverse = List.ofFn (fun j : Fin w => y.testBit (w - 1 - j.val)) := by
  apply List.ext_getElem
  · simp [bitsLE_length]
  · intro k h1 h2
    rw [List.getElem_reverse, bitsLE_getElem, List.getElem_ofFn]
    congr 1
    simp only [bitsLE_length]

theorem rowMajor_flatten {r c : ℕ} (f : Fin r → Fin c → Bool) :
    MatrixMaterialization.rowMajor f =
      (List.ofFn fun i : Fin r => List.ofFn fun j : Fin c => f i j).flatten := by
  unfold MatrixMaterialization.rowMajor
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext i
  congr 1
  funext j
  have key : ∀ k : Fin (r * c), k.val = i.val * c + j.val → finProdFinEquiv.symm k = (i, j) := by
    intro k hk
    rw [Equiv.symm_apply_eq]
    ext
    simp only [finProdFinEquiv_apply_val, hk]
    ring
  rw [key _ rfl]

theorem rows_of_entries {r c : ℕ} (w N : ℕ) (f : Fin r → Fin c → Bool) (hr : r = N + 1)
    (hc : c = w) (hf : ∀ i j, f i j = i.val.testBit (w - 1 - j.val)) :
    (List.ofFn fun i : Fin r => List.ofFn fun j : Fin c => f i j).flatten = rows w N := by
  subst hr hc
  unfold rows
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  rw [row_eq]
  apply List.ofFn_inj.mpr
  funext j
  exact hf i j

theorem seed_word_rows (b : ℕ) :
    MatrixMaterialization.rowMajor (Iteration.seedMatrix b).entry =
      rows (IndexSeed.width b) (2 ^ IndexSeed.width b - 1) := by
  have hN : (Iteration.seedMatrix b).rows = 2 ^ IndexSeed.width b - 1 + 1 := by
    have : 1 ≤ 2 ^ IndexSeed.width b := Nat.one_le_two_pow
    rw [EntryPrepBudget.seed_rows]
    omega
  rw [rowMajor_flatten]
  exact rows_of_entries _ _ _ hN (EntryPrepBudget.seed_cols b)
    (fun i j => EntryWriter22Split.seed_entry b i j)

/-! ## The producer on the prep exit bank -/

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The first double-interlace cell (known blank at the prep exit). -/
noncomputable def d0 : EntryPrepBudget.DStack :=
  (Fintype.equivFin EntryPrepBudget.DStack).symm ⟨0, by rw [EntryPrepBudget.card_dstack]; decide⟩

/-- The named matrix-word cell. -/
noncomputable def zO : EntryPrepBudget.BlankIdx := .inr (.inr (.inr (.inl d0)))
noncomputable def oCell : HStack := EntryPrepBudget.blankCell zO

theorem slots_inj : Function.Injective ![wcell 27, tmpH, mcell .N] := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | (exfalso; cases h)

theorem tmp_ne_o : tmpH ≠ oCell := by intro h; cases h
theorem n_ne_o : mcell .N ≠ oCell := by intro h; cases h

/-- ONE fixed producer program on the level stack. -/
noncomputable def seedProgram :=
  SeedTable.program (wcell 27) tmpH (mcell .N) oCell slots_inj

theorem seed_table_spec (G : EndpointGraph V E) (n c : ℕ) :
    EntryWriter22Split.SeedTableSpec Mm zO seedProgram SeedTable.startLabel
      ((none : Option Bool), (none : Option Bool))
      (SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n))) G n c := by
  intro F Q P hf
  have hW := (EntryLevelWords.exit_writer_words Mm G n c F Q P hf).2.2.1
  obtain ⟨t, ht, hr⟩ := SeedTable.seed_table_run (wcell 27) tmpH (mcell .N) oCell slots_inj
    tmp_ne_o n_ne_o (EntryWriter22Split.S0 Mm G n c F Q P)
    (IndexSeed.width (EffectiveIteration.sourceDepth n)) hW
    (EntryExitBlank.exit_blank_tmp G n c _) (EntryPrepBudget.exit_blank_N Mm G n c F Q P)
    (EntryPrepBudget.exit_blank_all Mm G n c F Q P zO)
  refine ⟨t, ht, ((none : Option Bool), (none : Option Bool)), ?_⟩
  unfold seedProgram
  rw [hr]
  unfold EntryWriter22Split.seedWord
  rw [show (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix =
    Iteration.seedMatrix (EffectiveIteration.sourceDepth n) from rfl, seed_word_rows]
  rfl

/-- `Writer22Spec` from the one remaining interface. -/
theorem level0_writer22_of_from (G : EndpointGraph V E) (n c : ℕ) {L2 V2 : Type}
    (W₂ : L2 → TM2.Stmt (fun _ : HStack => Bool) L2 V2) (w₂ : L2) (v₂ : V2) (T₂ : ℕ)
    (h₂ : EntryWriter22Split.Writer22From Mm zO W₂ w₂ v₂ T₂ G n c) :
    OuterLevel0Full.Writer22Spec Mm
      (BitMachineRawSequence.program seedProgram W₂ w₂
        ((none : Option Bool), (none : Option Bool)) v₂)
      (BitMachineRawSequence.leftLabel SeedTable.startLabel)
      (((none : Option Bool), (none : Option Bool)), v₂)
      (SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) + T₂ + 1) G n c :=
  EntryWriter22Split.writer22_split Mm zO seedProgram SeedTable.startLabel
    ((none : Option Bool), (none : Option Bool))
    (SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n))) W₂ w₂ v₂ T₂ G n c
    (seed_table_spec Mm G n c) h₂

#print axioms bitsLE_getElem
#print axioms row_eq
#print axioms rowMajor_flatten
#print axioms seed_word_rows
#print axioms slots_inj
#print axioms seed_table_spec
#print axioms level0_writer22_of_from

end EthInapproximability.CurrentPaper.EntrySeedSpec
