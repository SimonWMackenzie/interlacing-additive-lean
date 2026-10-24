import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalWordBound
import EthInapproximability.CurrentPaper.SourceCSPRowLoopCost

/-!
# Uniform charged cost for one raw source row

Every reset scratch word is bounded from the actual corrected controller's
reached yield configuration. The bound uses only the current raw suffix,
immutable unary cap, and fixed program syntax.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalUniformOne

open Turing BitMachineEncoding SourceCSPRowLoopController

def pushConstant (q H : Nat) : Nat :=
  BitMachineStackGrowth.perStep (SourceCSPRowLoopTotalController.program q H)

def resetBound (q H : Nat) (input cap : List Bool) : Nat :=
  (q * 5 + 4) *
    (cap.length + pushConstant q H *
      (1 + SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap)) +
    (q * 5 + 4) + 2 + (2 * cap.length + 2) + 1

def oneBound (q H : Nat) (input cap : List Bool) : Nat :=
  SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap + 3 +
    resetBound q H input cap

theorem reset_cost_uniform (q H : Nat) (input cap : List Bool)
    (E : Fin 4 → List Bool) (count : List Bool)
    (ty : Nat) (v : QueryControl)
    (U : SourceCSPRowQueryFrame.Stack q → List Bool)
    (hty : ty ≤ 1 + SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap)
    (hrun : ((advance (SourceCSPRowLoopTotalController.program q H))^[ty])
      (⟨some (adminLabel .check), initialControl,
        Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
      ⟨some (adminLabel .yield), queryControl v,
        Sum.elim U (Function.update E 0 count)⟩) :
    SourceCSPRowLoopIteration.resetCost q
      (Sum.elim U (Function.update E 0 count)) cap ≤
      resetBound q H input cap := by
  let S₀ : Stack q → List Bool :=
    Sum.elim (SourceCSPRowQueryFrame.initial input cap) E
  have hcell (i : Fin (q * 5 + 4)) :
      (Sum.elim U (Function.update E 0 count)
        (SourceCSPRowLoopClear.scratch q i)).length ≤
      cap.length + pushConstant q H *
        (1 + SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap) := by
    have hg := BitMachineStackGrowth.run_growth
      (SourceCSPRowLoopTotalController.program q H)
      (⟨some (adminLabel .check), initialControl, S₀⟩ : Config q H)
      ty (SourceCSPRowLoopClear.scratch q i)
    rw [hrun] at hg
    have hi := SourceCSPRowLoopCost.initial_scratch_le q input cap E i
    change (Sum.elim U (Function.update E 0 count)
      (SourceCSPRowLoopClear.scratch q i)).length ≤
      (S₀ (SourceCSPRowLoopClear.scratch q i)).length +
        pushConstant q H * ty at hg
    have hi' : (S₀ (SourceCSPRowLoopClear.scratch q i)).length ≤
        cap.length := by simpa only [S₀] using hi
    have hm := Nat.mul_le_mul_left (pushConstant q H) hty
    exact hg.trans (Nat.add_le_add hi' hm)
  have hsum : (∑ i : Fin (q * 5 + 4),
      (Sum.elim U (Function.update E 0 count)
        (SourceCSPRowLoopClear.scratch q i)).length) ≤
      (q * 5 + 4) *
        (cap.length + pushConstant q H *
          (1 + SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap)) := by
    have hs : (∑ i : Fin (q * 5 + 4),
        (Sum.elim U (Function.update E 0 count)
          (SourceCSPRowLoopClear.scratch q i)).length) ≤
        ∑ _i : Fin (q * 5 + 4),
          (cap.length + pushConstant q H *
            (1 + SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap)) := by
      apply Finset.sum_le_sum
      intro i _
      exact hcell i
    simpa only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using hs
  unfold SourceCSPRowLoopIteration.resetCost resetBound
  omega

theorem parsed_good_next_uniform (q H : Nat) (input cap : List Bool)
    (bank : SourceCSPRowController.Bank q) (rest : List Bool)
    (E : Fin 4 → List Bool) (count : List Bool)
    (hcount : E 0 = true :: count)
    (hcapE : E 1 = cap) (hscratch : E 3 = [])
    (hparse : SourceCSPRowController.readQueriesFrom (q := q) 0 input
        (fun _ => []) = some (bank, rest))
    (htable : H ≤ rest.length)
    (hrange : ∀ j : Fin q,
      EncodedCommunication.bitsValue (bank j) ≤ cap.length) :
    ∃ t,
      t ≤ oneBound q H input cap ∧
      ((advance (SourceCSPRowLoopTotalController.program q H))^[t])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
        ⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial (rest.drop H) cap)
            (Function.update E 0 count)⟩ := by
  let L := SourceCSPRowLoopTotalCombinedAll.wordBound q H input cap
  obtain ⟨hword, hcap⟩ :=
    SourceCSPRowLoopTotalWordBound.parsed_words_bounded input cap bank rest
      hparse htable
  obtain ⟨ty, tf, v, U, hty, htf, hyield, hrun⟩ :=
    SourceCSPRowLoopTotalNext.parsed_good_next q H input cap bank rest
      L E count hcount hcapE hscratch hparse htable hword hcap hrange
  have hreset := reset_cost_uniform q H input cap E count ty v U
    (by simpa only [L, SourceCSPRowLoopTotalCombinedAll.totalBound,
      SourceCSPRowLoopTotalCombinedAll.wordBound,
      SourceCSPRowLoopTotalCombinedAll.parserBound] using hty) hyield
  refine ⟨tf, ?_, hrun⟩
  unfold oneBound
  have hty' : ty ≤ 1 + SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap := by
    simpa only [L, SourceCSPRowLoopTotalCombinedAll.totalBound,
      SourceCSPRowLoopTotalCombinedAll.wordBound,
      SourceCSPRowLoopTotalCombinedAll.parserBound] using hty
  omega

theorem parsed_range_bad_uniform (q H : Nat) (input cap : List Bool)
    (bank : SourceCSPRowController.Bank q) (rest : List Bool)
    (E : Fin 4 → List Bool) (count : List Bool)
    (hcount : E 0 = true :: count)
    (hparse : SourceCSPRowController.readQueriesFrom (q := q) 0 input
        (fun _ => []) = some (bank, rest))
    (htable : H ≤ rest.length)
    (hbad : ¬ ∀ j : Fin q,
      EncodedCommunication.bitsValue (bank j) ≤ cap.length) :
    ∃ t S v,
      t ≤ oneBound q H input cap ∧
      ((advance (SourceCSPRowLoopTotalController.program q H))^[t])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
        ⟨none, (v, some false), S⟩ := by
  let L := SourceCSPRowLoopTotalCombinedAll.wordBound q H input cap
  obtain ⟨hword, hcap⟩ :=
    SourceCSPRowLoopTotalWordBound.parsed_words_bounded input cap bank rest
      hparse htable
  obtain ⟨t, S, v, ht, hr⟩ :=
    SourceCSPRowLoopTotalRangeReject.range_bad_rejects q H input cap bank rest
      L E count hcount hparse htable hword hcap hbad
  refine ⟨t, S, v, ?_, hr⟩
  have hbase : t ≤
      SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap + 3 := by
    simpa only [L, SourceCSPRowLoopTotalCombinedAll.totalBound,
      SourceCSPRowLoopTotalCombinedAll.wordBound,
      SourceCSPRowLoopTotalCombinedAll.parserBound] using ht
  unfold oneBound
  omega

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalUniformOne
