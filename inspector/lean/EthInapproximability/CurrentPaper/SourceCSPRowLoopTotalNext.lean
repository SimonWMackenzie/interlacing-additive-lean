import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRangeReject

/-!
# Reusing the same bank after one accepted arbitrary row

On a physically parsed, in-range row, the corrected controller performs the
same charged clear and cap-restoration program as the canonical path. The
next unread suffix is the actual suffix left by the parser, not a supplied
row-list oracle.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalNext

open Turing BitMachineEncoding SourceCSPRowLoopController

theorem parsed_good_next (q H : Nat) (input cap : List Bool)
    (bank : SourceCSPRowController.Bank q) (rest : List Bool)
    (L : Nat) (E : Fin 4 → List Bool) (count : List Bool)
    (hcount : E 0 = true :: count)
    (hcapE : E 1 = cap) (hscratch : E 3 = [])
    (hparse : SourceCSPRowController.readQueriesFrom (q := q) 0 input
        (fun _ => []) = some (bank, rest))
    (htable : H ≤ rest.length)
    (hword : ∀ j : Fin q, (bank j).length ≤ L)
    (hcap : cap.length ≤ L)
    (hrange : ∀ j : Fin q,
      EncodedCommunication.bitsValue (bank j) ≤ cap.length) :
    ∃ ty tf v U,
      ty ≤ 1 + (q * (2 * input.length + 4) + 2 * H + 3 +
        q * (100 * (L + 1) ^ 2) + 2) ∧
      tf ≤ ty + 1 + SourceCSPRowLoopIteration.resetCost q
        (Sum.elim U (Function.update E 0 count)) cap ∧
      ((advance (SourceCSPRowLoopTotalController.program q H))^[ty])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
        ⟨some (adminLabel .yield), queryControl v,
          Sum.elim U (Function.update E 0 count)⟩ ∧
      ((advance (SourceCSPRowLoopTotalController.program q H))^[tf])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
        ⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial (rest.drop H) cap)
            (Function.update E 0 count)⟩ := by
  obtain ⟨ty, v, U, b, hty, hyield, hsource, hparser, hquery, hb⟩ :=
    SourceCSPRowLoopTotalParsed.parsed_row_yield q H input cap bank rest L E count
      hcount hparse htable hword hcap
  have hbtrue : b = true := hb.mpr hrange
  let E' := Function.update E 0 count
  let S : Stack q → List Bool := Sum.elim U E'
  have hcap' : S (.inr 1) = cap := by
    simpa only [S, E', Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)]
      using hcapE
  have hscratch' : S (.inr 3) = [] := by
    simpa only [S, E', Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0)]
      using hscratch
  obtain ⟨tr, htr, hreset⟩ := SourceCSPRowLoopTotalOne.reset_lift q H
    S (rest.drop H) cap hsource hcap' hscratch'
  have hstep := SourceCSPRowLoopTotalController.yield_success q H S v
    (rest.take H) hparser (by simpa only [hbtrue] using hquery)
  have hafter : ((advance (SourceCSPRowLoopTotalController.program q H))^[1 + ty])
      (⟨some (adminLabel .check), initialControl,
        Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
      ⟨some (resetLabel (BitMachineRawSequence.leftLabel 0)),
        initialControl, S⟩ := by
    rw [Function.iterate_add_apply, hyield, Function.iterate_one]
    exact hstep
  have hwhole : ((advance (SourceCSPRowLoopTotalController.program q H))^[ty + 1 + tr])
      (⟨some (adminLabel .check), initialControl,
        Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
      ⟨some (adminLabel .check), initialControl,
        Sum.elim (SourceCSPRowQueryFrame.initial (rest.drop H) cap) E'⟩ := by
    rw [show ty + 1 + tr = tr + (1 + ty) by omega,
      Function.iterate_add_apply, hafter]
    simpa only [S, E'] using hreset
  refine ⟨ty, ty + 1 + tr, v, U, hty, ?_, hyield, ?_⟩
  · have htr' : tr ≤ SourceCSPRowLoopIteration.resetCost q
        (Sum.elim U (Function.update E 0 count)) cap := by
      simpa only [S, E'] using htr
    omega
  · simpa only [E'] using hwhole

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalNext
