import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalNumerical

/-!
# Total fixed-bank source-row loop on arbitrary raw suffixes

The semantic predicate below is defined from the same canonical fixed-q
parser and range relation as the physical row stage. The theorem proves
accept/reject and a uniform summed runtime for the actual one-bank controller;
the subsequent codec bridge identifies this predicate with the source codec.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalAll

open Turing BitMachineEncoding SourceCSPRowLoopController

def GoodRows (q H : Nat) (cap : List Bool) : Nat → List Bool → Prop
  | 0, input => input = []
  | m + 1, input =>
      ∃ bank rest,
        SourceCSPRowController.readQueriesFrom (q := q) 0 input
          (fun _ => []) = some (bank, rest) ∧
        H ≤ rest.length ∧
        (∀ j : Fin q, EncodedCommunication.bitsValue (bank j) ≤ cap.length) ∧
        GoodRows q H cap m (rest.drop H)

theorem zero_rows (q H : Nat) (input cap : List Bool)
    (E : Fin 4 → List Bool) (hcount : E 0 = []) :
    ∃ S v b,
      ((advance (SourceCSPRowLoopTotalController.program q H))^[3])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
        ⟨none, (v, some b), S⟩ ∧
      (b = true ↔ GoodRows q H cap 0 input) := by
  let S : Stack q → List Bool :=
    Sum.elim (SourceCSPRowQueryFrame.initial input cap) E
  have hc : S (.inr 0) = [] := hcount
  have hcheck := SourceCSPRowLoopTotalController.check_zero q H S hc
  cases input with
  | nil =>
      have hs : S (.inl (.inr 0)) = [] := rfl
      have heof := SourceCSPRowLoopTotalController.eof_empty q H S hs
      have haccept := SourceCSPRowLoopTotalController.accept_step q H S
      refine ⟨S, (queryStart, resetStart), true, ?_, by simp [GoodRows]⟩
      change advance (SourceCSPRowLoopTotalController.program q H)
        (advance (SourceCSPRowLoopTotalController.program q H)
          (advance (SourceCSPRowLoopTotalController.program q H)
            (⟨some (adminLabel .check), initialControl, S⟩ : Config q H))) = _
      rw [hcheck, heof, haccept]
  | cons b rest =>
      have hs : S (.inl (.inr 0)) = b :: rest := rfl
      have heof := SourceCSPRowLoopTotalController.eof_nonempty_full q H S b rest hs
      have hreject := SourceCSPRowLoopTotalController.reject_step q H S
        ((queryStart, resetStart), some b)
      refine ⟨S, (queryStart, resetStart), false, ?_, by simp [GoodRows]⟩
      change advance (SourceCSPRowLoopTotalController.program q H)
        (advance (SourceCSPRowLoopTotalController.program q H)
          (advance (SourceCSPRowLoopTotalController.program q H)
            (⟨some (adminLabel .check), initialControl, S⟩ : Config q H))) = _
      rw [hcheck, heof, hreject]

/-- The corrected fixed-stack controller halts on every raw row suffix. Its
Boolean result matches the recursive physical-parser/range/EOF semantics,
and the actual transition count is charged against the initial suffix. -/
theorem rows_total (q H m : Nat) (input cap : List Bool)
    (E : Fin 4 → List Bool)
    (hcount : E 0 = List.replicate m true)
    (hcap : E 1 = cap) (hscratch : E 3 = []) :
    ∃ t S v b,
      t ≤ m * SourceCSPRowLoopTotalUniformOne.oneBound q H input cap + 3 ∧
      ((advance (SourceCSPRowLoopTotalController.program q H))^[t])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial input cap) E⟩ : Config q H) =
        ⟨none, (v, some b), S⟩ ∧
      (b = true ↔ GoodRows q H cap m input) := by
  induction m generalizing input E with
  | zero =>
      obtain ⟨S, v, b, hr, hb⟩ := zero_rows q H input cap E (by simpa using hcount)
      exact ⟨3, S, v, b, by simp, hr, hb⟩
  | succ m ih =>
      have hc : E 0 = true :: List.replicate m true := by
        simpa only [List.replicate_succ] using hcount
      cases hp : SourceCSPRowController.readQueriesFrom (q := q) 0 input
          (fun _ => []) with
      | none =>
          have hbad : ¬ SourceCSPRowLoopTotalRowResult.ParseGood q H input := by
            simp [SourceCSPRowLoopTotalRowResult.ParseGood, hp]
          obtain ⟨t, S, v, ht, hr⟩ :=
            SourceCSPRowLoopTotalReject.parse_bad_rejects q H input cap E
              (List.replicate m true) hc hbad
          have hnot : ¬ GoodRows q H cap (m + 1) input := by
            simp [GoodRows, hp]
          refine ⟨t, S, v, false, ?_, hr, ?_⟩
          · have hone : t ≤ SourceCSPRowLoopTotalUniformOne.oneBound q H input cap := by
              unfold SourceCSPRowLoopTotalUniformOne.oneBound
              omega
            nlinarith
          · simp [hnot]
      | some pair =>
          obtain ⟨bank, rest⟩ := pair
          by_cases htable : H ≤ rest.length
          · by_cases hrange : ∀ j : Fin q,
                EncodedCommunication.bitsValue (bank j) ≤ cap.length
            · obtain ⟨tf, htf, hnext⟩ :=
                SourceCSPRowLoopTotalUniformOne.parsed_good_next_uniform
                  q H input cap bank rest E (List.replicate m true)
                  hc hcap hscratch hp htable hrange
              let E' := Function.update E 0 (List.replicate m true)
              have hc' : E' 0 = List.replicate m true := Function.update_self 0 _ E
              have hcap' : E' 1 = cap := by
                simpa only [E', Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)]
                  using hcap
              have hscratch' : E' 3 = [] := by
                simpa only [E', Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0)]
                  using hscratch
              obtain ⟨u, S, v, b, hu, hrun, hb⟩ :=
                ih (rest.drop H) E' hc' hcap' hscratch'
              have hsource := SourceCSPRowLoopTotalNumerical.parsed_suffix_le
                (H := H) input bank rest hp
              have hmono := SourceCSPRowLoopTotalNumerical.oneBound_mono
                q H (rest.drop H) input cap cap hsource le_rfl
              have htime : tf + u ≤
                  (m + 1) * SourceCSPRowLoopTotalUniformOne.oneBound
                    q H input cap + 3 := by
                have hm := Nat.mul_le_mul_left m hmono
                calc
                  tf + u ≤ SourceCSPRowLoopTotalUniformOne.oneBound q H input cap +
                      (m * SourceCSPRowLoopTotalUniformOne.oneBound q H
                        (rest.drop H) cap + 3) := by omega
                  _ ≤ SourceCSPRowLoopTotalUniformOne.oneBound q H input cap +
                      (m * SourceCSPRowLoopTotalUniformOne.oneBound q H input cap + 3) := by
                        omega
                  _ = (m + 1) * SourceCSPRowLoopTotalUniformOne.oneBound
                      q H input cap + 3 := by ring
              have hsem : GoodRows q H cap (m + 1) input ↔
                  GoodRows q H cap m (rest.drop H) := by
                simp [GoodRows, hp, htable, hrange]
              refine ⟨tf + u, S, v, b, htime, ?_, ?_⟩
              · rw [show tf + u = u + tf by omega,
                  Function.iterate_add_apply, hnext]
                simpa only [E'] using hrun
              · exact hb.trans hsem.symm
            · obtain ⟨t, S, v, ht, hr⟩ :=
                SourceCSPRowLoopTotalUniformOne.parsed_range_bad_uniform
                  q H input cap bank rest E (List.replicate m true)
                  hc hp htable hrange
              have hnot : ¬ GoodRows q H cap (m + 1) input := by
                simp [GoodRows, hp, htable, hrange]
              refine ⟨t, S, v, false, ?_, hr, ?_⟩
              · nlinarith
              · simp [hnot]
          · have hbad : ¬ SourceCSPRowLoopTotalRowResult.ParseGood q H input := by
              simp [SourceCSPRowLoopTotalRowResult.ParseGood, hp, htable]
            obtain ⟨t, S, v, ht, hr⟩ :=
              SourceCSPRowLoopTotalReject.parse_bad_rejects q H input cap E
                (List.replicate m true) hc hbad
            have hnot : ¬ GoodRows q H cap (m + 1) input := by
              simp [GoodRows, hp, htable]
            refine ⟨t, S, v, false, ?_, hr, ?_⟩
            · have hone : t ≤ SourceCSPRowLoopTotalUniformOne.oneBound q H input cap := by
                unfold SourceCSPRowLoopTotalUniformOne.oneBound
                omega
              nlinarith
            · simp [hnot]

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalAll
