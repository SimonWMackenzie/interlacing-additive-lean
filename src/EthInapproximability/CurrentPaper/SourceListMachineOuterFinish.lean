import EthInapproximability.CurrentPaper.SourceListMachineOuterCanonical

/-! Zero-count, empty-tail check, and final physical accumulator reversal. -/

namespace EthInapproximability.CurrentPaper.SourceListMachineOuter

open Turing TM2.Stmt BitMachine BitMachineEncoding

variable (M : Machine)

theorem afterCounter_zero (S : Stack M → List Bool) :
    advance (program M)
      ⟨some (adminLabel M .afterCounter),
        counterControl M (SourceListMachineCounter.doneControl false), S⟩ =
      ⟨some (adminLabel M .checkTail),
        counterControl M (SourceListMachineCounter.doneControl false), S⟩ := by
  simp only [advance, adminLabel, program, TM2.step, TM2.stepAux,
    Option.getD_some]
  rfl

theorem checkTail_empty (S : Stack M → List Bool) (hsource : S (.inl (.inr 0)) = []) :
    advance (program M)
      ⟨some (adminLabel M .checkTail),
        counterControl M (SourceListMachineCounter.doneControl false), S⟩ =
      ⟨some (adminLabel M .finalize),
        counterControl M (SourceListMachineCounter.doneControl false), S⟩ := by
  simp only [advance, adminLabel, program, TM2.step, TM2.stepAux,
    Option.getD_some, hsource, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false]
  rw [← hsource, Function.update_eq_self]
  rfl

theorem done_step (S : Stack M → List Bool) (v : Control M) :
    advance (program M) ⟨some (adminLabel M .done),v,S⟩ =
      ⟨none,accepted M v,S⟩ := by
  simp only [advance, adminLabel, program, TM2.step, TM2.stepAux,
    Option.getD_some]

theorem final_scan (S : Stack M → List Bool) (accumulator : List Bool)
    (hacc : S (.inl (.inr 7)) = accumulator) (hfinal : S (.inr 2) = []) :
    run M (accumulator.length+1)
      ⟨some (adminLabel M .finalize),
        counterControl M (SourceListMachineCounter.doneControl false), S⟩ =
      ⟨some (adminLabel M .done),
        counterControl M (SourceListMachineCounter.doneControl false),
        BitMachineBroadcast.contents (.inl (.inr 7)) (.inr 2) S []
          accumulator.reverse⟩ := by
  have hc : BitMachineBroadcast.contents (.inl (.inr 7)) (.inr 2) S accumulator [] = S := by
    simp only [BitMachineBroadcast.contents, ← hacc, ← hfinal,
      Function.update_eq_self]
  have hr := BitMachineBroadcast.scan_run (program M)
    (.inl (.inr (7 : Fin 8)) : Stack M) (.inr (2 : Fin 3))
    (by simp) (adminLabel M .finalize) (adminLabel M .done) rfl
    (counterControl M (SourceListMachineCounter.doneControl false)).1 none
    accumulator [] S
  rw [hc] at hr
  simpa only [run, BitMachineBroadcast.run, List.append_nil] using hr

theorem zero_finish (S : Stack M → List Bool) (q accumulator : List Bool)
    (h : LoopInvariant M S [] q accumulator) (hz : EncodedCommunication.bitsValue q = 0) :
    ∃ c : Config M, ∃ t ≤ 4*q.length+accumulator.length+9,
      run M t (loopCfg M S) = c ∧ c.l = none ∧
      c.stk (.inr 2) = accumulator.reverse := by
  have hsub : ProtocolBinaryCounter.subOne q = none := by
    cases hs : ProtocolBinaryCounter.subOne q with
    | none => rfl
    | some q' =>
        have hh := ProtocolBinaryCounter.subOne_spec q
        simp only [hs] at hh
        omega
  let T := BitMachineStackEmbedding.bank (counterStack M) S
    (SourceListMachineCounter.cfg none
      (SourceListMachineCounter.doneControl false) q []).stk
  have hT : LoopInvariant M T [] q accumulator :=
    counter_bank_invariant M S [] q q accumulator
      (SourceListMachineCounter.doneControl false) h
  obtain ⟨a, ha, hr⟩ := counter_embedded M S q
  rw [counterFrame_initial M S q h.count h.temp] at hr
  simp only [hsub] at hr
  rw [counterFrame_halted] at hr
  change run M a (loopCfg M S) =
    ⟨some (adminLabel M .afterCounter),
      counterControl M (SourceListMachineCounter.doneControl false), T⟩ at hr
  have hsource : T (.inl (.inr 0)) = [] := by
    have hh := hT.item (.inr (0 : Fin 8))
    exact hh.symm
  have hacc : T (.inl (.inr 7)) = accumulator := by
    have hh := hT.item (.inr (7 : Fin 8))
    exact hh.symm
  have h1 := afterCounter_zero M T
  have h2 := checkTail_empty M T hsource
  have h3 := final_scan M T accumulator hacc hT.final
  let U := BitMachineBroadcast.contents (.inl (.inr (7 : Fin 8))) (.inr (2 : Fin 3))
    T [] accumulator.reverse
  have h4 := done_step M U
    (counterControl M (SourceListMachineCounter.doneControl false))
  have hr1 := (run_add M hr 1).trans (run_succ M h1 0)
  have hr2 := (run_add M hr1 1).trans (run_succ M h2 0)
  have hr3 := (run_add M hr2 (accumulator.length+1)).trans h3
  have hr4 := (run_add M hr3 1).trans (run_succ M h4 0)
  refine ⟨_, a+1+1+(accumulator.length+1)+1, by omega, hr4, rfl, ?_⟩
  simp [run, U, BitMachineBroadcast.contents]

end EthInapproximability.CurrentPaper.SourceListMachineOuter
