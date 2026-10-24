import EthInapproximability.CurrentPaper.SourceListMachineOuterInit

/-! Physical embedded binary-counter call for the outer list loop. -/

namespace EthInapproximability.CurrentPaper.SourceListMachineOuter

open Turing TM2.Stmt BitMachine BitMachineEncoding

variable (M : Machine)

noncomputable def counterFrame (S : Stack M → List Bool)
    (c : SourceListMachineCounter.Config) : Config M :=
  BitMachineStackEmbedding.cfg (counterStack M) S
    (counterLabel M) (counterControl M) (some (adminLabel M .afterCounter)) c

theorem counterFrame_initial (S : Stack M → List Bool) (q : List Bool)
    (hq : S (.inr 0) = q) (hw : S (.inr 1) = []) :
    counterFrame M S (SourceListMachineCounter.cfg (some (.inr .scan))
      SourceListMachineCounter.initialControl q []) =
      ⟨some (counterLabel M (.inr .scan)),
        counterControl M SourceListMachineCounter.initialControl, S⟩ := by
  have h : ∀ k : SourceListMachineCounter.Stack,
      (SourceListMachineCounter.cfg (some (.inr .scan))
        SourceListMachineCounter.initialControl q []).stk k = S (counterStack M k) := by
    intro k
    fin_cases k
    · exact hq.symm
    · exact hw.symm
  unfold counterFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
  simp only [BitMachineInline.cfg]
  rw [BitMachineStackEmbedding.bank_eq_self (counterStack M) _ _ h]
  rfl

theorem afterInit_step (S : Stack M → List Bool) :
    advance (program M)
      ⟨some (adminLabel M .afterInit),
        initControl M (SourceListMachineInitialize.doneControl true), S⟩ =
      ⟨some (counterLabel M (.inr .scan)),
        counterControl M SourceListMachineCounter.initialControl, S⟩ := by
  simp only [advance, adminLabel, program, TM2.step, TM2.stepAux,
    Option.getD_some]
  rfl

theorem counterFrame_halted (S : Stack M → List Bool)
    (v : SourceListMachineCounter.Control) (q : List Bool) :
    counterFrame M S (SourceListMachineCounter.cfg none v q []) =
      ⟨some (adminLabel M .afterCounter), counterControl M v,
        BitMachineStackEmbedding.bank (counterStack M) S
          (SourceListMachineCounter.cfg none v q []).stk⟩ := rfl

theorem counter_embedded (S : Stack M → List Bool) (q : List Bool) :
    ∃ t ≤ 4*q.length+5,
      run M t (counterFrame M S (SourceListMachineCounter.cfg
        (some (.inr .scan)) SourceListMachineCounter.initialControl q [])) =
      counterFrame M S
        (match ProtocolBinaryCounter.subOne q with
          | none => SourceListMachineCounter.cfg none
              (SourceListMachineCounter.doneControl false) q []
          | some q' => SourceListMachineCounter.cfg none
              (SourceListMachineCounter.doneControl true) q' []) := by
  obtain ⟨t, ht, he⟩ := SourceListMachineCounter.counter_run q
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs (counterStack M) S
    (counterLabel M) (counterControl M) (fun v => v.1.2)
    (by intro v; rfl) (some (adminLabel M .afterCounter))
    SourceListMachineCounter.program (program M) (fun _ => rfl)
    (SourceListMachineCounter.cfg (some (.inr .scan))
      SourceListMachineCounter.initialControl q []) t
    (by
      change (SourceListMachineCounter.run t _).l = none
      rw [he]
      cases ProtocolBinaryCounter.subOne q <;> rfl)
  change run M u (counterFrame M S _) =
    counterFrame M S (SourceListMachineCounter.run t _) at hr
  rw [he] at hr
  exact ⟨u, hu.trans ht, hr⟩

theorem init_to_counter (n : Nat) (suffix : List Bool) :
    ∃ t ≤ 5*n.bits.length+7,
      run M t
        (rawInit (.inl (.inr 0) : Stack M) (adminLabel M .startInit)
          (initialControl M) (EncodedCommunication.natField n ++ suffix)) =
      counterFrame M
        (initBanks M (EncodedCommunication.natField n ++ suffix)
          {input := suffix, count := n.bits,
            output := (EncodedCommunication.natField n).reverse} [])
        (SourceListMachineCounter.cfg (some (.inr .scan))
          SourceListMachineCounter.initialControl n.bits []) := by
  obtain ⟨t, ht, he⟩ := init_from_raw M n suffix
  let d : SourceListMachineInitialize.Data :=
    {input := suffix, count := n.bits,
      output := (EncodedCommunication.natField n).reverse}
  let S := initBanks M (EncodedCommunication.natField n ++ suffix) d []
  have hf := initFrame_halted M (EncodedCommunication.natField n ++ suffix) d
  change run M t _ = initFrame M _
    (SourceListMachineInitialize.cfg none
      (SourceListMachineInitialize.doneControl true) d) at he
  rw [hf] at he
  have hs := afterInit_step M S
  have hi := counterFrame_initial M S n.bits
    (init_count M _ d []) (init_temp M _ d [])
  exact ⟨t+1, by omega, by
    rw [run_add M he 1, run_succ M hs 0]
    exact hi.symm⟩

end EthInapproximability.CurrentPaper.SourceListMachineOuter
