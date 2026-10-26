import EthInapproximability.CurrentPaper.SourceListMachineOuter

/-! The literal initialized bank is kept in embedded form. Projections are
proved separately so that Lean need not normalize every foreign stack at once. -/

namespace EthInapproximability.CurrentPaper.SourceListMachineOuter

open Turing TM2.Stmt BitMachine BitMachineEncoding

variable (M : Machine)

def banks (source count accumulator finalOutput : List Bool) : Stack M → List Bool :=
  Sum.elim (Sum.elim (fun _ : Fin M.stackCount => [])
    (SourceListMachineItem.foreign source [] [] [] accumulator))
    ![count,[],finalOutput]

noncomputable def initBanks (source : List Bool) (d : SourceListMachineInitialize.Data)
    (finalOutput : List Bool) : Stack M → List Bool :=
  BitMachineStackEmbedding.bank (initStack M)
    (banks M source [] [] finalOutput) d.stacks

theorem init_input (source : List Bool) (d : SourceListMachineInitialize.Data)
    (finalOutput : List Bool) :
    initBanks M source d finalOutput (.inl (.inr 0)) = d.input :=
  BitMachineStackEmbedding.bank_at (initStack M) _ d.stacks 0

theorem init_saved (source : List Bool) (d : SourceListMachineInitialize.Data)
    (finalOutput : List Bool) :
    initBanks M source d finalOutput (.inl (.inr 1)) = d.saved :=
  BitMachineStackEmbedding.bank_at (initStack M) _ d.stacks 1

theorem init_count (source : List Bool) (d : SourceListMachineInitialize.Data)
    (finalOutput : List Bool) :
    initBanks M source d finalOutput (.inr 0) = d.count :=
  BitMachineStackEmbedding.bank_at (initStack M) _ d.stacks 2

theorem init_temp (source : List Bool) (d : SourceListMachineInitialize.Data)
    (finalOutput : List Bool) :
    initBanks M source d finalOutput (.inr 1) = d.temp :=
  BitMachineStackEmbedding.bank_at (initStack M) _ d.stacks 3

theorem init_accumulator (source : List Bool) (d : SourceListMachineInitialize.Data)
    (finalOutput : List Bool) :
    initBanks M source d finalOutput (.inl (.inr 7)) = d.output :=
  BitMachineStackEmbedding.bank_at (initStack M) _ d.stacks 4

def run (n : Nat) (c : Config M) : Config M := ((advance (program M))^[n]) c

theorem run_succ {c c' : Config M} (h : advance (program M) c = c') (n : Nat) :
    run M (n+1) c = run M n c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run M n) h)

theorem run_add {c c' : Config M} {n : Nat} (h : run M n c = c') (m : Nat) :
    run M (n+m) c = run M m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run M m) h

noncomputable def initFrame (source : List Bool)
    (c : SourceListMachineInitialize.Config) : Config M :=
  BitMachineStackEmbedding.cfg (initStack M) (banks M source [] [] [])
    (initLabel M) (initControl M) (some (adminLabel M .afterInit)) c

theorem initFrame_initial (source : List Bool) :
    initFrame M source (SourceListMachineInitialize.cfg (some (.inl .scan))
      SourceListMachineInitialize.initialControl {input := source}) =
    ⟨some (initLabel M (.inl .scan)),
      initControl M SourceListMachineInitialize.initialControl,
      banks M source [] [] []⟩ := by
  have h : ∀ k : SourceListMachineInitialize.Stack,
      (SourceListMachineInitialize.Data.stacks {input := source}) k =
        banks M source [] [] [] (initStack M k) := by
    intro k
    fin_cases k <;> rfl
  unfold initFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
  simp only [BitMachineInline.cfg, SourceListMachineInitialize.cfg]
  rw [BitMachineStackEmbedding.bank_eq_self (initStack M) _ _ h]

theorem banks_raw (source : List Bool) :
    banks M source [] [] [] =
      (rawInit (.inl (.inr 0) : Stack M) (adminLabel M .startInit)
        (initialControl M) source).stk := by
  funext k
  cases k with
  | inl k =>
      cases k with
      | inl k => simp [banks, rawInit, SourceListMachineItem.foreign]
      | inr k => fin_cases k <;> simp [banks, rawInit, SourceListMachineItem.foreign]
  | inr k => fin_cases k <;> simp [banks, rawInit]

theorem start_step (source : List Bool) :
    advance (program M)
      (rawInit (.inl (.inr 0) : Stack M) (adminLabel M .startInit)
        (initialControl M) source) =
      initFrame M source (SourceListMachineInitialize.cfg (some (.inl .scan))
        SourceListMachineInitialize.initialControl {input := source}) := by
  rw [initFrame_initial]
  have hb := banks_raw M source
  simp only [advance, rawInit, adminLabel, program, TM2.step, TM2.stepAux,
    Option.getD_some]
  congr 1
  exact hb.symm

theorem init_embedded (n : Nat) (suffix source : List Bool) :
    ∃ t ≤ 5 * n.bits.length + 5,
      run M t (initFrame M source
        (SourceListMachineInitialize.cfg
          (some (.inl .scan)) SourceListMachineInitialize.initialControl
          {input := EncodedCommunication.natField n ++ suffix})) =
        initFrame M source
          (SourceListMachineInitialize.cfg none
            (SourceListMachineInitialize.doneControl true)
            {input := suffix, count := n.bits,
              output := (EncodedCommunication.natField n).reverse}) := by
  obtain ⟨t, ht, he⟩ := SourceListMachineInitialize.init_encoded n suffix []
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs (initStack M)
    (banks M source [] [] [])
    (initLabel M) (initControl M) (fun v => v.1.1.2)
    (by intro v; rfl) (some (adminLabel M .afterInit))
    SourceListMachineInitialize.program (program M) (fun _ => rfl)
    (SourceListMachineInitialize.cfg (some (.inl .scan))
      SourceListMachineInitialize.initialControl
      {input := EncodedCommunication.natField n ++ suffix}) t
    (by change (SourceListMachineInitialize.run t _).l = none; rw [he]; rfl)
  change run M u (initFrame M source _) =
    initFrame M source (SourceListMachineInitialize.run t _) at hr
  rw [he] at hr
  simp only [List.append_nil] at hr
  exact ⟨u, hu.trans ht, hr⟩

theorem init_from_raw (n : Nat) (suffix : List Bool) :
    ∃ t ≤ 5*n.bits.length+6,
      run M t
        (rawInit (.inl (.inr 0) : Stack M) (adminLabel M .startInit)
          (initialControl M) (EncodedCommunication.natField n ++ suffix)) =
        initFrame M (EncodedCommunication.natField n ++ suffix)
          (SourceListMachineInitialize.cfg none
            (SourceListMachineInitialize.doneControl true)
            {input := suffix, count := n.bits,
              output := (EncodedCommunication.natField n).reverse}) := by
  obtain ⟨t, ht, hr⟩ := init_embedded M n suffix
    (EncodedCommunication.natField n ++ suffix)
  exact ⟨t+1, by omega, (run_succ M (start_step M _) t).trans hr⟩

theorem initFrame_halted (source : List Bool) (d : SourceListMachineInitialize.Data) :
    initFrame M source
      (SourceListMachineInitialize.cfg none
        (SourceListMachineInitialize.doneControl true) d) =
      ⟨some (adminLabel M .afterInit),
        initControl M (SourceListMachineInitialize.doneControl true),
        initBanks M source d []⟩ := rfl

end EthInapproximability.CurrentPaper.SourceListMachineOuter
