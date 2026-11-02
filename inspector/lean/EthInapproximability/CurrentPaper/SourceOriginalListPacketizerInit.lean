import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerProgram

/-! Charged outer-header initialization with the original unary bank foreign. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizer

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

noncomputable section

def initBanks (n : ℕ) (source : List Bool)
    (d : SourceListMachineInitialize.Data) : Stack → List Bool :=
  BitMachineStackEmbedding.bank initStack (startBank n source) d.stacks

def initFrame (n : ℕ) (source : List Bool)
    (c : SourceListMachineInitialize.Config) : Config :=
  BitMachineStackEmbedding.cfg initStack (startBank n source)
    initLabel initControl (some (adminLabel .afterInit)) c

theorem initFrame_initial (n : ℕ) (source : List Bool) :
    initFrame n source
      (SourceListMachineInitialize.cfg (some (.inl .scan))
        SourceListMachineInitialize.initialControl {input := source}) =
      ⟨some (initLabel (.inl .scan)),
        initControl SourceListMachineInitialize.initialControl,
        startBank n source⟩ := by
  have h : ∀ k : SourceListMachineInitialize.Stack,
      (SourceListMachineInitialize.Data.stacks {input := source}) k =
        startBank n source (initStack k) := by
    intro k
    fin_cases k <;> simp [SourceListMachineInitialize.Data.stacks,
      startBank, initStack]
  unfold initFrame BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
  simp only [BitMachineInline.cfg, SourceListMachineInitialize.cfg]
  rw [BitMachineStackEmbedding.bank_eq_self initStack _ _ h]

theorem start_step (n : ℕ) (source : List Bool) :
    advance program (startCfg n source) =
      initFrame n source
        (SourceListMachineInitialize.cfg (some (.inl .scan))
          SourceListMachineInitialize.initialControl {input := source}) := by
  rw [initFrame_initial]
  simp only [advance, startCfg, adminLabel, program, TM2.step,
    TM2.stepAux, Option.getD_some]

theorem init_embedded (n m : ℕ) (suffix source : List Bool) :
    ∃ t ≤ 5*m.bits.length+5,
      run t (initFrame n source
        (SourceListMachineInitialize.cfg (some (.inl .scan))
          SourceListMachineInitialize.initialControl
          {input := natField m ++ suffix})) =
        initFrame n source
          (SourceListMachineInitialize.cfg none
            (SourceListMachineInitialize.doneControl true)
            {input := suffix, count := m.bits,
              output := (natField m).reverse}) := by
  obtain ⟨t, ht, he⟩ := SourceListMachineInitialize.init_encoded m suffix []
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs initStack
    (startBank n source) initLabel initControl (fun v => v.1.1.1.1)
    (by intro v; rfl) (some (adminLabel .afterInit))
    SourceListMachineInitialize.program program (fun _ => rfl)
    (SourceListMachineInitialize.cfg (some (.inl .scan))
      SourceListMachineInitialize.initialControl
      {input := natField m ++ suffix}) t
    (by change (SourceListMachineInitialize.run t _).l = none; rw [he]; rfl)
  change run u (initFrame n source _) =
    initFrame n source (SourceListMachineInitialize.run t _) at hr
  rw [he] at hr
  simp only [List.append_nil] at hr
  exact ⟨u, hu.trans ht, hr⟩

theorem init_from_start (n : ℕ) (xs : List (List Bool)) :
    ∃ t ≤ 5*xs.length.bits.length+6,
      run t (startCfg n (SourceListEncoding.encode xs)) =
        initFrame n (SourceListEncoding.encode xs)
          (SourceListMachineInitialize.cfg none
            (SourceListMachineInitialize.doneControl true)
            {input := SourceListEncoding.fields xs,
             count := xs.length.bits,
             output := (natField xs.length).reverse}) := by
  obtain ⟨t, ht, hr⟩ := init_embedded n xs.length
    (SourceListEncoding.fields xs) (SourceListEncoding.encode xs)
  have he : SourceListEncoding.encode xs =
      natField xs.length ++ SourceListEncoding.fields xs := rfl
  rw [← he] at hr
  refine ⟨t+1, by omega, ?_⟩
  rw [run, Function.iterate_succ_apply, start_step]
  exact hr

theorem initFrame_halted (n : ℕ) (source : List Bool)
    (d : SourceListMachineInitialize.Data) :
    initFrame n source
      (SourceListMachineInitialize.cfg none
        (SourceListMachineInitialize.doneControl true) d) =
      ⟨some (adminLabel .afterInit),
        initControl (SourceListMachineInitialize.doneControl true),
        initBanks n source d⟩ := rfl

end

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizer
