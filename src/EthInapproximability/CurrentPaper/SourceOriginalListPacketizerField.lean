import EthInapproximability.CurrentPaper.SourceOriginalListPacketizerInvariant

/-! The physically embedded extraction of one canonical sparse-CNF field. -/

namespace EthInapproximability.CurrentPaper.SourceOriginalListPacketizer

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication

noncomputable section

def fieldFrame (S : Stack → List Bool)
    (c : SourceListMachineFields.Config) : Config :=
  BitMachineStackEmbedding.cfg fieldStack S fieldLabel fieldControl
    (some (adminLabel .afterField)) c

theorem fieldFrame_initial (S : Stack → List Bool) (word suffix : List Bool)
    (hinput : S (.inr 0) = natField word.length ++ (word ++ suffix))
    (hsaved : S (.inr 1) = [])
    (htwo : S (.inr 5) = [])
    (hthree : S (.inr 6) = [])
    (hfour : S (.inr 7) = [])
    (hfive : S (.inr 8) = [])
    (hword : S (.inl SourceOriginalPacketFraming.wordStack) = []) :
    fieldFrame S (SourceListMachineFields.cfg (some (.inl .scan))
      SourceListMachineFields.initialControl
      {input := natField word.length ++ (word ++ suffix)}) =
    ⟨some (fieldLabel (.inl .scan)),
      fieldControl SourceListMachineFields.initialControl,S⟩ := by
  have h : ∀ k : SourceListMachineFields.Stack,
      (SourceListMachineFields.cfg (some (.inl .scan))
        SourceListMachineFields.initialControl
        {input := natField word.length ++ (word ++ suffix)}).stk k =
      S (fieldStack k) := by
    intro k
    fin_cases k
    · exact hinput.symm
    · exact hsaved.symm
    · exact htwo.symm
    · exact hthree.symm
    · exact hfour.symm
    · exact hfive.symm
    · exact hword.symm
  unfold fieldFrame BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg
  simp only [BitMachineInline.cfg]
  rw [BitMachineStackEmbedding.bank_eq_self fieldStack _ _ h]
  rfl

theorem fieldFrame_halted (S : Stack → List Bool)
    (v : SourceListMachineFields.Control) (d : SourceListMachineFields.Data) :
    fieldFrame S (SourceListMachineFields.cfg none v d) =
      ⟨some (adminLabel .afterField), fieldControl v,
        BitMachineStackEmbedding.bank fieldStack S d.stacks⟩ := rfl

theorem field_embedded (S : Stack → List Bool) (word suffix : List Bool) :
    ∃ t ≤ 20*(word.length+1)*(word.length.bits.length+1),
      run t (fieldFrame S (SourceListMachineFields.cfg
        (some (.inl .scan)) SourceListMachineFields.initialControl
        {input := natField word.length ++ (word ++ suffix)})) =
      fieldFrame S (SourceListMachineFields.success word suffix) := by
  obtain ⟨t, ht, he⟩ := SourceListMachineFields.field_encoded word suffix
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs fieldStack S
    fieldLabel fieldControl (fun v => v.1.1.2)
    (by intro v; rfl) (some (adminLabel .afterField))
    SourceListMachineFields.program program (fun _ => rfl)
    (SourceListMachineFields.cfg (some (.inl .scan))
      SourceListMachineFields.initialControl
      {input := natField word.length ++ (word ++ suffix)}) t
    (by change (SourceListMachineFields.run t _).l = none
        rw [he]; rfl)
  change run u (fieldFrame S _) = fieldFrame S (SourceListMachineFields.run t _) at hr
  rw [he] at hr
  exact ⟨u,hu.trans ht,hr⟩

theorem afterCounter_positive (S : Stack → List Bool) :
    advance program
      ⟨some (adminLabel .afterCounter),
        counterControl (SourceListMachineCounter.doneControl true), S⟩ =
      ⟨some (fieldLabel (.inl .scan)),
        fieldControl SourceListMachineFields.initialControl,S⟩ := by
  simp only [advance, adminLabel, program, TM2.step, TM2.stepAux, Option.getD_some]
  simp [counterControl, SourceListMachineCounter.doneControl]

theorem afterField_positive (S : Stack → List Bool) :
    advance program
      ⟨some (adminLabel .afterField),
        fieldControl (SourceListMachineFields.coreControl (some true,false)),S⟩ =
      ⟨some (frameLabel frameStartLabel),frameControl frameInitialControl,S⟩ := by
  simp only [advance, adminLabel, program, TM2.step, TM2.stepAux, Option.getD_some]
  simp [fieldControl, SourceListMachineFields.coreControl]

end

end EthInapproximability.CurrentPaper.SourceOriginalListPacketizer
