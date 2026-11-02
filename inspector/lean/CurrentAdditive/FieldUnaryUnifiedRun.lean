import CurrentAdditive.FieldUnaryUnifiedBank

/-! The literal unary initializer, first-passing field search, and packed
field-list printer run as one fixed TM2 program. -/

namespace CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FiniteFieldMachine
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

def prepTime (d n : Nat) : Nat := 2*d+d/2+2*n+7

theorem prep_phase (d n : Nat) (hd : 0 < d) :
    ∃ u ≤ prepTime d n,
      run u (initialConfig d n) =
        BitMachineStackEmbedding.cfg prepSlots (initialStack d n)
          Label.prep prepEmbed (some (.field (.search (.outer .initial))))
          (Prep.prepared d n) := by
  have hhalt :
      (((advance Prep.program)^[prepTime d n]) (Prep.initial d n)).l = none := by
    simpa only [prepTime, CurrentAdditive.FieldSearchCompletion.FieldUnaryBankPrep.run] using
      congrArg TM2.Cfg.l (Prep.run_prepare d n hd)
  obtain ⟨u, hu, hrun⟩ :=
    BitMachineStackEmbedding.outputs prepSlots (initialStack d n)
      Label.prep prepEmbed Prod.fst
      (by intro s; rfl)
      (some (.field (.search (.outer .initial))))
      Prep.program program (by intro l; rfl)
      (Prep.initial d n) (prepTime d n) hhalt
  refine ⟨u, hu, ?_⟩
  rw [initial_eq_frame]
  rw [run_eq_any (inferInstance : DecidableEq Stack)]
  exact hrun.trans (congrArg
    (BitMachineStackEmbedding.cfg prepSlots (initialStack d n)
      Label.prep prepEmbed (some (.field (.search (.outer .initial)))))
    (by simpa only [prepTime,
        CurrentAdditive.FieldSearchCompletion.FieldUnaryBankPrep.run] using
      Prep.run_prepare d n hd))

def fieldStart (d n : Nat) :
    CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.Config :=
  CurrentAdditive.FieldSearchCompletion.concreteShadowFreeStart d n
    (CurrentAdditive.FieldSearchCompletion.initialConfig d)

theorem prepared_eq_field_frame (d n : Nat) :
    BitMachineStackEmbedding.cfg prepSlots (initialStack d n)
      Label.prep prepEmbed (some (.field (.search (.outer .initial))))
      (Prep.prepared d n) =
    BitMachineStackEmbedding.cfg fieldSlots (preparedStack d n)
      Label.field fieldEmbed none (fieldStart d n) := by
  have hprep := prepared_eq_frame d n
  have hfield : BitMachineStackEmbedding.bank fieldSlots (preparedStack d n)
      (fieldStart d n).stk = preparedStack d n := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    simpa only [fieldStart,
      CurrentAdditive.FieldSearchCompletion.concreteShadowFreeStart,
      CurrentAdditive.FieldSearchCompletion.initialConfig,
      preparedStack, Sum.elim_inr] using
      (congrFun (visible_eq_shadowFree d n) k).symm
  simp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  rw [hprep, hfield]
  rfl

theorem field_phase (d n t : Nat)
    (hhalt :
      (CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.run t
        (fieldStart d n)).l = none) :
    ∃ u ≤ t,
      run u (BitMachineStackEmbedding.cfg fieldSlots (preparedStack d n)
        Label.field fieldEmbed none (fieldStart d n)) =
      BitMachineStackEmbedding.cfg fieldSlots (preparedStack d n)
        Label.field fieldEmbed none
        (CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.run t
          (fieldStart d n)) := by
  have hhalt' :
      (((advance CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.program)^[t])
        (fieldStart d n)).l = none := by
    rw [← CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.run_eq_any
      (inferInstance : DecidableEq FieldSearchPrinterHandoff.Stack)]
    exact hhalt
  obtain ⟨u, hu, hrun⟩ :=
    BitMachineStackEmbedding.outputs fieldSlots (preparedStack d n)
      Label.field fieldEmbed Prod.snd
      (by intro s; rfl) none
      CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.program
      program (by intro l; rfl) (fieldStart d n) t hhalt'
  exact ⟨u, hu, by
    rw [run_eq_any (inferInstance : DecidableEq Stack)]
    exact hrun.trans (by
      rw [← CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.run_eq_any
        (inferInstance : DecidableEq FieldSearchPrinterHandoff.Stack)])⟩

theorem physical_firstPassing_packed_from_unary (d n : Nat) (hd : 0 < d) :
    ∃ c < 2 ^ d,
      CurrentAdditive.FiniteFieldConstructor.TrialSearch.firstPassing d =
        some (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c) ∧
      ∃ t ≤ prepTime d n +
          55 * 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2 + 2 +
          FieldListOutputMachine.timeBound d c n,
        (run t (initialConfig d n)).l = none ∧
        (run t (initialConfig d n)).stk
          (fieldSlots (printerSlots FieldListOutputMachine.output)) =
          CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.packedBits d c n := by
  obtain ⟨c, hc, hfirst, tf, htf, hhalt, hp⟩ :=
    CurrentAdditive.FieldSearchCompletion.physical_firstPassing_packed_shadowFree
      d n hd
  obtain ⟨up, hup, hprep⟩ := prep_phase d n hd
  have hfieldhalt :
      (CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.run tf
        (fieldStart d n)).l = none := hhalt
  obtain ⟨uf, huf, hfield⟩ := field_phase d n tf hfieldhalt
  have hfull :
      run (up + uf) (initialConfig d n) =
      BitMachineStackEmbedding.cfg fieldSlots (preparedStack d n)
        Label.field fieldEmbed none
        (CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.run tf
          (fieldStart d n)) := by
    rw [run_add, hprep, prepared_eq_field_frame]
    exact hfield
  refine ⟨c, hc, hfirst, up + uf, ?_, ?_, ?_⟩
  · omega
  · rw [hfull]
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hfieldhalt]
  · rw [hfull]
    rw [show (BitMachineStackEmbedding.cfg fieldSlots (preparedStack d n)
        Label.field fieldEmbed none
        (CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.run tf
          (fieldStart d n))).stk
        (fieldSlots (printerSlots FieldListOutputMachine.output)) =
      (CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.run tf
        (fieldStart d n)).stk
          (printerSlots FieldListOutputMachine.output) from by
        exact BitMachineStackEmbedding.bank_at fieldSlots _ _ _]
    exact hp

#print axioms physical_firstPassing_packed_from_unary

end CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine
