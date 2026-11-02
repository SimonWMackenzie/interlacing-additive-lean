import CurrentAdditive.V38PublicFieldBank

namespace CurrentAdditive.V38FieldPad
open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FieldSearchCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem physical_field_pad_bank (K d n : ℕ) (hK : 0 < K) (hd : 0 < d) :
    ∃ c < 2 ^ d,
      FiniteFieldConstructor.TrialSearch.firstPassing d =
        some (FiniteFieldConstructor.TrialSearch.monicBits d c) ∧
      ∃ steps ≤ FieldUnaryUnifiedMachine.prepTime d n +
          V38Clock.paddedBudget d n,
        (run K hK steps (initialConfig K d n hK)).l = none ∧
        (run K hK steps (initialConfig K d n hK)).stk (.inr true) =
          V38ZeroPad.padFrom (⟨0, hK⟩ : Fin K)
            (FiniteFieldMachine.UnifiedFieldListMachine.packedBits d c n) ∧
        (run K hK steps (initialConfig K d n hK)).stk (.inl fieldOutput) = [] ∧
        (run K hK steps (initialConfig K d n hK)).stk (.inr false) = [] := by
  obtain ⟨c, hc, hfirst, ts, hts, hhalt, hout⟩ :=
    FieldUnaryUnifiedMachine.physical_firstPassing_packed_from_unary d n hd
  let f := FieldUnaryUnifiedMachine.run ts (FieldUnaryUnifiedMachine.initialConfig d n)
  have hfhalt : f.l = none := hhalt
  have hfcfg : f = ⟨none, f.var, f.stk⟩ := by
    rcases f with ⟨l, v, S⟩
    change l = none at hfhalt
    subst l
    rfl
  let S := initialStack d n
  let T := bank fieldPlace S f.stk
  have hstart : stackCfg fieldPlace S (FieldUnaryUnifiedMachine.initialConfig d n) =
      (⟨some (FieldUnaryUnifiedMachine.Label.prep .scanD),
        FieldUnaryUnifiedMachine.prepEmbed none, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) := by
    have hb : bank fieldPlace S (FieldUnaryUnifiedMachine.initialStack d n) = S := by
      apply bank_eq_self
      intro k
      rfl
    simp only [stackCfg, FieldUnaryUnifiedMachine.initialConfig, hb]
  have hfield : ((advance fieldProgram)^[ts])
      (⟨some (FieldUnaryUnifiedMachine.Label.prep .scanD),
        FieldUnaryUnifiedMachine.prepEmbed none, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, f.var, T⟩ := by
    have hr := BitMachineStackRun.run fieldPlace S FieldUnaryUnifiedMachine.program
      (FieldUnaryUnifiedMachine.initialConfig d n) ts
    rw [hstart] at hr
    rw [← FieldUnaryUnifiedMachine.run_eq_any (inferInstance : DecidableEq FStack)] at hr
    change _ = stackCfg fieldPlace S f at hr
    rw [hfcfg] at hr
    exact hr
  let bits := FiniteFieldMachine.UnifiedFieldListMachine.packedBits d c n
  obtain ⟨tp, htp, hpad⟩ := V38ZeroPad.pad_run (⟨0, hK⟩ : Fin K) bits
  have hpadSource : T (padPlace .source) = bits := by
    change bank fieldPlace S f.stk (fieldPlace fieldOutput) = bits
    rw [bank_at]
    exact hout
  have hpadOther (k : Bool) : T (.inr k) = [] := by
    exact bank_outside fieldPlace S f.stk (.inr k) (by
      rintro ⟨i, hi⟩; cases hi)
  have hpadBank : bank padPlace T
      (V38ZeroPad.cfg (some (.copy (⟨0, hK⟩ : Fin K))) none bits [] []).stk = T := by
    apply bank_eq_self
    intro k
    cases k with
    | source => exact hpadSource.symm
    | work => exact (hpadOther false).symm
    | output => exact (hpadOther true).symm
  have hpadStart : stackCfg padPlace T
      (V38ZeroPad.cfg (some (.copy (⟨0, hK⟩ : Fin K))) none bits [] []) =
      (⟨some (.copy (⟨0, hK⟩ : Fin K)), none, T⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) := by
    change (⟨some (V38ZeroPad.Label.copy (⟨0, hK⟩ : Fin K)), none,
      bank padPlace T
        (V38ZeroPad.cfg (some (.copy (⟨0, hK⟩ : Fin K))) none bits [] []).stk⟩ :
          TM2.Cfg (fun _ : Stack => Bool) (V38ZeroPad.Label K) V38ZeroPad.Control) = _
    rw [hpadBank]
  let U := bank padPlace T
    (V38ZeroPad.cfg (K := K) none none [] []
      (V38ZeroPad.padFrom (⟨0, hK⟩ : Fin K) bits)).stk
  have hpad' : ((advance (padProgram K))^[tp])
      (⟨some (.copy (⟨0, hK⟩ : Fin K)), none, T⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) = ⟨none, none, U⟩ := by
    have hr := BitMachineStackRun.run padPlace T (V38ZeroPad.program K)
      (V38ZeroPad.cfg (some (.copy (⟨0, hK⟩ : Fin K))) none bits [] []) tp
    rw [hpadStart] at hr
    change _ = stackCfg padPlace T
      (V38ZeroPad.run K tp (V38ZeroPad.cfg (some (.copy ⟨0, hK⟩)) none bits [] [])) at hr
    rw [hpad] at hr
    exact hr
  obtain ⟨steps, hsteps, hr⟩ := BitMachineRawSequence.runs fieldProgram (padProgram K)
    (FieldUnaryUnifiedMachine.Label.prep .scanD) (.copy (⟨0, hK⟩ : Fin K))
    (FieldUnaryUnifiedMachine.prepEmbed none) f.var none none S T U ts tp hfield hpad'
  refine ⟨c, hc, hfirst, steps, ?_, ?_, ?_, ?_, ?_⟩
  · have hlen : bits.length = (2 ^ d) ^ 2 * n := by
      exact FiniteFieldConstructor.CanonicalTable.packedFieldBits_length _ _ _
    dsimp [V38Clock.paddedBudget, V38Clock.fieldBudget]
    dsimp [FiniteFieldMachine.FieldListOutputMachine.timeBound] at hts ⊢
    omega
  · exact congrArg (fun q => q.l) hr
  · have hh := congrArg (fun q => q.stk (.inr true)) hr
    change _ = U (.inr true) at hh
    change (run K hK steps (initialConfig K d n hK)).stk (.inr true) = U (.inr true) at hh
    rw [hh]
    change bank padPlace T _ (padPlace .output) = _
    rw [bank_at]
    rfl

  · have hh := congrArg (fun q => q.stk (.inl fieldOutput)) hr
    change (run K hK steps (initialConfig K d n hK)).stk (.inl fieldOutput) =
      U (.inl fieldOutput) at hh
    rw [hh]
    change bank padPlace T _ (padPlace .source) = []
    rw [bank_at]
    rfl
  · have hh := congrArg (fun q => q.stk (.inr false)) hr
    change (run K hK steps (initialConfig K d n hK)).stk (.inr false) =
      U (.inr false) at hh
    rw [hh]
    change bank padPlace T _ (padPlace .work) = []
    rw [bank_at]
    rfl

#print axioms physical_field_pad_bank

end CurrentAdditive.V38FieldPad
