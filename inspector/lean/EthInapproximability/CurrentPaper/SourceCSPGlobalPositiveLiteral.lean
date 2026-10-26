import EthInapproximability.CurrentPaper.SourceCSPGlobalDecisionProgram
import EthInapproximability.CurrentPaper.SourceCSPHeaderBankTransport

/-!
# Raw positive-header witness in the global bank

The actual all-input guarded prefix chooses a finite-control tag. If that tag
is positive, the literal global postprefix bank contains a canonical header,
bounded unary row count, and exact unread source suffix. The statement makes
no positivity assumption about the decoded vertex count.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalPositiveLiteral

open Turing BitMachineEncoding BitMachineStackEmbedding

theorem canonical_header_word_bounds (a q n m : Nat)
    (input rest : List Bool)
    (hinput : input = SourceCSPHeaderParse.header n m a q ++ rest) :
    n.bits.length ≤ input.length ∧
    m.bits.length ≤ input.length ∧
    rest.length ≤ input.length := by
  have hlen : input.length =
      (2 * n.bits.length + 1) + (2 * m.bits.length + 1) +
        (2 * a.bits.length + 1) + (2 * q.bits.length + 1) +
        rest.length := by
    simp only [hinput, SourceCSPHeaderParse.header,
      List.length_append, EncodedCommunication.natField,
      EncodedCommunication.field_length]
  omega

theorem positive_literal (a q : Nat) (input : List Bool) :
    ∃ (tp : Nat) (v : SourceCSPGuardOutputCombined.PrefixControl)
      (Sp : SourceCSPInputFrame.Stack → List Bool),
      tp ≤ SourceCSPGuardDispatchSequence.bound a q input.length ∧
      ((advance (SourceCSPGuardOutputCombined.program a q))^[tp])
        (SourceCSPGuardOutputCombined.initial a q input) =
          (⟨some .route, (v, none), Sp⟩ :
            TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
              (SourceCSPGuardOutputCombined.Label a q)
              SourceCSPGuardOutputCombined.Control) ∧
      (v.2.2 = some .positive →
        ∃ (n m tg : Nat) (rest : List Bool)
          (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool),
          tg ≤ SourceCSPGuardDispatchSequence.bound a q input.length + 2 ∧
          ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
            (SourceCSPGlobalDecisionProgram.initial a q input) =
              (⟨some .afterPrefix, .prefix (v, none), S⟩ :
                TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
                  (SourceCSPGlobalDecisionProgram.Label a q)
                  (SourceCSPGlobalDecisionProgram.Control a q)) ∧
          input = SourceCSPHeaderParse.header n m a q ++ rest ∧
          S (SourceCSPGlobalDecisionProgram.inputEmbedding
            SourceCSPGuardDispatch.vertexSlot) = n.bits ∧
          S (SourceCSPGlobalDecisionProgram.inputEmbedding
            (.inl (.inl (.inl 1)))) = m.bits ∧
          S (SourceCSPGlobalDecisionProgram.inputEmbedding
            SourceCSPGuardDispatch.sourceSlot) = rest ∧
          S (SourceCSPGlobalDecisionProgram.inputEmbedding
            SourceCSPGuardDispatch.countSlot) = List.replicate m true ∧
          m ≤ input.length ∧
          (∀ k : Fin 7,
            S (SourceCSPGlobalDecisionProgram.capEmbedding (.inr k)) = []) ∧
          (∀ k : SourceCSPRowQueryFrame.Stack q ⊕ Fin 5,
            S (.inr k) = [])) := by
  obtain ⟨tp, v, Sp, htp, hrp, hpos⟩ :=
    SourceCSPHeaderBankTransport.combined_positive_prefix a q input
  refine ⟨tp, v, Sp, htp, hrp, ?_⟩
  intro hv
  obtain ⟨n, m, rest, hinput, hn, hm, hrest, hcount, hmL⟩ := hpos hv
  let localCfg := SourceCSPGuardOutputCombined.initial a q input
  have hcompleted : ((advance
      (SourceCSPGuardOutputCombined.program a q))^[tp + 2]) localCfg =
      ⟨none, (v, none), Sp⟩ := by
    rw [show tp + 2 = 2 + tp by omega, Function.iterate_add_apply]
    simpa only [localCfg, hrp,
      SourceCSPGuardOutputCombined.routeRun] using
      SourceCSPGuardOutputCombined.route_positive a q v Sp hv
  have hhalt : (((advance
      (SourceCSPGuardOutputCombined.program a q))^[tp + 2])
      localCfg).l = none := by rw [hcompleted]
  let before := SourceCSPHeaderRowBridge.initial (q := q) input
  let read : SourceCSPGlobalDecisionProgram.Control a q →
      SourceCSPGuardOutputCombined.Control :=
    fun x => match x with
      | .prefix w => w
      | _ => SourceCSPGuardOutputCombined.initialControl
  have hleft : Function.LeftInverse read
      SourceCSPGlobalDecisionProgram.Control.prefix := by
    intro w
    rfl
  obtain ⟨tg, htg, hglobal⟩ := outputs
    (SourceCSPGlobalDecisionProgram.inputEmbedding (q := q)) before
    SourceCSPGlobalDecisionProgram.Label.prefix
    SourceCSPGlobalDecisionProgram.Control.prefix
    read hleft (some .afterPrefix)
    (SourceCSPGuardOutputCombined.program a q)
    (SourceCSPGlobalDecisionProgram.program a q)
    (fun _ => rfl) localCfg (tp + 2) hhalt
  rw [hcompleted] at hglobal
  have hstart : BitMachineStackEmbedding.cfg
      (SourceCSPGlobalDecisionProgram.inputEmbedding (q := q)) before
      SourceCSPGlobalDecisionProgram.Label.prefix
      SourceCSPGlobalDecisionProgram.Control.prefix
      (some .afterPrefix) localCfg =
      SourceCSPGlobalDecisionProgram.initial a q input := by
    simp only [BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, localCfg,
      SourceCSPGlobalDecisionProgram.initial,
      SourceCSPGuardOutputCombined.initial, before]
    congr 1
    apply bank_eq_self
    intro k
    rfl
  rw [hstart] at hglobal
  let S := bank (SourceCSPGlobalDecisionProgram.inputEmbedding (q := q))
    before Sp
  refine ⟨n, m, tg, rest, S, htg.trans (by omega), ?_, hinput,
    ?_, ?_, ?_, ?_, hmL, ?_, ?_⟩
  · simpa only [S, BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, id_eq, Option.map_none] using hglobal
  · simpa only [S, bank_at] using hn
  · simpa only [S, bank_at] using hm
  · simpa only [S, bank_at] using hrest
  · simpa only [S, bank_at] using hcount
  · intro k
    have houtside : ¬ ∃ j : SourceCSPInputFrame.Stack,
        SourceCSPGlobalDecisionProgram.inputEmbedding (q := q) j =
          SourceCSPGlobalDecisionProgram.capEmbedding (q := q) (.inr k) := by
      rintro ⟨j, h⟩
      cases h
    rw [show S = bank
      (SourceCSPGlobalDecisionProgram.inputEmbedding (q := q)) before Sp
        from rfl]
    rw [bank_outside _ _ _ _ houtside]
    rfl
  · intro k
    have houtside : ¬ ∃ j : SourceCSPInputFrame.Stack,
        SourceCSPGlobalDecisionProgram.inputEmbedding (q := q) j =
          (.inr k : SourceCSPGlobalDecisionProgram.Stack q) := by
      rintro ⟨j, h⟩
      cases h
    rw [show S = bank
      (SourceCSPGlobalDecisionProgram.inputEmbedding (q := q)) before Sp
        from rfl]
    rw [bank_outside _ _ _ _ houtside]
    rfl

end EthInapproximability.CurrentPaper.SourceCSPGlobalPositiveLiteral
