import EthInapproximability.CurrentPaper.SourceCSPGlobalPositiveLiteral

/-!
# Physical positive-cap stage after a literal guarded header

This stage turns the actual canonical n-word and unary m in the global bank
into the checked unary vertex cap. It covers n=0 and n>q*m as failed cap
results; it does not impose a positive-size promise on the raw source.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalCapFromLiteral

open Turing BitMachineEncoding BitMachineStackEmbedding

def capBound (q nword m : Nat) : Nat :=
  1 + (2 + q * (2 * m + 3) + 3 +
    (2 * nword + 2 + (2 * (q * m) + 2) + 1 +
      (q * m + 1) * (4 * nword + 5) + 3) + 1)

theorem capBound_uniform (q nword m L : Nat)
    (hnword : nword ≤ L) (hm : m ≤ L) :
    capBound q nword m ≤ capBound q L L := by
  dsimp only [capBound]
  gcongr

theorem cap_from_literal (a q n m : Nat)
    (v : SourceCSPGuardOutputCombined.Control)
    (S₀ : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hv : v.1.2.2 = some .positive)
    (hnword : S₀ (SourceCSPGlobalDecisionProgram.inputEmbedding
      SourceCSPGuardDispatch.vertexSlot) = n.bits)
    (hm : S₀ (SourceCSPGlobalDecisionProgram.inputEmbedding
      SourceCSPGuardDispatch.countSlot) = List.replicate m true)
    (hempty : ∀ k : Fin 7,
      S₀ (SourceCSPGlobalDecisionProgram.capEmbedding (.inr k)) = []) :
    ∃ (t : Nat) (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
      (c : Unit × SourceCSPPositiveCapEntry.CapControl),
      t ≤ capBound q n.bits.length m ∧
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
        (⟨some .afterPrefix, .prefix v, S₀⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (SourceCSPGlobalDecisionProgram.Control a q)) =
        ⟨some .capCheck, .cap c, S⟩ ∧
      (S SourceCSPHeaderRowBridge.capSource).head? =
        some (decide (0 < n ∧ n ≤ q * m)) := by
  let before : SourceCSPBudgetFrame.Stack → List Bool :=
    fun k => S₀ (SourceCSPGlobalDecisionProgram.capEmbedding k)
  have hm' : before (.inl (.inr 6)) = List.replicate m true := hm
  have hnword' : before (.inl (.inl (.inl (.inl 0)))) = n.bits := hnword
  have hstatus : before (.inr 0) = [] := hempty 0
  have htarget : before (.inr 1) = [] := hempty 1
  have hwork : before (.inr 2) = [] := hempty 2
  have hunused : ∀ k : Fin 7, 3 ≤ k.val → before (.inr k) = [] := by
    intro k _
    exact hempty k
  obtain ⟨tc, vc, Tc, htc, hrc, hcap, _, _⟩ :=
    SourceCSPPositiveCapEntry.positive_total n m q before
      hm' hnword' hstatus htarget hwork hunused
  have hstart := SourceCSPGlobalDecisionProgram.after_prefix_positive
    a q v S₀ hv
  obtain ⟨uc, Sc, huc, hucRun, hrestrict⟩ :=
    SourceCSPGlobalDecisionProgram.cap_lift a q S₀ tc
      ((), ((none, none), vc)) Tc (by simpa only [before] using hrc)
  refine ⟨uc + 1, Sc, ((), ((none, none), vc)), ?_, ?_, ?_⟩
  · dsimp only [capBound]
    omega
  · change ((advance (SourceCSPGlobalDecisionProgram.program a q))^[uc + 1]) _ = _
    rw [Function.iterate_succ_apply, hstart]
    exact hucRun
  · simpa only [SourceCSPGlobalDecisionProgram.capEmbedding,
      SourceCSPHeaderRowBridge.capSource] using
        (congrArg List.head? (hrestrict.1 (.inr 6))).trans hcap

/-- In the good-size branch the cap and the literal unread source suffix are
both retained, so row preparation is fed by the physical parser bank. -/
theorem cap_from_literal_success (a q n m : Nat)
    (v : SourceCSPGuardOutputCombined.Control)
    (S₀ : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hn : 0 < n) (hsize : n ≤ q * m)
    (hv : v.1.2.2 = some .positive)
    (hnword : S₀ (SourceCSPGlobalDecisionProgram.inputEmbedding
      SourceCSPGuardDispatch.vertexSlot) = n.bits)
    (hm : S₀ (SourceCSPGlobalDecisionProgram.inputEmbedding
      SourceCSPGuardDispatch.countSlot) = List.replicate m true)
    (hempty : ∀ k : Fin 7,
      S₀ (SourceCSPGlobalDecisionProgram.capEmbedding (.inr k)) = [])
    (hrowblank : ∀ k : SourceCSPRowQueryFrame.Stack q ⊕ Fin 5,
      S₀ (.inr k) = []) :
    ∃ (t : Nat) (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
      (c : Unit × SourceCSPPositiveCapEntry.CapControl),
      t ≤ capBound q n.bits.length m ∧
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
        (⟨some .afterPrefix, .prefix v, S₀⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (SourceCSPGlobalDecisionProgram.Control a q)) =
        ⟨some .capCheck, .cap c, S⟩ ∧
      S SourceCSPHeaderRowBridge.capSource =
        true :: List.replicate (n - 1) true ∧
      S SourceCSPHeaderRowBridge.count = List.replicate m true ∧
      S SourceCSPHeaderRowBridge.source =
        S₀ SourceCSPHeaderRowBridge.source ∧
      (∀ k : SourceCSPRowQueryFrame.Stack q ⊕ Fin 5,
        S (.inr k) = []) := by
  let before : SourceCSPBudgetFrame.Stack → List Bool :=
    fun k => S₀ (SourceCSPGlobalDecisionProgram.capEmbedding k)
  have hm' : before (.inl (.inr 6)) = List.replicate m true := hm
  have hnword' : before (.inl (.inl (.inl (.inl 0)))) = n.bits := hnword
  have hstatus : before (.inr 0) = [] := hempty 0
  have htarget : before (.inr 1) = [] := hempty 1
  have hwork : before (.inr 2) = [] := hempty 2
  have hunused : ∀ k : Fin 7, 3 ≤ k.val → before (.inr k) = [] := by
    intro k _
    exact hempty k
  obtain ⟨tc, vc, Tc, htc, hrc, hcap, hcount, hsource⟩ :=
    SourceCSPPositiveCapEntry.positive_success_row n m q before
      hn hsize hm' hnword' hstatus htarget hwork hunused
  have hstart := SourceCSPGlobalDecisionProgram.after_prefix_positive
    a q v S₀ hv
  obtain ⟨uc, Sc, huc, hucRun, hrestrict⟩ :=
    SourceCSPGlobalDecisionProgram.cap_lift a q S₀ tc
      ((), ((none, none), vc)) Tc (by simpa only [before] using hrc)
  refine ⟨uc + 1, Sc, ((), ((none, none), vc)), ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [capBound]
    omega
  · change ((advance (SourceCSPGlobalDecisionProgram.program a q))^[uc + 1]) _ = _
    rw [Function.iterate_succ_apply, hstart]
    exact hucRun
  · exact (hrestrict.1 (.inr 6)).trans hcap
  · exact (hrestrict.1 (.inl (.inr 6))).trans hcount
  · exact (hrestrict.1 SourceCSPPositiveSuffix.rowSlot).trans hsource
  · intro k
    have houtside : ¬ ∃ j : SourceCSPBudgetFrame.Stack,
        SourceCSPGlobalDecisionProgram.capEmbedding (q := q) j =
          (.inr k : SourceCSPGlobalDecisionProgram.Stack q) := by
      rintro ⟨j, h⟩
      cases h
    exact (hrestrict.2 (.inr k) houtside).trans (hrowblank k)

/-- On an arbitrary raw input whose actual guarded classifier chooses the
positive tag, the global table physically reaches the cap check with its
literal status bit. This does not assume the cap succeeds. -/
theorem raw_positive_cap (a q : Nat) (input : List Bool) :
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
        ∃ (n m t : Nat) (rest : List Bool)
          (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
          (c : Unit × SourceCSPPositiveCapEntry.CapControl),
          input = SourceCSPHeaderParse.header n m a q ++ rest ∧
          m ≤ input.length ∧
          t ≤ SourceCSPGuardDispatchSequence.bound a q input.length + 2 +
            capBound q input.length input.length ∧
          ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
            (SourceCSPGlobalDecisionProgram.initial a q input) =
              (⟨some .capCheck, .cap c, S⟩ :
                TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
                  (SourceCSPGlobalDecisionProgram.Label a q)
                  (SourceCSPGlobalDecisionProgram.Control a q)) ∧
          (S SourceCSPHeaderRowBridge.capSource).head? =
            some (decide (0 < n ∧ n ≤ q * m))) := by
  obtain ⟨tp, v, Sp, htp, hrp, hpositive⟩ :=
    SourceCSPGlobalPositiveLiteral.positive_literal a q input
  refine ⟨tp, v, Sp, htp, hrp, ?_⟩
  intro hv
  obtain ⟨n, m, tg, rest, S₀, htg, hglobal, hinput,
    hnword, _, _, hm, hmL, hempty, _⟩ := hpositive hv
  obtain ⟨tc, S, c, htc, hcapRun, hcap⟩ :=
    cap_from_literal a q n m (v, none) S₀ hv hnword hm hempty
  have hnL := (SourceCSPGlobalPositiveLiteral.canonical_header_word_bounds
    a q n m input rest hinput).1
  have huniform := capBound_uniform q n.bits.length m
    input.length hnL hmL
  refine ⟨n, m, tg + tc, rest, S, c, hinput, hmL,
    by omega, ?_, hcap⟩
  change ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg + tc]) _ = _
  rw [show tg + tc = tc + tg by omega, Function.iterate_add_apply,
    hglobal]
  exact hcapRun

end EthInapproximability.CurrentPaper.SourceCSPGlobalCapFromLiteral
