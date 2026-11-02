import EthInapproximability.CurrentPaper.SourceCSPGlobalCapFailure
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-!
# Literal guarded reject/zero runs in the global CSP controller

This file lifts the already-checked local guarded writers through the same
global instruction table. It does not implement new writer instructions.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalDecisionProgram

open Turing BitMachineEncoding BitMachineStackEmbedding

/-- A complete local guarded prefix run with nonpositive outcome embeds into
the global controller, then its administrative `.afterPrefix` label halts. -/
theorem lift_nonpositive_terminal (a q : Nat) (input : List Bool)
    (t : Nat) (c : SourceCSPGuardOutputCombined.Control)
    (T : SourceCSPInputFrame.Stack → List Bool)
    (hr : ((advance (SourceCSPGuardOutputCombined.program a q))^[t])
      (SourceCSPGuardOutputCombined.initial a q input) =
      (⟨none, c, T⟩ :
        TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
          (SourceCSPGuardOutputCombined.Label a q)
          SourceCSPGuardOutputCombined.Control))
    (hnot : c.1.2.2 ≠ some .positive) :
    ∃ (u : Nat) (S : Stack q → List Bool),
      u ≤ t + 1 ∧
      ((advance (program a q))^[u]) (initial a q input) =
        (⟨none, .prefix c, S⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) ∧
      (∀ k : SourceCSPInputFrame.Stack, S (inputEmbedding k) = T k) := by
  let localCfg := SourceCSPGuardOutputCombined.initial a q input
  have hhalt : (((advance
      (SourceCSPGuardOutputCombined.program a q))^[t]) localCfg).l = none := by
    simpa only [localCfg] using congrArg (fun x => x.l) hr
  let before := SourceCSPHeaderRowBridge.initial (q := q) input
  let read : Control a q → SourceCSPGuardOutputCombined.Control :=
    fun x => match x with
      | .prefix v => v
      | _ => SourceCSPGuardOutputCombined.initialControl
  have hleft : Function.LeftInverse read Control.prefix := by
    intro v
    rfl
  obtain ⟨v, hv, hrun⟩ := outputs
    (inputEmbedding (q := q)) before Label.prefix Control.prefix
    read hleft (some .afterPrefix)
    (SourceCSPGuardOutputCombined.program a q) (program a q)
    (fun _ => rfl) localCfg t hhalt
  have hstart : cfg (inputEmbedding (q := q)) before Label.prefix
      Control.prefix (some .afterPrefix) localCfg = initial a q input := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, initial,
      SourceCSPGuardOutputCombined.initial, before]
    congr 1
    apply bank_eq_self
    intro k
    rfl
  rw [hr, hstart] at hrun
  let S := bank (inputEmbedding (q := q)) before T
  have hprefix : ((advance (program a q))^[v]) (initial a q input) =
      (⟨some .afterPrefix, .prefix c, S⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) := by
    simpa only [S, cfg, stackCfg, BitMachineInline.cfg,
      Option.map_none] using hrun
  refine ⟨v + 1, S, by omega, ?_, ?_⟩
  · rw [show v + 1 = 1 + v by omega,
      Function.iterate_add_apply, hprefix]
    simp only [Function.iterate_one]
    exact after_prefix_nonpositive a q c S hnot
  · intro k
    exact bank_at (inputEmbedding (q := q)) before T k

end EthInapproximability.CurrentPaper.SourceCSPGlobalDecisionProgram

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalDecisionProgram

open Turing BitMachineEncoding

theorem classify_zero_conditions (good : Bool)
    (vertex count source : List Bool)
    (h : SourceCSPGuardDispatch.classify good vertex count source = .zero) :
    good = true ∧ vertex = [] ∧ count = [] ∧ source = [] := by
  cases good <;> cases vertex <;> cases count <;> cases source <;>
    simp [SourceCSPGuardDispatch.classify] at h ⊢

private theorem local_terminal_bound (a q : Nat) (input : List Bool)
    (tp tr : Nat) (v : SourceCSPGuardOutputCombined.PrefixControl)
    (Sp : SourceCSPInputFrame.Stack → List Bool)
    (htp : tp ≤ SourceCSPGuardDispatchSequence.bound a q input.length)
    (hrp : ((advance (SourceCSPGuardOutputCombined.program a q))^[tp])
      (SourceCSPGuardOutputCombined.initial a q input) =
        (⟨some .route, (v, none), Sp⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (SourceCSPGuardOutputCombined.Label a q)
            SourceCSPGuardOutputCombined.Control))
    (htr : tr ≤ (Sp SourceCSPRejectWriterFrame.outputSlot).length + 4) :
    tp + tr ≤ SourceCSPGuardOutputCombined.polyBound a q input.length := by
  have hgrowth := BitMachineStackGrowth.run_growth
    (SourceCSPGuardOutputCombined.program a q)
    (SourceCSPGuardOutputCombined.initial a q input) tp
    SourceCSPRejectWriterFrame.outputSlot
  rw [hrp] at hgrowth
  have hblank : (SourceCSPGuardOutputCombined.initial a q input).stk
      SourceCSPRejectWriterFrame.outputSlot = [] := rfl
  rw [hblank] at hgrowth
  simp only [List.length_nil, Nat.zero_add] at hgrowth
  unfold SourceCSPGuardOutputCombined.polyBound
  have hmul := Nat.mul_le_mul_left
    (1 + BitMachineStackGrowth.perStep
      (SourceCSPGuardOutputCombined.program a q)) htp
  simp only [add_mul, one_mul] at hmul ⊢
  omega

/-- Every raw input first reaches the actual guarded route tag. If the
classifier chooses reject or zero, the corresponding already-checked writer
runs inside the same global program and then halts at `.afterPrefix`.
In particular, the zero case is guarded by the classifier's checked header,
arity, empty unary count and empty unread suffix conditions. -/
theorem raw_guarded_terminal (a q : Nat) (input : List Bool) :
    ∃ (tp : Nat) (v : SourceCSPGuardOutputCombined.PrefixControl)
      (Sp S₀ : SourceCSPInputFrame.Stack → List Bool)
      (wa wq word : List Bool),
      tp ≤ SourceCSPGuardDispatchSequence.bound a q input.length ∧
      ((advance (SourceCSPGuardOutputCombined.program a q))^[tp])
        (SourceCSPGuardOutputCombined.initial a q input) =
          (⟨some .route, (v, none), Sp⟩ :
            TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
              (SourceCSPGuardOutputCombined.Label a q)
              SourceCSPGuardOutputCombined.Control) ∧
      v.2.2 = some (SourceCSPGuardDispatch.classify
        ((SourceCSPHeaderValidFlag.parserGood input &&
          decide (wq = q.bits) && decide (wa = a.bits)) &&
          decide (EncodedCommunication.bitsValue word ≤ input.length))
        (S₀ SourceCSPGuardDispatch.vertexSlot)
        (S₀ SourceCSPGuardDispatch.countSlot)
        (S₀ SourceCSPGuardDispatch.sourceSlot)) ∧
      (v.2.2 = some .zero →
        ((SourceCSPHeaderValidFlag.parserGood input &&
          decide (wq = q.bits) && decide (wa = a.bits)) &&
          decide (EncodedCommunication.bitsValue word ≤ input.length)) = true ∧
        S₀ SourceCSPGuardDispatch.vertexSlot = [] ∧
        S₀ SourceCSPGuardDispatch.countSlot = [] ∧
        S₀ SourceCSPGuardDispatch.sourceSlot = []) ∧
      (v.2.2 = some .reject →
        ∃ (t : Nat) (S : Stack q → List Bool),
          t ≤ SourceCSPGuardOutputCombined.polyBound a q input.length + 1 ∧
          ((advance (program a q))^[t]) (initial a q input) =
            (⟨none, .prefix (SourceCSPGuardOutputCombined.rejectControl, none), S⟩ :
              TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) ∧
          S outputSlot = SourceCSPRejectFormula.bits ∧
          S outputSlot ∉ EncodedCNF.Language) ∧
      (v.2.2 = some .zero →
        ∃ (t : Nat) (S : Stack q → List Bool),
          t ≤ SourceCSPGuardOutputCombined.polyBound a q input.length + 1 ∧
          ((advance (program a q))^[t]) (initial a q input) =
            (⟨none, .prefix (SourceCSPGuardOutputCombined.zeroControl, none), S⟩ :
              TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) ∧
          S outputSlot = [false, false]) := by
  obtain ⟨tp, v, Sp, S₀, wa, wq, word, htp, hrp, htag⟩ :=
    SourceCSPGuardOutputCombined.all_input_prefix a q input
  refine ⟨tp, v, Sp, S₀, wa, wq, word, htp, hrp, htag, ?_, ?_, ?_⟩
  · intro hv
    have hc : SourceCSPGuardDispatch.classify
        ((SourceCSPHeaderValidFlag.parserGood input &&
          decide (wq = q.bits) && decide (wa = a.bits)) &&
          decide (EncodedCommunication.bitsValue word ≤ input.length))
        (S₀ SourceCSPGuardDispatch.vertexSlot)
        (S₀ SourceCSPGuardDispatch.countSlot)
        (S₀ SourceCSPGuardDispatch.sourceSlot) = .zero := by
      apply Option.some.inj
      calc
        some (SourceCSPGuardDispatch.classify
          ((SourceCSPHeaderValidFlag.parserGood input &&
            decide (wq = q.bits) && decide (wa = a.bits)) &&
            decide (EncodedCommunication.bitsValue word ≤ input.length))
          (S₀ SourceCSPGuardDispatch.vertexSlot)
          (S₀ SourceCSPGuardDispatch.countSlot)
          (S₀ SourceCSPGuardDispatch.sourceSlot)) = v.2.2 := htag.symm
        _ = some .zero := hv
    exact classify_zero_conditions _ _ _ _ hc
  · intro hv
    obtain ⟨tr, T, htr, hroute, hout, _⟩ :=
      SourceCSPGuardOutputCombined.route_reject a q v Sp hv
    have hlocal : ((advance
        (SourceCSPGuardOutputCombined.program a q))^[tp + tr])
        (SourceCSPGuardOutputCombined.initial a q input) =
        (⟨none, (SourceCSPGuardOutputCombined.rejectControl, none), T⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (SourceCSPGuardOutputCombined.Label a q)
            SourceCSPGuardOutputCombined.Control) := by
      rw [show tp + tr = tr + tp by omega,
        Function.iterate_add_apply, hrp]
      exact hroute
    have hnot :
        ((SourceCSPGuardOutputCombined.rejectControl, none) :
          SourceCSPGuardOutputCombined.Control).1.2.2 ≠
        some SourceCSPGuardDispatch.Outcome.positive := by decide
    obtain ⟨u, S, hu, hglobal, hbank⟩ :=
      lift_nonpositive_terminal a q input (tp + tr)
        (SourceCSPGuardOutputCombined.rejectControl, none) T
        hlocal hnot
    have hb := local_terminal_bound a q input tp tr v Sp htp hrp htr
    refine ⟨u, S, by omega, hglobal, ?_, ?_⟩
    · exact (hbank SourceCSPRejectWriterFrame.outputSlot).trans hout
    · change S (inputEmbedding SourceCSPRejectWriterFrame.outputSlot) ∉
        EncodedCNF.Language
      rw [(hbank SourceCSPRejectWriterFrame.outputSlot).trans hout]
      exact SourceCSPRejectFormula.bits_not_language
  · intro hv
    obtain ⟨tr, T, htr, hroute, hout, _⟩ :=
      SourceCSPGuardOutputCombined.route_zero a q v Sp hv
    have hlocal : ((advance
        (SourceCSPGuardOutputCombined.program a q))^[tp + tr])
        (SourceCSPGuardOutputCombined.initial a q input) =
        (⟨none, (SourceCSPGuardOutputCombined.zeroControl, none), T⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (SourceCSPGuardOutputCombined.Label a q)
            SourceCSPGuardOutputCombined.Control) := by
      rw [show tp + tr = tr + tp by omega,
        Function.iterate_add_apply, hrp]
      exact hroute
    have hnot :
        ((SourceCSPGuardOutputCombined.zeroControl, none) :
          SourceCSPGuardOutputCombined.Control).1.2.2 ≠
        some SourceCSPGuardDispatch.Outcome.positive := by decide
    obtain ⟨u, S, hu, hglobal, hbank⟩ :=
      lift_nonpositive_terminal a q input (tp + tr)
        (SourceCSPGuardOutputCombined.zeroControl, none) T
        hlocal hnot
    have hb := local_terminal_bound a q input tp tr v Sp htp hrp htr
    exact ⟨u, S, by omega, hglobal,
      (hbank SourceCSPRejectWriterFrame.outputSlot).trans hout⟩

end EthInapproximability.CurrentPaper.SourceCSPGlobalDecisionProgram
