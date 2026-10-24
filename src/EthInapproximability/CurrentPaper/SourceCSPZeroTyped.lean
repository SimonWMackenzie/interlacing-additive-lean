import EthInapproximability.CurrentPaper.SourceCSPGlobalPrefixTerminal
import EthInapproximability.CurrentPaper.SourceCSPHeaderBankTransport
import EthInapproximability.CurrentPaper.SourceCSPRowCodecConverse
import EthInapproximability.CurrentPaper.SourceCSPGuardedCodec

/-!
# The typed zero-vertex input takes the actual zero arm

This is a boundary lemma for fixed positive query arity. It does not extend
the source promise to malformed inputs. The all-input guard remains responsible
for rejecting those inputs.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPZeroTyped

open Turing BitMachineEncoding EncodedCommunication EncodedETHSource

theorem zero_raw_header {a q : Nat} (hq : 0 < q)
    (P : ConstraintInstance a q) (hn : P.vertices = 0) :
    constraintBits P = SourceCSPHeaderParse.header 0 0 a q := by
  have hm := SourceCSPGuardedCodec.zero_vertices_no_constraints hq P hn
  cases P with
  | mk n m system =>
      dsimp at hn hm
      subst n
      subst m
      simpa only [SourceCSPGuardedCodec.input_eq_header_rows,
        SourceCSPCodec.fnFields_zero, List.append_nil]

theorem zero_header_parse (a q : Nat) :
    SourceCSPRowController.readQueriesFrom (q := 4) 0
      (SourceCSPHeaderParse.header 0 0 a q) (fun _ => []) =
      some ((fun j : Fin 4 => (SourceCSPHeaderParse.numbers 0 0 a q j).bits), []) := by
  simpa only [SourceCSPHeaderParse.queries_eq_header, List.append_nil] using
    SourceCSPRowCodecConverse.parse_canonical_zero
      (SourceCSPHeaderParse.numbers 0 0 a q) []

theorem zero_guard_route (a q : Nat) :
    ∃ (t : Nat) (S : SourceCSPInputFrame.Stack → List Bool)
      (v : SourceCSPGuardDispatch.Control),
      t ≤ SourceCSPGuardDispatchSequence.bound a q
        (SourceCSPHeaderParse.header 0 0 a q).length ∧
      ((advance (SourceCSPGuardDispatchSequence.program a q))^[t])
        (⟨some (.inl (SourceCSPGuardDispatchSequence.headerStart a q)),
          (SourceCSPGuardDispatchSequence.headerInitial,
            SourceCSPGuardDispatch.initialControl),
          SourceCSPInputFrame.initial (SourceCSPHeaderParse.header 0 0 a q)⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (BitMachineRawSequence.Label
              (SourceCSPGuardDispatchSequence.HeaderLabel a q)
              SourceCSPGuardDispatch.Label)
            (SourceCSPGuardDispatchSequence.HeaderControl ×
              SourceCSPGuardDispatch.Control)) =
        ⟨none, (SourceCSPGuardDispatchSequence.headerInitial, v), S⟩ ∧
      v.2 = some .zero := by
  let bank : SourceCSPRowController.Bank 4 :=
    fun j => (SourceCSPHeaderParse.numbers 0 0 a q j).bits
  have hp : SourceCSPRowController.readQueriesFrom (q := 4) 0
      (SourceCSPHeaderParse.header 0 0 a q) (fun _ => []) =
      some (bank, []) := zero_header_parse a q
  obtain ⟨t, S, v, ht, hr, _, _, _, _, hv⟩ :=
    SourceCSPHeaderBankTransport.dispatch_success_bank a q
      (SourceCSPHeaderParse.header 0 0 a q) bank [] hp
  refine ⟨t, S, v, ht, hr, ?_⟩
  simpa [bank, SourceCSPHeaderParse.numbers,
    SourceCSPGuardDispatch.classify,
    EncodedCommunication.bitsValue_bits] using hv

theorem zero_combined_route (a q : Nat) :
    ∃ (t : Nat) (S : SourceCSPInputFrame.Stack → List Bool)
      (v : SourceCSPGuardOutputCombined.PrefixControl),
      t ≤ SourceCSPGuardDispatchSequence.bound a q
        (SourceCSPHeaderParse.header 0 0 a q).length ∧
      ((advance (SourceCSPGuardOutputCombined.program a q))^[t])
        (SourceCSPGuardOutputCombined.initial a q
          (SourceCSPHeaderParse.header 0 0 a q)) =
        (⟨some .route, (v, none), S⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
            (SourceCSPGuardOutputCombined.Label a q)
            SourceCSPGuardOutputCombined.Control) ∧
      v.2.2 = some .zero := by
  obtain ⟨tp, Sp, vp, htp, hrp, hvp⟩ := zero_guard_route a q
  let localCfg : TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
      (SourceCSPGuardOutputCombined.PrefixLabel a q)
      SourceCSPGuardOutputCombined.PrefixControl :=
    ⟨some (.inl (SourceCSPGuardDispatchSequence.headerStart a q)),
      (SourceCSPGuardDispatchSequence.headerInitial,
        SourceCSPGuardDispatch.initialControl),
      SourceCSPInputFrame.initial (SourceCSPHeaderParse.header 0 0 a q)⟩
  have hhalt : (((advance (SourceCSPGuardDispatchSequence.program a q))^[tp])
      localCfg).l = none := by
    simpa only [localCfg] using congrArg (fun c => c.l) hrp
  obtain ⟨t, ht, hr⟩ := BitMachineInline.outputs
    SourceCSPGuardOutputCombined.Label.prefix
    (fun v => (v, none)) Prod.fst (fun _ => rfl) (some .route)
    (SourceCSPGuardDispatchSequence.program a q)
    (SourceCSPGuardOutputCombined.program a q)
    (fun _ => rfl) localCfg tp hhalt
  rw [hrp] at hr
  refine ⟨t, Sp, (SourceCSPGuardDispatchSequence.headerInitial, vp),
    ht.trans htp, ?_, ?_⟩
  · simpa only [SourceCSPGuardOutputCombined.initial,
      SourceCSPGuardOutputCombined.initialControl, localCfg,
      BitMachineInline.cfg, Option.map_none] using hr
  · exact hvp

theorem zero_global_header (a q : Nat) :
    ∃ (t : Nat) (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool),
      t ≤ SourceCSPGuardOutputCombined.polyBound a q
        (SourceCSPHeaderParse.header 0 0 a q).length + 1 ∧
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
        (SourceCSPGlobalDecisionProgram.initial a q
          (SourceCSPHeaderParse.header 0 0 a q)) =
        (⟨none,
          .prefix (SourceCSPGuardOutputCombined.zeroControl, none), S⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (SourceCSPGlobalDecisionProgram.Control a q)) ∧
      S SourceCSPGlobalDecisionProgram.outputSlot = [false, false] := by
  let input := SourceCSPHeaderParse.header 0 0 a q
  obtain ⟨tp, Sp, v, htp, hrp, hv⟩ := zero_combined_route a q
  obtain ⟨tr, T, htr, hroute, hout, _⟩ :=
    SourceCSPGuardOutputCombined.route_zero a q v Sp hv
  change tr ≤ (Sp SourceCSPRejectWriterFrame.outputSlot).length + 4 at htr
  have hlocal : ((advance (SourceCSPGuardOutputCombined.program a q))^[tp + tr])
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
    SourceCSPGlobalDecisionProgram.lift_nonpositive_terminal
      a q input (tp + tr)
      (SourceCSPGuardOutputCombined.zeroControl, none) T hlocal hnot
  have hgrowth := BitMachineStackGrowth.run_growth
    (SourceCSPGuardOutputCombined.program a q)
    (SourceCSPGuardOutputCombined.initial a q input) tp
    SourceCSPRejectWriterFrame.outputSlot
  rw [hrp] at hgrowth
  have hblank : (SourceCSPGuardOutputCombined.initial a q input).stk
      SourceCSPRejectWriterFrame.outputSlot = [] := rfl
  rw [hblank] at hgrowth
  simp only [List.length_nil, Nat.zero_add] at hgrowth
  have hmul := Nat.mul_le_mul_left
    (1 + BitMachineStackGrowth.perStep
      (SourceCSPGuardOutputCombined.program a q)) htp
  simp only [add_mul, one_mul] at hmul
  refine ⟨u, S, ?_, hglobal, ?_⟩
  · unfold SourceCSPGuardOutputCombined.polyBound
    simp only [add_mul, one_mul]
    omega
  · exact (hbank SourceCSPRejectWriterFrame.outputSlot).trans hout

/-- A genuine encoded positive-arity zero-vertex CSP takes the checked EOF
zero arm of the *same* global raw-input controller, and emits the literal
encoding of its three-CNF translation. -/
theorem typed_zero_global {a q : Nat} (hq : 0 < q)
    (P : ConstraintInstance a q) (hn : P.vertices = 0) :
    ∃ (t : Nat) (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool),
      t ≤ SourceCSPGuardOutputCombined.polyBound a q
        (constraintBits P).length + 1 ∧
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
        (SourceCSPGlobalDecisionProgram.initial a q (constraintBits P)) =
        (⟨none,
          .prefix (SourceCSPGuardOutputCombined.zeroControl, none), S⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (SourceCSPGlobalDecisionProgram.Control a q)) ∧
      S SourceCSPGlobalDecisionProgram.outputSlot =
        EncodedCNF.encode (SourceBooleanEncoding.threeCNF P.system hq) := by
  rw [zero_raw_header hq P hn]
  obtain ⟨t, S, ht, hr, ho⟩ := zero_global_header a q
  refine ⟨t, S, ht, hr, ?_⟩
  rw [ho, SourceCSPGuardedCodec.zero_instance_encoding hq P hn]
  decide


end EthInapproximability.CurrentPaper.SourceCSPZeroTyped
