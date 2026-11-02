import EthInapproximability.CurrentPaper.SourceGenericConverterClock
import EthInapproximability.CurrentPaper.SourceValidAccepted
import EthInapproximability.CurrentPaper.SourceCSPZeroTyped
import EthInapproximability.CurrentPaper.EncodedETHSourceComposition

/-!
# The fixed generic converter: total clock, valid typed outputs, cited Dinur
# outputs (unit 1, segment 5)

Paper B, locked v8 Section 6 (`thm:paper-sparse-gap-source`) and Appendix B;
CP-SOURCE-EFFECTIVE, arbitrary fixed positive alphabet `a = D.alphabet`.

* `converter_total`: ONE fixed program `Converter.converter a q hq` halts on
  EVERY raw bit list within `convC a q * (|input|+1)^27` steps, branching
  through the actual validator: reject (the admitted non-language reject word),
  zero (`[false,false]`), or accept (continuing the SAME reached bank through
  prefix, rows, header and finalizer to the literal encoded three-CNF of the
  read-back instance). All answers are in the validator output slot.
* `converter_valid`: on the literal encoding `constraintBits P` of a typed
  instance with `ValidSize P` (zero vertices included, via the admitted
  `SourceCSPZeroTyped.typed_zero_global`; positive via the admitted
  `SourceValidAcceptance.accepted_halt`, `canonical_header_unique`,
  `canonical_rows_read`), the output is `encode (threeCNF P.system hq)`.
* `converter_dinur`: on the cited Dinur bit function's actual output for a
  valid formula, the output is `encode (booleanFormula D f).val`, the exact
  consumer object of `EncodedETHSourceComposition`. `ValidSize` is the cited
  `D.no_isolates`; no `a = 2`, positivity promise or supplied output is used.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.Converter

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

theorem global_le_envelope (a q : Nat) (input : List Bool) (tb : Nat)
    (c : SourceCSPGlobalDecisionProgram.Control a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (htb : tb ≤ SourceCSPGlobalTotalValidation.totalBound a q input.length + 1)
    (hrun : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tb])
      (SourceCSPGlobalDecisionProgram.initial a q input) = ⟨none, c, S⟩)
    (g : SourceCSPGlobalDecisionProgram.Stack q) :
    (S g).length ≤ AcceptedSource.envelope a q input.length := by
  have h := AcceptedSource.global_cells_le a q input tb c S htb hrun g
  unfold AcceptedSource.envelope
  omega

theorem nonaccepted_clock_le (a q L tg : Nat)
    (htg : tg ≤ SourceCSPGlobalTotalValidation.totalBound a q L + 1) :
    tg + 1 ≤ convC a q * (L + 1) ^ 27 := by
  obtain ⟨hTB, _⟩ := controller_parts_le a q L
  have hX : 0 < L + 1 := by omega
  have hX3 : (L + 1) ^ 3 ≤ (L + 1) ^ 27 := pow_mono _ 3 27 hX (by norm_num)
  have h1 : 1 ≤ (L + 1) ^ 27 := Nat.one_le_pow _ _ hX
  have hc : (ctlC a q + 1) * (L + 1) ^ 3 ≤ (ctlC a q + 1) * (L + 1) ^ 27 :=
    Nat.mul_le_mul_left _ hX3
  have e : convC a q * (L + 1) ^ 27 =
      2 * ((ctlC a q + 1) * (L + 1) ^ 27) +
      PrefixAmbientProgram.ambientCoefficient a q * (q + 1) ^ 9 * (L + 1) ^ 27 +
      sufC a q * (hC a q + 1) ^ 9 * (L + 1) ^ 27 + phC a q * (L + 1) ^ 27 +
      5 * (L + 1) ^ 27 := by
    unfold convC; ring
  rw [e]
  omega

theorem outCell_global {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool) :
    bank (globalEmbC q) (fun _ => []) S (outCell q) =
      S SourceCSPGlobalDecisionProgram.outputSlot := by
  unfold outCell
  exact bank_at _ _ _ _

/-- Total: every raw input, one fixed program, one polynomial clock. -/
theorem converter_total {a q : Nat} (ha : 0 < a) (hq : 0 < q) (input : List Bool) :
    ∃ t ≤ convC a q * (input.length + 1) ^ 27,
      ∃ (c : FirstRow.CtlOf (converter a q hq)) (W : CStack q → List Bool),
        ((advance (converter a q hq))^[t]) (converterInitial a q hq input) =
          ⟨none, c, W⟩ ∧
        ((W (outCell q) = SourceCSPRejectFormula.bits ∧
            W (outCell q) ∉ EncodedCNF.Language) ∨
          W (outCell q) = [false, false] ∨
          (∃ (n m : Nat) (rows : Fin m → SourceCSPCodec.Row n a q) (suffix : List Bool),
            input = SourceCSPHeaderParse.header n m a q ++ suffix ∧
            SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
              some (rows, []) ∧
            W (outCell q) = EncodedCNF.encode (SourceBooleanEncoding.threeCNF
              (SourceCSPCodec.fromRows n m a q rows).system hq))) := by
  obtain ⟨tg, htg, c, S, hglobal, _ts, _hts, _d, _U, _hsel, hcase⟩ :=
    SourceCSPTotalSelectiveScratch.raw_total_selective a q input
  rcases hcase with hreje | hzero | hacc
  · obtain ⟨hc, _, hout, hnlang, _, _⟩ := hreje
    obtain ⟨t, ht, hrun⟩ := topC_nonaccepted_run (body (a := a) hq)
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (SourceCSPFirstRowController.bodyStart (q := q) (a := a))))
      (bodyInit (a := a) hq) input tg c S hglobal hc
    refine ⟨t, ht.trans (nonaccepted_clock_le a q _ tg htg), _, _, hrun,
      Or.inl ⟨?_, ?_⟩⟩
    · rw [outCell_global]; exact hout
    · rw [outCell_global]; exact hnlang
  · obtain ⟨hc, _, hout, _, _⟩ := hzero
    have hnot : SourceCSPSelectiveStage.acceptedControl c = false := by
      rw [hc]; rfl
    obtain ⟨t, ht, hrun⟩ := topC_nonaccepted_run (body (a := a) hq)
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (SourceCSPFirstRowController.bodyStart (q := q) (a := a))))
      (bodyInit (a := a) hq) input tg c S hglobal hnot
    refine ⟨t, ht.trans (nonaccepted_clock_le a q _ tg htg), _, _, hrun,
      Or.inr (Or.inl ?_)⟩
    rw [outCell_global]; exact hout
  · obtain ⟨n, m, rest, rows, vr, hc, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hacc
    rw [hc] at hglobal
    obtain ⟨n', m', hm', suffix', rows', U', lastRow', t, _, hsize', hmL', hinput',
      hread', hUenv, ht, hrun, hout⟩ := accepted_run ha hq input tg vr S hglobal
    have hsuffix : suffix'.length ≤ input.length := by rw [hinput']; simp
    have hS := global_le_envelope a q input tg _ S htg hglobal
      SourceCSPGlobalDecisionProgram.outputSlot
    have hclock := accepted_clock_le hq hm' input suffix' rows' U' S hsize' hmL'
      hsuffix hUenv hS
    exact ⟨t, ht.trans hclock, _, _, hrun,
      Or.inr (Or.inr ⟨n', m', rows', suffix', hinput', hread', hout⟩)⟩

/-- Valid typed outputs (the internal converter's actual consumer domain),
including the legitimate zero-vertex case. -/
theorem converter_valid {a q : Nat} (ha : 0 < a) (hq : 0 < q)
    (P : EncodedETHSource.ConstraintInstance a q)
    (hsize : SourceCSPCodec.ValidSize P) :
    ∃ t ≤ convC a q * ((EncodedETHSource.constraintBits P).length + 1) ^ 27,
      ∃ (c : FirstRow.CtlOf (converter a q hq)) (W : CStack q → List Bool),
        ((advance (converter a q hq))^[t])
            (converterInitial a q hq (EncodedETHSource.constraintBits P)) =
          ⟨none, c, W⟩ ∧
        W (outCell q) = EncodedCNF.encode (SourceBooleanEncoding.threeCNF P.system hq) := by
  obtain ⟨tg, htg, c, S, hglobal, _ts, _hts, _d, _U, _hsel, _hcase⟩ :=
    SourceCSPTotalSelectiveScratch.raw_total_selective a q (EncodedETHSource.constraintBits P)
  by_cases hz : P.vertices = 0
  · -- legitimate zero case: the admitted typed zero arm
    obtain ⟨tz, Sz, _, hrz, houtz⟩ := SourceCSPZeroTyped.typed_zero_global hq P hz
    have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique
      (SourceCSPGlobalDecisionProgram.program a q)
      (SourceCSPGlobalDecisionProgram.initial a q (EncodedETHSource.constraintBits P))
      tg tz (by rw [hglobal]) (by rw [hrz])
    have hc : c = .prefix (SourceCSPGuardOutputCombined.zeroControl, none) := by
      have h := congrArg (fun z => z.var) heq
      simpa only [hglobal, hrz] using h
    have hS : S = Sz := by
      have h := congrArg (fun z => z.stk) heq
      simpa only [hglobal, hrz] using h
    subst hS
    have hnot : SourceCSPSelectiveStage.acceptedControl c = false := by
      rw [hc]; rfl
    obtain ⟨t, ht, hrun⟩ := topC_nonaccepted_run (body (a := a) hq)
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (SourceCSPFirstRowController.bodyStart (q := q) (a := a))))
      (bodyInit (a := a) hq) (EncodedETHSource.constraintBits P) tg c S hglobal hnot
    refine ⟨t, ht.trans (nonaccepted_clock_le a q _ tg htg), _, _, hrun, ?_⟩
    rw [outCell_global]; exact houtz
  · -- positive case: the admitted accepting halt, then the converter body
    have hn : 0 < P.vertices := Nat.pos_of_ne_zero hz
    obtain ⟨ta, vr, Sa, _, hacc⟩ := SourceValidAcceptance.accepted_halt P hn hsize
    obtain ⟨tb, _, _, _, _, htb, hglob, _⟩ :=
      AcceptedSource.raw_accepted_source a q (EncodedETHSource.constraintBits P) ta vr Sa hacc
    obtain ⟨n, m, hm, suffix, rows, U, lastRow, t, _, hsize', hmL, hinput,
      hread, hUenv, ht, hrun, hout⟩ := accepted_run ha hq (EncodedETHSource.constraintBits P) ta vr Sa hacc
    have hsuffix : suffix.length ≤ (EncodedETHSource.constraintBits P).length := by rw [hinput]; simp
    have hS := global_le_envelope a q (EncodedETHSource.constraintBits P) tb _ Sa htb hglob
      SourceCSPGlobalDecisionProgram.outputSlot
    have hclock := accepted_clock_le hq hm (EncodedETHSource.constraintBits P) suffix rows U Sa hsize' hmL
      hsuffix hUenv hS
    obtain ⟨hnEq, hmEq, hsEq⟩ :=
      SourceValidAcceptance.canonical_header_unique P n m suffix hinput
    subst hnEq
    subst hmEq
    subst hsEq
    have hrr := hread.symm.trans (SourceValidAcceptance.canonical_rows_read P)
    have hrows : rows = SourceCSPCodec.rowsOf P :=
      (Prod.mk.inj (Option.some.inj hrr)).1
    subst hrows
    rw [SourceCSPCodec.fromRows_rowsOf] at hout
    exact ⟨t, ht.trans hclock, _, _, hrun, hout⟩

/-- The cited Dinur bit function's actual output for a valid formula: the
fixed converter at `a = D.alphabet`, `q = D.arity` outputs exactly the encoded
`booleanFormula D f` within one fixed polynomial of that output's length. -/
theorem converter_dinur (D : EncodedETHSource.DinurReduction)
    (f : EncodedETHSource.ValidFormula) :
    ∃ t ≤ convC D.alphabet D.arity *
        ((D.bitFunction (EncodedCNF.encode f.val)).length + 1) ^ 27,
      ∃ (c : FirstRow.CtlOf (converter D.alphabet D.arity D.arity_pos))
        (W : CStack D.arity → List Bool),
        ((advance (converter D.alphabet D.arity D.arity_pos))^[t])
            (converterInitial D.alphabet D.arity D.arity_pos
              (D.bitFunction (EncodedCNF.encode f.val))) =
          ⟨none, c, W⟩ ∧
        W (outCell D.arity) =
          EncodedCNF.encode (EncodedETHSourceComposition.booleanFormula D f).val := by
  rw [D.bitFunction_valid f]
  exact converter_valid D.alphabet_pos D.arity_pos (D.reduce f) (D.no_isolates f)

#print axioms global_le_envelope
#print axioms nonaccepted_clock_le
#print axioms converter_total
#print axioms converter_valid
#print axioms converter_dinur

end EthInapproximability.CurrentPaper.SourceGenericComposite.Converter
