import EthInapproximability.CurrentPaper.SourceCSPInputFrame
import EthInapproximability.CurrentPaper.SourceCSPQueryRange

/-!
# Physical bound of the CSP constraint count by raw input length

The binary `m` header word is compared to the unary raw-input length on the
same physical bank. The bounded loop has a transition count polynomial in
the raw bit length, even on rejected inputs. It preserves the original `m`
word and cap; its output is a leading Boolean status followed by unary
`min(m, input.length)`.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPConstraintGuard

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceCSPInputFrame.Stack

def guardEmbedding : SourceCSPQueryRange.Stack ↪ Stack where
  toFun k := if k = 0 then .inl (.inl (.inl 1))
    else if k = 1 then .inr 2 else if k = 2 then .inr 3
    else if k = 3 then .inr 4 else if k = 4 then .inr 5 else .inr 6
  inj' := by intro x y h; fin_cases x <;> fin_cases y <;> simp_all

def Ready (S : Stack → List Bool) (word cap : List Bool) : Prop :=
  S (.inl (.inl (.inl 1))) = word ∧ S (.inr 2) = cap ∧
    S (.inr 3) = [] ∧ S (.inr 4) = [] ∧
    S (.inr 5) = [] ∧ S (.inr 6) = []

def guardProgram (l : SourceCSPQueryRange.Label) :=
  stmt guardEmbedding id id id none (SourceCSPQueryRange.program l)

theorem guard_total (word cap : List Bool) (before : Stack → List Bool)
    (hready : Ready before word cap) :
    ∃ t v S, t ≤ 2 * word.length + 2 + (2 * cap.length + 2) + 1 +
          (cap.length + 1) * (4 * word.length + 5) + 1 ∧
      ((advance guardProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none, none), (none, false)), before⟩ :
          TM2.Cfg (fun _ : Stack => Bool) SourceCSPQueryRange.Label
            SourceCSPQueryRange.Control) = ⟨none, v, S⟩ ∧
      S (.inl (.inl (.inl 1))) = word ∧
      S (.inr 2) = cap ∧
      S (.inr 6) = ProtocolBoundedUnary.result word cap [] ∧
      S (.inl (.inl (.inl 0))) = before (.inl (.inl (.inl 0))) ∧
      S (.inl (.inl (.inr 0))) = before (.inl (.inl (.inr 0))) := by
  obtain ⟨t, c, ht, hr, hh, hword, hcap, _, hout⟩ :=
    SourceCSPQueryRange.range_run word cap []
  let localCfg : SourceCSPQueryRange.Config :=
    ⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
      ((none, none), (none, false)),
      SourceCSPQueryRange.contents word cap [] [] [] []⟩
  have hhalt : (((advance SourceCSPQueryRange.program)^[t]) localCfg).l = none := by
    simpa only [localCfg, hh] using congrArg (fun c => c.l) hr
  obtain ⟨u, hu, hrun⟩ := outputs guardEmbedding before id id id
    (fun _ => rfl) none SourceCSPQueryRange.program guardProgram
    (fun _ => rfl) localCfg t hhalt
  have hstart : cfg guardEmbedding before id id none localCfg =
      (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
        ((none, none), (none, false)), before⟩ :
        TM2.Cfg (fun _ : Stack => Bool) SourceCSPQueryRange.Label
          SourceCSPQueryRange.Control) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k
    · exact hready.1.symm
    · exact hready.2.1.symm
    · exact hready.2.2.1.symm
    · exact hready.2.2.2.1.symm
    · exact hready.2.2.2.2.1.symm
    · exact hready.2.2.2.2.2.symm
  change ((advance SourceCSPQueryRange.program)^[t]) localCfg = _ at hr
  rw [hr, hstart] at hrun
  refine ⟨u, c.var, bank guardEmbedding before c.stk, hu.trans ht,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [cfg, stackCfg, BitMachineInline.cfg,
      id_eq, hh, Option.map_none] using hrun
  · change bank guardEmbedding before c.stk (guardEmbedding 0) = word
    rw [bank_at]
    exact hword
  · change bank guardEmbedding before c.stk (guardEmbedding 1) = cap
    rw [bank_at]
    exact hcap
  · change bank guardEmbedding before c.stk (guardEmbedding 5) = _
    rw [bank_at]
    exact hout
  · apply bank_outside
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [guardEmbedding] at hk
  · apply bank_outside
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [guardEmbedding] at hk

abbrev HeaderLabel (a q : Nat) := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label BitMachineCopy.Label
    SourceInputLengthUnary.CountLabel)
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
      (SourceFixedBinaryCheck.Label a.bits))
    (SourceFixedBinaryCheck.Label q.bits))

abbrev HeaderControl := (Option Bool × Option Bool) ×
  ((SourceCSPRowController.Control × Option Bool) × Option Bool)

def guardedProgram (a q : Nat) :=
  BitMachineRawSequence.program (SourceCSPInputFrame.inputHeaderProgram a q)
    guardProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (((none, none), (((none, none), none), none)) : HeaderControl)
    (((none, none), (none, false)) : SourceCSPQueryRange.Control)

abbrev GuardedConfig (a q : Nat) :=
  TM2.Cfg (fun _ : Stack => Bool)
    (BitMachineRawSequence.Label (HeaderLabel a q) SourceCSPQueryRange.Label)
    (HeaderControl × SourceCSPQueryRange.Control)

/-- Literal three-stage input-length count, fixed-header check and guarded
constraint-count conversion, including every sequence handoff. The result
contains a status bit and a bounded unary `m`; no row loop is asserted. -/
theorem canonical_guarded_header (n m a q : Nat) (rest : List Bool) :
    ∃ (t : Nat) (c : GuardedConfig a q),
      t ≤ 3 * (SourceCSPHeaderParse.header n m a q ++ rest).length + 4 +
        4 * (2 * (SourceCSPHeaderParse.header n m a q ++ rest).length + 4) + 3 +
        (a.bits.length + 1) + (q.bits.length + 1) + 3 +
        (2 * m.bits.length + 2 +
          (2 * (SourceCSPHeaderParse.header n m a q ++ rest).length + 2) + 1 +
          ((SourceCSPHeaderParse.header n m a q ++ rest).length + 1) *
            (4 * m.bits.length + 5) + 1) + 1 ∧
      ((advance (guardedProgram a q))^[t])
        (⟨some (.inl (.inl (.inl BitMachineCopy.Label.scan))),
          ((((none, none), (((none, none), none), none))),
            ((none, none), (none, false))),
          SourceCSPInputFrame.initial
            (SourceCSPHeaderParse.header n m a q ++ rest)⟩ :
          GuardedConfig a q) = c ∧
      c.l = none ∧
      c.stk (.inl (.inl (.inl 0))) = n.bits ∧
      c.stk (.inl (.inl (.inl 1))) = m.bits ∧
      c.stk (.inl (.inl (.inr 0))) = rest ∧
      c.stk (.inr 6) = ProtocolBoundedUnary.result m.bits
        (List.replicate
          (SourceCSPHeaderParse.header n m a q ++ rest).length true) [] := by
  let input := SourceCSPHeaderParse.header n m a q ++ rest
  let cap := List.replicate input.length true
  obtain ⟨th, ch, hth, hrh, hhalt, _, hn, hm, hrest, hcap, hunused⟩ :=
    SourceCSPInputFrame.canonical_input_header n m a q rest
  have hready : Ready ch.stk m.bits cap := by
    refine ⟨hm, hcap, ?_, ?_, ?_, ?_⟩
    · exact hunused 3 (by decide)
    · exact hunused 4 (by decide)
    · exact hunused 5 (by decide)
    · exact hunused 6 (by decide)
  obtain ⟨tg, vg, Sg, htg, hrg, hmg, _, hout, hng, hrestg⟩ :=
    guard_total m.bits cap ch.stk hready
  cases ch with
  | mk l vh Sh =>
    cases l with
    | some l => cases hhalt
    | none =>
      obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
        (SourceCSPInputFrame.inputHeaderProgram a q) guardProgram
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) : HeaderLabel a q)
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) :
          SourceCSPQueryRange.Label)
        (((none, none), (((none, none), none), none)) : HeaderControl) vh
        (((none, none), (none, false)) : SourceCSPQueryRange.Control) vg
        (SourceCSPInputFrame.initial input) Sh Sg th tg hrh hrg
      refine ⟨t, ⟨none,
        (((none, none), (((none, none), none), none)), vg), Sg⟩,
        ?_, ?_, rfl, ?_, ?_, ?_⟩
      · dsimp only [input, cap] at htg
        simp only [List.length_replicate] at htg
        omega
      · simpa only [guardedProgram, input] using hr
      · exact hng.trans hn
      · exact hmg
      · exact ⟨hrestg.trans hrest, hout⟩

theorem guard_result_at_constraint_count (m : Nat) (input : List Bool)
    (hbound : m ≤ input.length) :
    ProtocolBoundedUnary.result m.bits
      (List.replicate input.length true) [] =
        true :: List.replicate m true := by
  simp [ProtocolBoundedUnary.result, EncodedCommunication.bitsValue_bits, hbound]

end EthInapproximability.CurrentPaper.SourceCSPConstraintGuard
