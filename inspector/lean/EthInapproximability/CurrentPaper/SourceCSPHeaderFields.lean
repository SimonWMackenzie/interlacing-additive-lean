import EthInapproximability.CurrentPaper.SourceCSPHeaderCheck

/-!
# Retained variable header words through fixed-parameter checks

The literal constant-word checks consume only the `a,q` words. This
companion exposes the original `n,m` words on the same physical bank for
subsequent bounded-unary guards, without altering the frozen header checker.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPHeaderFields

open Turing BitMachineEncoding BitMachineStackEmbedding

theorem parser_variable_words (n m a q : Nat) (rest : List Bool) :
    SourceCSPHeaderCheck.parserAfter n m a q rest (.inl (.inl 0)) = n.bits ∧
      SourceCSPHeaderCheck.parserAfter n m a q rest (.inl (.inl 1)) = m.bits := by
  constructor
  · simpa [SourceCSPHeaderParse.numbers] using
      SourceCSPHeaderCheck.parser_word n m a q rest 0
  · simpa [SourceCSPHeaderParse.numbers] using
      SourceCSPHeaderCheck.parser_word n m a q rest 1

theorem canonical_variable_words (n m a q : Nat) (rest : List Bool) :
    ∃ t S v, t ≤ 4 * (2 *
        (SourceCSPHeaderParse.header n m a q ++ rest).length + 4) + 3 +
        (a.bits.length + 1) + (q.bits.length + 1) + 2 ∧
      SourceCSPHeaderCheck.fixedHeaderRun a q t
        (⟨some (.inl (.inl (.start 0))), (((none, none), none), none),
          SourceCSPHeaderCheck.parserInitial
            (SourceCSPHeaderParse.header n m a q ++ rest)⟩ :
          TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
                (SourceFixedBinaryCheck.Label a.bits))
              (SourceFixedBinaryCheck.Label q.bits))
            (BitMachineRawSequence.Control
              (BitMachineRawSequence.Control SourceCSPRowController.Control (Option Bool))
              (Option Bool))) =
        ⟨none, (((none, none), none), v), S⟩ ∧
      S (.inr 0) = [true, true] ∧
      S (.inl (.inl 0)) = n.bits ∧
      S (.inl (.inl 1)) = m.bits ∧
      S (.inl (.inr 0)) = rest := by
  obtain ⟨tp, vp, hp, hpr⟩ := SourceCSPHeaderCheck.parser_canonical n m a q rest
  obtain ⟨hpn, hpm⟩ := parser_variable_words n m a q rest
  have ha : SourceCSPHeaderCheck.parserAfter n m a q rest (.inl (.inl 2)) =
      a.bits := by
    simpa [SourceCSPHeaderParse.numbers] using
      SourceCSPHeaderCheck.parser_word n m a q rest 2
  obtain ⟨ta, va, Sa, hta, hra, hsa, hvarA, hsourceA⟩ :=
    SourceCSPHeaderCheck.checker_total a.bits a.bits [] 2
      (SourceCSPHeaderCheck.parserAfter n m a q rest) ha
      (SourceCSPHeaderCheck.parser_status n m a q rest)
  have hqa : Sa (.inl (.inl 3)) = q.bits := by
    rw [hvarA 3 (by decide)]
    simpa [SourceCSPHeaderParse.numbers] using
      SourceCSPHeaderCheck.parser_word n m a q rest 3
  obtain ⟨tq, vq, Sq, htq, hrq, hsq, hvarQ, hsourceQ⟩ :=
    SourceCSPHeaderCheck.checker_total q.bits q.bits [true] 3 Sa hqa
      (by simpa using hsa)
  obtain ⟨tpa, htpa, hrpa⟩ := BitMachineRawSequence.runs
    SourceCSPHeaderCheck.parserProgram
    (SourceCSPHeaderCheck.checkerProgram a.bits 2)
    (.start 0 : SourceCSPRowController.Label 4 0)
    (.compare 0 : SourceFixedBinaryCheck.Label a.bits)
    ((none, none) : SourceCSPRowController.Control) vp
    (none : Option Bool) va
    (SourceCSPHeaderCheck.parserInitial
      (SourceCSPHeaderParse.header n m a q ++ rest))
    (SourceCSPHeaderCheck.parserAfter n m a q rest) Sa tp ta hpr hra
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceCSPHeaderCheck.alphabetProgram a)
    (SourceCSPHeaderCheck.checkerProgram q.bits 3)
    (.inl (.start 0) : BitMachineRawSequence.Label
      (SourceCSPRowController.Label 4 0)
      (SourceFixedBinaryCheck.Label a.bits))
    (.compare 0 : SourceFixedBinaryCheck.Label q.bits)
    (((none, none), none) :
      BitMachineRawSequence.Control SourceCSPRowController.Control (Option Bool))
    ((none, none), va) (none : Option Bool) vq
    (SourceCSPHeaderCheck.parserInitial
      (SourceCSPHeaderParse.header n m a q ++ rest))
    Sa Sq tpa tq hrpa hrq
  refine ⟨t, Sq, vq, ?_, hr, ?_, ?_, ?_, ?_⟩
  · omega
  · simpa using hsq
  · rw [hvarQ 0 (by decide), hvarA 0 (by decide)]
    exact hpn
  · rw [hvarQ 1 (by decide), hvarA 1 (by decide)]
    exact hpm
  · rw [hsourceQ, hsourceA]
    change bank SourceCSPHeaderCheck.parserEmbedding _ _
      (SourceCSPHeaderCheck.parserEmbedding (.inr 0)) = rest
    rw [bank_at]
    rfl

end EthInapproximability.CurrentPaper.SourceCSPHeaderFields
