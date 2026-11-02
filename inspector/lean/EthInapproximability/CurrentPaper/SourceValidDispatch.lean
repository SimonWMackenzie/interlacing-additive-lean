import EthInapproximability.CurrentPaper.SourceCSPGlobalTotalValidation
import EthInapproximability.CurrentPaper.SourceCSPHeaderBankTransport
import EthInapproximability.CurrentPaper.SourceCSPRowCodecConverse
import EthInapproximability.CurrentPaper.SourceCSPGuardedCodec

namespace EthInapproximability.CurrentPaper.SourceValidAcceptance

open Turing BitMachineEncoding EncodedCommunication
open scoped Classical

def headerBank {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q) :
    SourceCSPRowController.Bank 4 :=
  fun i => (SourceCSPHeaderParse.numbers
    P.vertices P.constraints a q i).bits

theorem canonical_parse {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q) :
    SourceCSPRowController.readQueriesFrom (q := 4) 0
      (EncodedETHSource.constraintBits P) (fun _ => []) =
      some (headerBank P,
        SourceCSPCodec.fnFields SourceCSPCodec.rowFields
          (SourceCSPCodec.rowsOf P)) := by
  let rows := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
    (SourceCSPCodec.rowsOf P)
  have he := SourceCSPGuardedCodec.input_eq_header_rows P
  rw [he, ← SourceCSPHeaderParse.queries_eq_header]
  exact SourceCSPRowCodecConverse.parse_canonical_zero
    (SourceCSPHeaderParse.numbers P.vertices P.constraints a q) rows

theorem vertex_word_nonempty (n : Nat) (hn : 0 < n) :
    n.bits ≠ [] := by
  intro h
  have hv := EncodedCommunication.bitsValue_bits n
  rw [h] at hv
  simp [EncodedCommunication.bitsValue] at hv
  omega

theorem dispatch_positive {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hn : 0 < P.vertices) :
    ∃ t S v,
      t ≤ SourceCSPGuardDispatchSequence.bound a q
        (EncodedETHSource.constraintBits P).length ∧
      ((advance (SourceCSPGuardDispatchSequence.program a q))^[t])
        (⟨some (.inl (SourceCSPGuardDispatchSequence.headerStart a q)),
          (SourceCSPGuardDispatchSequence.headerInitial,
            SourceCSPGuardDispatch.initialControl),
          SourceCSPInputFrame.initial
            (EncodedETHSource.constraintBits P)⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool) _ _) =
        ⟨none, (SourceCSPGuardDispatchSequence.headerInitial, v), S⟩ ∧
      v.2 = some .positive := by
  let input := EncodedETHSource.constraintBits P
  let rows := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
    (SourceCSPCodec.rowsOf P)
  obtain ⟨t, S, v, ht, hr, hvertex, hcount, hsource, hunary, hv⟩ :=
    SourceCSPHeaderBankTransport.dispatch_success_bank a q input
      (headerBank P) rows (canonical_parse P)
  refine ⟨t, S, v, ht, hr, ?_⟩
  have hcountFits : P.constraints ≤ input.length :=
    SourceCSPCodec.constraints_le_bits P
  have hne := vertex_word_nonempty P.vertices hn
  rw [hv]
  simp [SourceCSPGuardDispatch.classify, headerBank,
    SourceCSPHeaderParse.numbers,
    EncodedCommunication.bitsValue_bits, hcountFits, hne]

#print axioms dispatch_positive

end EthInapproximability.CurrentPaper.SourceValidAcceptance
