import EthInapproximability.CurrentPaper.SourceValidRoute

namespace EthInapproximability.CurrentPaper.SourceValidAcceptance

open Turing BitMachineEncoding EncodedCommunication
open scoped Classical

theorem canonical_header_unique {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (n m : Nat) (rest : List Bool)
    (hinput : EncodedETHSource.constraintBits P =
      SourceCSPHeaderParse.header n m a q ++ rest) :
    n = P.vertices ∧ m = P.constraints ∧
      rest = SourceCSPCodec.fnFields SourceCSPCodec.rowFields
        (SourceCSPCodec.rowsOf P) := by
  let numbers := SourceCSPHeaderParse.numbers n m a q
  let rows := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
    (SourceCSPCodec.rowsOf P)
  have hother := SourceCSPRowCodecConverse.parse_canonical_zero
    numbers rest
  have htyped := canonical_parse P
  rw [hinput, ← SourceCSPHeaderParse.queries_eq_header] at htyped
  have heq : ((fun j => (numbers j).bits), rest) =
      (headerBank P, rows) := Option.some.inj (hother.symm.trans htyped)
  have hn := congrArg
    (fun p : (SourceCSPRowController.Bank 4 × List Bool) =>
      EncodedCommunication.bitsValue (p.1 0)) heq
  have hm := congrArg
    (fun p : (SourceCSPRowController.Bank 4 × List Bool) =>
      EncodedCommunication.bitsValue (p.1 1)) heq
  have hr := congrArg
    (fun p : (SourceCSPRowController.Bank 4 × List Bool) => p.2) heq
  have hn' : n = P.vertices := by
    simpa [numbers, headerBank, SourceCSPHeaderParse.numbers] using hn
  have hm' : m = P.constraints := by
    simpa [numbers, headerBank, SourceCSPHeaderParse.numbers] using hm
  exact ⟨hn', hm', hr⟩

#print axioms canonical_header_unique

end EthInapproximability.CurrentPaper.SourceValidAcceptance
