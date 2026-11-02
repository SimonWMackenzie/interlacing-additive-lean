import EthInapproximability.CurrentPaper.SourceCSPRowControllerTotal

/-!
# Literal parsing of the four canonical CSP header fields

The fixed four-field row controller is reused as a header reader with an
empty table. Its finite bank positions 0,1,2,3 hold the original canonical
binary words for `n,m,a,q`; no number is decoded in finite control.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPHeaderParse

open Turing BitMachineEncoding EncodedCommunication

abbrev Bank := SourceCSPRowController.Bank 4
abbrev Config := TM2.Cfg (fun _ : SourceCSPRowController.Stack 4 => Bool)
  (SourceCSPRowController.Label 4 0) SourceCSPRowController.Control

def numbers (n m a q : Nat) : Fin 4 → Nat := ![n, m, a, q]

def header (n m a q : Nat) : List Bool :=
  natField n ++ natField m ++ natField a ++ natField q

theorem queries_eq_header (n m a q : Nat) :
    SourceCSPRowController.queriesFrom 0 (numbers n m a q) =
      header n m a q := by
  simp [SourceCSPRowController.queriesFrom, numbers, header]

theorem canonical_run (n m a q : Nat) (rest : List Bool) :
    ∃ t, t ≤ 4 * (2 * (header n m a q ++ rest).length + 4) + 3 ∧
      SourceCSPRowController.run (H := 0) t
        (SourceCSPRowController.cfg (H := 0) (some (.start 0)) (none, none)
          (fun _ => []) (header n m a q ++ rest) [] []) =
        SourceCSPRowController.cfg (H := 0) none (none, none)
          (fun j => (numbers n m a q j).bits) rest [] [true] := by
  obtain ⟨t, ht, hr⟩ := SourceCSPRowController.row_run
    4 0 (numbers n m a q) [] rest [] rfl
  rw [queries_eq_header] at ht hr
  refine ⟨t, ?_, ?_⟩
  · simpa only [List.append_nil, List.nil_append, Nat.mul_zero, Nat.zero_add] using ht
  · simpa only [List.append_nil, List.nil_append] using hr

theorem canonical_words (n m a q : Nat) (rest : List Bool) :
    ∃ (t : Nat) (c : Config),
      t ≤ 4 * (2 * (header n m a q ++ rest).length + 4) + 3 ∧
      SourceCSPRowController.run (H := 0) t
        (SourceCSPRowController.cfg (H := 0) (some (.start 0)) (none, none)
          (fun _ => []) (header n m a q ++ rest) [] []) = c ∧
      c.l = none ∧ c.stk (.inl 0) = n.bits ∧
      c.stk (.inl 1) = m.bits ∧ c.stk (.inl 2) = a.bits ∧
      c.stk (.inl 3) = q.bits ∧ c.stk (.inr 0) = rest ∧
      c.stk (.inr 2) = [true] := by
  obtain ⟨t, ht, hr⟩ := canonical_run n m a q rest
  refine ⟨t, _, ht, hr, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem all_input (input : List Bool) :
    ∃ (t : Nat) (c : Config), t ≤ 4 * (2 * input.length + 4) + 3 ∧
      SourceCSPRowController.run (H := 0) t
        (SourceCSPRowController.cfg (H := 0) (some (.start 0))
          (none, none) (fun _ => []) input [] []) = c ∧
      c.l = none ∧
      c.stk (.inr 2) = SourceCSPRowController.rowResult 4 0 input := by
  obtain ⟨t, ht, hp⟩ := SourceCSPRowController.controller_total 4 0 input []
  refine ⟨t, _, by simpa only [Nat.mul_zero, Nat.zero_add] using ht,
    rfl, hp.1, ?_⟩
  simpa only [List.append_nil] using hp.2

end EthInapproximability.CurrentPaper.SourceCSPHeaderParse
