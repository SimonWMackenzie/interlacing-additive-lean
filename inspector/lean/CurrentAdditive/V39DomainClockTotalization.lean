import CurrentAdditive.GeneralPolynomialClockBound

/-! Domain-restricted polynomial machines can be made physically total by
the existing charged unary-fuel writer and bounded simulation. The domain
may be undecidable. No test for membership in it is performed. -/

noncomputable section
open Classical

namespace CurrentAdditive.V39DomainClockTotalization

open EthInapproximability.CurrentPaper

theorem polynomial_le_written_fuel (c d n : ℕ) :
    c*(n+1)^d ≤ (n+2)^(c+d+1) := by
  have hc : c ≤ (n+2)^c :=
    (Nat.le_of_lt Nat.lt_two_pow_self).trans
      (Nat.pow_le_pow_left (by omega : 2 ≤ n+2) c)
  have hd := Nat.pow_le_pow_left (by omega : n+1 ≤ n+2) d
  calc
    c*(n+1)^d ≤ (n+2)^c*(n+2)^d := Nat.mul_le_mul hc hd
    _ = (n+2)^(c+d) := by rw [pow_add]
    _ ≤ (n+2)^(c+d+1) := Nat.pow_le_pow_right (by omega : 1 ≤ n+2) (by omega)

/-- One actual all-word polynomial program preserves every source run on
its promised domain. Unary clock construction and timeout execution are
charged by GeneralPolynomialClock.polytime, not supplied as advice. -/
theorem totalize_on_domain
    (Domain : List Bool → Prop) (f : List Bool → List Bool)
    (M : BitMachine.Machine) (c d : ℕ)
    (hvalid : ∀ word, Domain word →
      M.OutputsWithin word (f word) (c*(word.length+1)^d)) :
    ∃ total : List Bool → List Bool,
      BitMachine.Polytime total ∧ ∀ word, Domain word → total word = f word := by
  let degree := c+d
  let total := GeneralPolynomialClock.result degree M
  refine ⟨total, GeneralPolynomialClock.polytime degree M, ?_⟩
  intro word hw
  have hbound : c*(word.length+1)^d ≤
      GeneralPolynomialFuelPrefix.clockLength (degree := degree) word :=
    polynomial_le_written_fuel c d word.length
  have hs := GeneralPolynomialClock.outputs_valid degree M word (f word)
    (BitMachine.outputsWithin_mono M (hvalid word hw) hbound)
  exact BitMachine.outputsWithin_unique (GeneralPolynomialClock.machine degree M)
    (GeneralPolynomialClock.outputs_all degree M word) hs

namespace DefaultBit

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := Fin 2

def program (_ : Unit) : TM2.Stmt (fun _ : Stack => Bool) Unit (Option Bool) :=
  pop 0 (fun _ b => b) (push 1 (fun b => b.getD false) halt)

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (1 : Stack) () none program

/-- A literal one-step physical default gate. Its output is always exactly
one bit, including on empty or malformed source output. -/
theorem outputs (word : List Bool) :
    machine.OutputsWithin word [word.headD false] 1 := by
  apply outputsWithin_of_raw_run (0 : Stack) (1 : Stack) () none program
    word [word.headD false] 1 1 (by omega)
  · simp [advance, program, TM2.step, TM2.stepAux, rawInit]
  · cases word <;> simp [advance, program, TM2.step, TM2.stepAux, rawInit, List.headD]

theorem polytime : BitMachine.Polytime (fun word => [word.headD false]) := by
  refine ⟨machine, 1, 0, ?_⟩
  intro word
  simpa using outputs word

end DefaultBit

/-- Totalization for comparator bits. Timeout and malformed executions return
one default bit; valid singleton source outputs are preserved exactly. -/
theorem totalize_boolean_on_domain
    (Domain : List Bool → Prop) (answer : List Bool → Bool)
    (M : BitMachine.Machine) (c d : ℕ)
    (hvalid : ∀ word, Domain word →
      M.OutputsWithin word [answer word] (c*(word.length+1)^d)) :
    ∃ total : List Bool → Bool,
      BitMachine.Polytime (fun word => [total word]) ∧
      ∀ word, Domain word → total word = answer word := by
  obtain ⟨total, hpoly, heq⟩ := totalize_on_domain Domain
    (fun word => [answer word]) M c d hvalid
  refine ⟨fun word => (total word).headD false, ?_, ?_⟩
  · exact BitMachineComposition.polytime_comp hpoly DefaultBit.polytime
  · intro word hw
    simp [heq word hw]

#print axioms totalize_on_domain
#print axioms DefaultBit.outputs
#print axioms DefaultBit.polytime
#print axioms totalize_boolean_on_domain

end CurrentAdditive.V39DomainClockTotalization
