import Paper2.YaoCompositionFullBank

/-! Translate the raw selector-count run into the numbered-stack machine
and retain its unary `H` input bank, rather than certifying only output. -/

namespace Paper2.YaoParameterBank

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open Paper2.YaoParameterLoader
open Paper2.YaoLowerBound
open Paper2.YaoLookup

theorem selector_count_full_bank (t b lambda : ℕ) :
    ∃ steps ≤ 1 + MatrixAddressMachine.exactTime (2 ^ b)
        (fixedWidth t) (fixedTail t lambda),
      let M := selectorCountMachine t lambda
      let c := M.run steps (M.init (List.replicate (2 ^ b) true))
      c.l = none ∧
        c.stk M.input = List.replicate (2 ^ b) true ∧
        c.stk M.output = List.replicate (selectorCount t b lambda) true := by
  obtain ⟨steps, hs, hr⟩ := count_run t lambda (2 ^ b)
  refine ⟨steps, hs, ?_⟩
  let M := selectorCountMachine t lambda
  let inBits := List.replicate (2 ^ b) true
  let ek := Fintype.equivFin (Fin 6)
  let el := Fintype.equivFin CountLabel
  let ev := Fintype.equivFin Bool
  have hi : M.init inBits = renameCfg ek el ev (countStart (2 ^ b)) := by
    change (ofFinite (0 : Fin 6) (5 : Fin 6) (none : CountLabel)
      false (countProgram t lambda)).init inBits = _
    rw [ofFinite_init]
    congr 1
    unfold rawInit countStart
    congr 1
    funext k
    fin_cases k <;> rfl
  have he : M.run steps (M.init inBits) =
      renameCfg ek el ev
        (BitMachineInline.cfg some id none
          (MatrixAddressMachine.cfg none false
            (List.replicate (2 ^ b) true)
            (List.replicate (fixedWidth t) true)
            (List.replicate (fixedTail t lambda) true) [] []
            (List.replicate
              (2 ^ b * fixedWidth t + fixedTail t lambda) true))) := by
    rw [hi]
    have hrun := ofFinite_run (0 : Fin 6) (5 : Fin 6)
      (none : CountLabel) false (countProgram t lambda)
      (countStart (2 ^ b)) steps
    rw [hr] at hrun
    simpa only [ek, el, ev, M, selectorCountMachine] using hrun
  change (M.run steps (M.init inBits)).l = none ∧
    (M.run steps (M.init inBits)).stk M.input = inBits ∧
    (M.run steps (M.init inBits)).stk M.output =
      List.replicate (selectorCount t b lambda) true
  rw [he]
  constructor
  · rfl
  constructor
  · have hk : M.input = ek (0 : Fin 6) := rfl
    rw [hk]
    simp only [renameCfg, Equiv.symm_apply_apply]
    rfl
  · have hk : M.output = ek (5 : Fin 6) := rfl
    rw [hk]
    simp only [renameCfg, Equiv.symm_apply_apply]
    exact congrArg (fun n => List.replicate n true)
      (selector_count_polynomial_formula t b lambda)

#print axioms selector_count_full_bank

theorem equal_halting_runs (M : Machine) (c : M.Config)
    (m n : ℕ) (hm : (M.run m c).l = none)
    (hn : (M.run n c).l = none) : M.run m c = M.run n c := by
  rcases le_total m n with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [BitMachine.run_add, BitMachine.run_halted M _ hm]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [BitMachine.run_add, BitMachine.run_halted M _ hn]

theorem selector_count_halt_preserves_H (t b lambda n : ℕ)
    (hhalt : ((selectorCountMachine t lambda).run n
      ((selectorCountMachine t lambda).init
        (List.replicate (2 ^ b) true))).l = none) :
    ((selectorCountMachine t lambda).run n
      ((selectorCountMachine t lambda).init
        (List.replicate (2 ^ b) true))).stk
      (selectorCountMachine t lambda).input =
        List.replicate (2 ^ b) true := by
  obtain ⟨steps, _, hsHalt, hsInput, _⟩ := selector_count_full_bank t b lambda
  have he := equal_halting_runs (selectorCountMachine t lambda)
    ((selectorCountMachine t lambda).init (List.replicate (2 ^ b) true))
    n steps hhalt hsHalt
  rw [he]
  exact hsInput

/-- The already joined `e -> b -> H -> selectorCount` program has an
exact composite final configuration. Its count-stage input `H` and output
`selectorCount` are both present in distinct physical banks after halt;
neither is inferred from a semantic output oracle. -/
theorem edge_to_selector_count_full_banks (t e lambda : ℕ) :
    ∃ (a b : ℕ),
      a ≤ 2*e+2 + (UnaryBinaryEncoding.coefficient+6)*(e+1)^2 +
        2*paddedEdgeBits e+2 + 16*paddedEdgeCount e ∧
      b ≤ 1 + MatrixAddressMachine.exactTime (paddedEdgeCount e)
        (fixedWidth t) (fixedTail t lambda) ∧
      let A := logPowerMachine
      let B := selectorCountMachine t lambda
      let ca := A.run a (A.init (List.replicate e true))
      let cb := B.run b (B.init (List.replicate (paddedEdgeCount e) true))
      let final := ((advance (program A B))^[
        a + 2*paddedEdgeCount e+2+b])
          (rawInit (.inl A.input) (.inl A.start)
            (A.initial,B.initial,none) (List.replicate e true))
      final = rightCfg A B ca.var
        (Function.update ca.stk A.output []) cb ∧
      final.stk (.inr (.inl B.input)) =
        List.replicate (paddedEdgeCount e) true ∧
      final.stk (.inr (.inl B.output)) =
        List.replicate (selectorCount t (paddedEdgeBits e) lambda) true := by
  let A := logPowerMachine
  let B := selectorCountMachine t lambda
  obtain ⟨a,b,ha,hb,_,_,hBhalt,hBout,hrun⟩ :=
    composition_full_run A B (log_power_outputs e)
      (selector_count_outputs t (paddedEdgeBits e) lambda)
  have hrun' : ((advance (program A B))^[
        a + 2*paddedEdgeCount e+2+b])
          (rawInit (.inl A.input) (.inl A.start)
            (A.initial,B.initial,none) (List.replicate e true)) =
      rightCfg A B (A.run a (A.init (List.replicate e true))).var
        (Function.update (A.run a (A.init (List.replicate e true))).stk A.output [])
        (B.run b (B.init (List.replicate (paddedEdgeCount e) true))) := by
    simpa only [List.length_replicate] using hrun
  refine ⟨a,b,ha,?_,?_⟩
  · simpa only [paddedEdgeCount] using hb
  · dsimp only
    refine ⟨hrun', ?_, ?_⟩
    · rw [hrun', rightCfg_right_bank]
      exact selector_count_halt_preserves_H t (paddedEdgeBits e) lambda b hBhalt
    · rw [hrun', rightCfg_right_bank]
      exact hBout

#print axioms edge_to_selector_count_full_banks

end Paper2.YaoParameterBank
