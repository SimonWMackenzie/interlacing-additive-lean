import CurrentAdditive.TrialSearchCombinedSearchState

/-! Physical branch transitions for the complete finite-field trial search. -/

namespace CurrentAdditive.FieldSearchCompletion

set_option maxHeartbeats 1000000

open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedCallback
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedOuterExact
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedOuterLift (boundary)
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSearchState
open CurrentAdditive.FieldMachineHelper.TrialSearchControllerBridge
open CurrentAdditive.FieldMachineHelper.TrialCounterMachine
open CurrentAdditive.FieldMachineHelper.CounterBitEncoding (testBit_bitsValue)
open CurrentAdditive.FieldMachineHelper.TrialDividerTotal (divisionClock)
open CurrentAdditive.FiniteFieldConstructor.TrialSearch (monicBits remainder)

namespace Outer
export CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine
  (Label Config cfg run run_after_passing_last_degree
   run_after_passing_last_divisor_next_degree
   run_after_failing_nonlast_candidate run_after_failing_last_candidate)
end Outer

def callbackClock (d e : Nat) : Nat :=
  1 + 4 * d + 6 + (divisionClock e (d - e + 1) + 2 * e + 3)

theorem callback_state
    (d c e t : Nat) (he : e ≤ d) (hc : c < 2 ^ d)
    (ht : t < 2 ^ e) (base : Registers) :
    ∃ u ≤ callbackClock d e,
      let g := run u ⟨some (.outer .test), base, searchBank d c e t⟩
      g.l = some (.outer .afterTest) ∧
      g.var.outer.1 =
        (remainder d e (monicBits e t) (monicBits d c) != 0) ∧
      g.stk = searchBank d c e t := by
  let S := searchBank d c e t
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    searchBank_stacks d c e t
  obtain ⟨u, hu, h⟩ :=
    combined_test_from_controller d e c t he hc ht base S
      h0 h1 h2 h3 h4 h5 h6 h7
  refine ⟨u, hu, ?_⟩
  change (run u ⟨some (.outer .test), base, S⟩).l = _ ∧ _ at h
  rcases h with ⟨hl, hb, h0', h1', h2', h3', h4', h5', h6', h7', hf⟩
  refine ⟨hl, hb, ?_⟩
  funext i
  fin_cases i
  · exact h0'
  · exact h1'
  · exact h2'
  · exact h3'.trans h3.symm
  · exact h4'.trans h4.symm
  · exact h5'.trans h5.symm
  · exact h6'.trans h6.symm
  · exact h7'.trans h7.symm
  · exact hf 8 (by decide)
  · exact hf 9 (by decide)
  · exact hf 10 (by decide)
  · exact hf 11 (by decide)

#print axioms callback_state

/-- A physical test followed by any checked controller branch is one run of
the same twelve-stack machine. The branch is checked on the exact post-test
registers and stacks, so this lemma does not assume a callback oracle. -/
theorem callback_then_controller
    (d c e t : Nat) (he : e ≤ d) (hc : c < 2 ^ d)
    (ht : t < 2 ^ e) (base : Registers)
    (target : Outer.Label) (n : Nat)
    (hbranch : ∀ (s : Outer.Control),
      s.1 = (remainder d e (monicBits e t) (monicBits d c) != 0) →
      (Outer.run n
        ⟨some .afterTest, s, searchBank d c e t⟩).l = some target)
    (hboundary : boundary target) :
    ∃ steps ≤ callbackClock d e + n,
      let g := run steps
        ⟨some (.outer .test), base, searchBank d c e t⟩
      g.l = some (.outer target) ∧
      g.stk =
        (Outer.run n
          ⟨some .afterTest,
            (run (steps - n)
              ⟨some (.outer .test), base, searchBank d c e t⟩).var.outer,
            searchBank d c e t⟩).stk := by
  obtain ⟨u, hu, hcallback⟩ := callback_state d c e t he hc ht base
  let g := run u ⟨some (.outer .test), base, searchBank d c e t⟩
  change g.l = _ ∧ _ at hcallback
  rcases hcallback with ⟨hl, hb, hs⟩
  have hlocal := hbranch g.var.outer hb
  have hlocal' :
      (Outer.run n ⟨some .afterTest, g.var.outer, g.stk⟩).l =
        some target := by
    rw [hs]
    exact hlocal
  have hglobal := combined_controller_exact g.var g.stk .afterTest target n
    hlocal' hboundary
  refine ⟨u + n, by omega, ?_⟩
  have hcfg : g = ⟨some (.outer .afterTest), g.var, g.stk⟩ := by
    rcases g with ⟨l, v, S⟩
    change l = some (.outer .afterTest) at hl
    cases hl
    rfl
  have htime : u + n - n = u := by omega
  simp only [htime]
  rw [CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.run_add]
  change (run n g).l = some (.outer target) ∧
    (run n g).stk =
      (Outer.run n ⟨some .afterTest, g.var.outer,
        searchBank d c e t⟩).stk
  have hrun : run n g =
      ⟨some (.outer target),
        {g.var with outer :=
          (Outer.run n ⟨some .afterTest, g.var.outer, g.stk⟩).var},
        (Outer.run n ⟨some .afterTest, g.var.outer, g.stk⟩).stk⟩ := by
    rw [hcfg]
    exact hglobal
  rw [hrun, hs]
  exact ⟨rfl, rfl⟩

#print axioms callback_then_controller

/-- Exact stack state after the physical callback and a concrete controller
branch. This is the reusable iteration step for the search schedule. -/
theorem callback_then_exact_bank
    (d c e t : Nat) (he : e ≤ d) (hc : c < 2 ^ d)
    (ht : t < 2 ^ e) (base : Registers)
    (target : Outer.Label) (n : Nat) (finalBank : Fin 12 → List Bool)
    (hbranch : ∀ (s : Outer.Control),
      s.1 = (remainder d e (monicBits e t) (monicBits d c) != 0) →
      let q := Outer.run n
        ⟨some .afterTest, s, searchBank d c e t⟩
      q.l = some target ∧ q.stk = finalBank)
    (hboundary : boundary target) :
    ∃ steps ≤ callbackClock d e + n,
      let g := run steps
        ⟨some (.outer .test), base, searchBank d c e t⟩
      g.l = some (.outer target) ∧ g.stk = finalBank := by
  obtain ⟨u, hu, hcallback⟩ := callback_state d c e t he hc ht base
  let g := run u ⟨some (.outer .test), base, searchBank d c e t⟩
  change g.l = _ ∧ _ at hcallback
  rcases hcallback with ⟨hl, hb, hs⟩
  obtain ⟨hlocalLabel, hlocalBank⟩ := hbranch g.var.outer hb
  have hlocalLabel' :
      (Outer.run n ⟨some .afterTest, g.var.outer, g.stk⟩).l =
        some target := by rw [hs]; exact hlocalLabel
  have hglobal := combined_controller_exact g.var g.stk .afterTest target n
    hlocalLabel' hboundary
  refine ⟨u + n, by omega, ?_⟩
  have hcfg : g = ⟨some (.outer .afterTest), g.var, g.stk⟩ := by
    rcases g with ⟨l, v, S⟩
    change l = some (.outer .afterTest) at hl
    cases hl
    rfl
  rw [CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.run_add]
  change (run n g).l = some (.outer target) ∧
    (run n g).stk = finalBank
  have hrun : run n g =
      ⟨some (.outer target),
        {g.var with outer :=
          (Outer.run n ⟨some .afterTest, g.var.outer, g.stk⟩).var},
        (Outer.run n ⟨some .afterTest, g.var.outer, g.stk⟩).stk⟩ := by
    rw [hcfg]
    exact hglobal
  rw [hrun]
  constructor
  · rfl
  · rw [hs]; exact hlocalBank

#print axioms callback_then_exact_bank

theorem counterWord_wrap (width : Nat) :
    counterWord width (2 ^ width) = counterWord width 0 := by
  apply List.ext_getElem
  · simp [counterWord_length]
  · intro i hi hj
    have hleft := testBit_bitsValue (counterWord width (2 ^ width)) i
    have hright := testBit_bitsValue (counterWord width 0) i
    rw [counterWord_value] at hleft hright
    simp only [Nat.mod_self, Nat.zero_mod] at hleft hright
    simp only [List.getElem?_eq_getElem hi, Option.getD_some] at hleft
    simp only [List.getElem?_eq_getElem hj, Option.getD_some] at hright
    exact hleft.symm.trans hright

#print axioms counterWord_wrap

theorem pass_last_degree
    (d c e t : Nat) (he : e = d / 2)
    (hd : e ≤ d) (hc : c < 2 ^ d)
    (ht : t + 1 = 2 ^ e) (hpass :
      (remainder d e (monicBits e t) (monicBits d c) != 0) = true)
    (base : Registers) :
    ∃ steps ≤ callbackClock d e + (2 * e + 5),
      let g := run steps
        ⟨some (.outer .test), base, searchBank d c e t⟩
      g.l = some (.outer .success) ∧
      g.stk 0 = counterWord d c := by
  let finalBank := Outer.bank (counterWord d c) (counterWord e (t + 1))
    (List.replicate (d - e) true) (fun _ => []) []
    (List.replicate (e - 1) true) (List.replicate (e - 1) true) []
  have hbranch (s : Outer.Control)
      (hs : s.1 =
        (remainder d e (monicBits e t) (monicBits d c) != 0)) :
      let q := Outer.run (2 * e + 5)
        ⟨some .afterTest, s, searchBank d c e t⟩
      q.l = some .success ∧ q.stk = finalBank := by
    have hs' : s.1 = true := by rw [hs, hpass]
    rcases s with ⟨b, carry, bit⟩
    cases b with
    | false => simp at hs'
    | true =>
      have hcarry := increment_counter_carry_last e t ht
      have hrun := Outer.run_after_passing_last_degree
        (counterWord d c) (counterWord e t)
        (List.replicate (d - e) true) (fun _ => [])
        (List.replicate (e - 1) true) (List.replicate (e - 1) true)
        carry bit hcarry
      have hcfg :
          (⟨some .afterTest, (true, carry, bit),
            searchBank d c e t⟩ : Outer.Config) =
          Outer.cfg (some .afterTest) (true, carry, bit)
            (counterWord d c) (counterWord e t)
            (List.replicate (d - e) true) (fun _ => [])
            [true] (List.replicate (e - 1) true)
            (List.replicate (e - 1) true) [] := by
        simp [searchBank, Outer.cfg, he]
      rw [hcfg]
      have hrun' :
          Outer.run (2 * e + 5)
            (Outer.cfg (some .afterTest) (true, carry, bit)
              (counterWord d c) (counterWord e t)
              (List.replicate (d - e) true) (fun _ => [])
              [true] (List.replicate (e - 1) true)
              (List.replicate (e - 1) true) []) =
            Outer.cfg (some .success) (true, true, none)
              (counterWord d c) (counterWord e (t + 1))
              (List.replicate (d - e) true) (fun _ => []) []
              (List.replicate (e - 1) true)
              (List.replicate (e - 1) true) [] := by
        simpa [counterWord_increment, counterWord_length] using hrun
      rw [hrun']
      exact ⟨rfl, rfl⟩
  obtain ⟨steps, hsteps, hout⟩ :=
    callback_then_exact_bank d c e t hd hc (by omega) base
      .success (2 * e + 5) finalBank hbranch (by trivial)
  refine ⟨steps, hsteps, ?_⟩
  change (run steps ⟨some (.outer .test), base,
    searchBank d c e t⟩).l = _ ∧ _ at hout
  rcases hout with ⟨hl, hbank⟩
  exact ⟨hl, by rw [hbank]; rfl⟩

#print axioms pass_last_degree

theorem pass_last_divisor_next_degree
    (d c e t : Nat) (he : 0 < e) (helt : e < d / 2)
    (hc : c < 2 ^ d) (ht : t + 1 = 2 ^ e)
    (hpass :
      (remainder d e (monicBits e t) (monicBits d c) != 0) = true)
    (base : Registers) :
    ∃ steps ≤ callbackClock d e + (4 * e + 8),
      let g := run steps
        ⟨some (.outer .test), base, searchBank d c e t⟩
      g.l = some (.outer .test) ∧
      g.stk = searchBank d c (e + 1) 0 := by
  have hed : e ≤ d := by omega
  have hshift : List.replicate (d - e) true =
      true :: List.replicate (d - (e + 1)) true := by
    have hn : d - e = (d - (e + 1)) + 1 := by omega
    rw [hn]
    simp [List.replicate_succ]
  have hremaining : List.replicate (d / 2 - e + 1) true =
      true :: true :: List.replicate (d / 2 - e - 1) true := by
    have hn : d / 2 - e + 1 = (d / 2 - e - 1) + 2 := by omega
    rw [hn]
    simp [List.replicate_succ]
  have hnewremaining : List.replicate (d / 2 - (e + 1) + 1) true =
      true :: List.replicate (d / 2 - e - 1) true := by
    have hn : d / 2 - (e + 1) + 1 = (d / 2 - e - 1) + 1 := by omega
    rw [hn]
    simp [List.replicate_succ]
  have hnewused : List.replicate ((e + 1) - 1) true =
      true :: List.replicate (e - 1) true := by
    have hn : (e + 1) - 1 = (e - 1) + 1 := by omega
    rw [hn]
    simp [List.replicate_succ]
  have hused : true :: List.replicate (e - 1) true =
      List.replicate e true := by
    have hn : e = (e - 1) + 1 := by omega
    rw [hn]
    simp [List.replicate_succ]
  have hword :
      (incrementAux true (counterWord e t)).2 ++ [false] =
        counterWord (e + 1) 0 := by
    rw [counterWord_increment, ht, counterWord_wrap]
    have hrep (n : Nat) (b : Bool) :
        List.replicate n b ++ [b] = List.replicate (n + 1) b := by
      induction n with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ, ih]
    simpa [counterWord] using hrep e false
  let finalBank := Outer.bank (counterWord d c)
    ((incrementAux true (counterWord e t)).2 ++ [false])
    (List.replicate (d - (e + 1)) true) (fun _ => [])
    (true :: List.replicate (d / 2 - e - 1) true)
    (true :: List.replicate (e - 1) true)
    (true :: List.replicate (e - 1) true) []
  have hbranch (s : Outer.Control)
      (hs : s.1 =
        (remainder d e (monicBits e t) (monicBits d c) != 0)) :
      let q := Outer.run (4 * e + 8)
        ⟨some .afterTest, s, searchBank d c e t⟩
      q.l = some .test ∧ q.stk = finalBank := by
    have hs' : s.1 = true := by rw [hs, hpass]
    rcases s with ⟨b, carry, bit⟩
    cases b with
    | false => simp at hs'
    | true =>
      have hcarry := increment_counter_carry_last e t ht
      have hrun := Outer.run_after_passing_last_divisor_next_degree
        (counterWord d c) (counterWord e t)
        (List.replicate (d - (e + 1)) true) (fun _ => [])
        (List.replicate (d / 2 - e - 1) true)
        (List.replicate (e - 1) true)
        (List.replicate (e - 1) true)
        carry bit hcarry
      have hcfg :
          (⟨some .afterTest, (true, carry, bit),
            searchBank d c e t⟩ : Outer.Config) =
          Outer.cfg (some .afterTest) (true, carry, bit)
            (counterWord d c) (counterWord e t)
            (true :: List.replicate (d - (e + 1)) true)
            (fun _ => [])
            (true :: true :: List.replicate (d / 2 - e - 1) true)
            (List.replicate (e - 1) true)
            (List.replicate (e - 1) true) [] := by
        simp [searchBank, Outer.cfg, hshift, hremaining]
      rw [hcfg]
      have hrun' :
          Outer.run (4 * e + 8)
            (Outer.cfg (some .afterTest) (true, carry, bit)
              (counterWord d c) (counterWord e t)
              (true :: List.replicate (d - (e + 1)) true)
              (fun _ => [])
              (true :: true :: List.replicate (d / 2 - e - 1) true)
              (List.replicate (e - 1) true)
              (List.replicate (e - 1) true) []) =
          Outer.cfg (some .test) (true, true, none)
            (counterWord d c)
            ((incrementAux true (counterWord e t)).2 ++ [false])
            (List.replicate (d - (e + 1)) true) (fun _ => [])
            (true :: List.replicate (d / 2 - e - 1) true)
            (true :: List.replicate (e - 1) true)
            (true :: List.replicate (e - 1) true) [] := by
        simpa [counterWord_length] using hrun
      rw [hrun']
      exact ⟨rfl, rfl⟩
  obtain ⟨steps, hsteps, hout⟩ :=
    callback_then_exact_bank d c e t hed hc (by omega) base
      .test (4 * e + 8) finalBank hbranch (by trivial)
  refine ⟨steps, hsteps, ?_⟩
  change (run steps ⟨some (.outer .test), base,
    searchBank d c e t⟩).l = _ ∧ _ at hout
  rcases hout with ⟨hl, hbank⟩
  refine ⟨hl, hbank.trans ?_⟩
  funext i
  fin_cases i <;>
    simp [finalBank, searchBank, Outer.bank, hword, hnewremaining,
      hused]

#print axioms pass_last_divisor_next_degree

theorem fail_nonlast_candidate
    (d c e t : Nat) (he : 0 < e) (hed : e ≤ d / 2)
    (hc : c + 1 < 2 ^ d) (ht : t < 2 ^ e)
    (hfail :
      (remainder d e (monicBits e t) (monicBits d c) != 0) = false)
    (base : Registers) :
    ∃ steps ≤ callbackClock d e + (2 * d + 3 * e + 4),
      let g := run steps
        ⟨some (.outer .test), base, searchBank d c e t⟩
      g.l = some (.outer .test) ∧
      g.stk = searchBank d (c + 1) 1 0 := by
  have he' : e ≤ d := by omega
  have hdpos : 0 < d := by omega
  have hhalfpos : 0 < d / 2 := by omega
  have hnext := increment_counter_carry_nonlast d c hc
  have hshift : List.replicate (e - 1) true ++
      List.replicate (d - e) true =
        List.replicate (d - 1) true := by
    rw [← List.replicate_add]
    congr 1
    omega
  have hremaining : List.replicate (e - 1) true ++
      List.replicate (d / 2 - e + 1) true =
        List.replicate (d / 2) true := by
    rw [← List.replicate_add]
    congr 1
    omega
  have hdivisor : ([false] : List Bool) = counterWord 1 0 := rfl
  let finalBank := Outer.bank (counterWord d (c + 1)) [false]
    (List.replicate (e - 1) true ++ List.replicate (d - e) true)
    (fun _ => [])
    (List.replicate (e - 1) true ++
      List.replicate (d / 2 - e + 1) true) [] [] []
  have hbranch (s : Outer.Control)
      (hs : s.1 =
        (remainder d e (monicBits e t) (monicBits d c) != 0)) :
      let q := Outer.run (2 * d + 3 * e + 4)
        ⟨some .afterTest, s, searchBank d c e t⟩
      q.l = some .test ∧ q.stk = finalBank := by
    have hs' : s.1 = false := by rw [hs, hfail]
    rcases s with ⟨b, carry, bit⟩
    cases b with
    | true => simp at hs'
    | false =>
      have hrun := Outer.run_after_failing_nonlast_candidate
        (counterWord d c) (counterWord e t)
        (List.replicate (d - e) true) (fun _ => [])
        (List.replicate (d / 2 - e + 1) true)
        (List.replicate (e - 1) true)
        (List.replicate (e - 1) true)
        carry bit hnext
      have hcfg :
          (⟨some .afterTest, (false, carry, bit),
            searchBank d c e t⟩ : Outer.Config) =
          Outer.cfg (some .afterTest) (false, carry, bit)
            (counterWord d c) (counterWord e t)
            (List.replicate (d - e) true) (fun _ => [])
            (List.replicate (d / 2 - e + 1) true)
            (List.replicate (e - 1) true)
            (List.replicate (e - 1) true) [] := by
        rfl
      rw [hcfg]
      have hrun' :
          Outer.run (2 * d + 3 * e + 4)
            (Outer.cfg (some .afterTest) (false, carry, bit)
              (counterWord d c) (counterWord e t)
              (List.replicate (d - e) true) (fun _ => [])
              (List.replicate (d / 2 - e + 1) true)
              (List.replicate (e - 1) true)
              (List.replicate (e - 1) true) []) =
            Outer.cfg (some .test) (false, false, none)
              (counterWord d (c + 1)) [false]
              (List.replicate (e - 1) true ++
                List.replicate (d - e) true)
              (fun _ => [])
              (List.replicate (e - 1) true ++
                List.replicate (d / 2 - e + 1) true) [] [] [] := by
        have hclock :
            2 * (counterWord d c).length +
              (counterWord e t).length +
              (List.replicate (e - 1) true).length +
              (List.replicate (e - 1) true).length + 6 =
              2 * d + 3 * e + 4 := by
          simp [counterWord_length]
          omega
        rw [hclock] at hrun
        simpa [counterWord_increment] using hrun
      rw [hrun']
      exact ⟨rfl, rfl⟩
  obtain ⟨steps, hsteps, hout⟩ :=
    callback_then_exact_bank d c e t he' (by omega) ht base
      .test (2 * d + 3 * e + 4) finalBank hbranch (by trivial)
  refine ⟨steps, hsteps, ?_⟩
  change (run steps ⟨some (.outer .test), base,
    searchBank d c e t⟩).l = _ ∧ _ at hout
  rcases hout with ⟨hl, hbank⟩
  refine ⟨hl, hbank.trans ?_⟩
  funext i
  fin_cases i <;>
    simp [finalBank, searchBank, Outer.bank, hshift, hremaining,
      hdivisor, show d / 2 - 1 + 1 = d / 2 by omega]

#print axioms fail_nonlast_candidate

theorem fail_last_candidate
    (d c e t : Nat) (he : 0 < e) (hed : e ≤ d / 2)
    (hc : c + 1 = 2 ^ d) (ht : t < 2 ^ e)
    (hfail :
      (remainder d e (monicBits e t) (monicBits d c) != 0) = false)
    (base : Registers) :
    ∃ steps ≤ callbackClock d e + (2 * d + 3),
      let g := run steps
        ⟨some (.outer .test), base, searchBank d c e t⟩
      g.l = some (.outer .exhausted) := by
  have he' : e ≤ d := by omega
  have hlast := increment_counter_carry_last d c hc
  have hbranch (s : Outer.Control)
      (hs : s.1 =
        (remainder d e (monicBits e t) (monicBits d c) != 0)) :
      (Outer.run (2 * d + 3)
        ⟨some .afterTest, s, searchBank d c e t⟩).l = some .exhausted := by
    have hs' : s.1 = false := by rw [hs, hfail]
    rcases s with ⟨b, carry, bit⟩
    cases b with
    | true => simp at hs'
    | false =>
      have hrun := Outer.run_after_failing_last_candidate
        (counterWord d c) (counterWord e t)
        (List.replicate (d - e) true) (fun _ => [])
        (List.replicate (d / 2 - e + 1) true)
        (List.replicate (e - 1) true)
        (List.replicate (e - 1) true)
        carry bit hlast
      have hcfg :
          (⟨some .afterTest, (false, carry, bit),
            searchBank d c e t⟩ : Outer.Config) =
          Outer.cfg (some .afterTest) (false, carry, bit)
            (counterWord d c) (counterWord e t)
            (List.replicate (d - e) true) (fun _ => [])
            (List.replicate (d / 2 - e + 1) true)
            (List.replicate (e - 1) true)
            (List.replicate (e - 1) true) [] := by rfl
      rw [hcfg]
      have hclock : 2 * (counterWord d c).length + 3 = 2 * d + 3 := by
        simp [counterWord_length]
      rw [hclock] at hrun
      simpa [Outer.cfg] using
        congrArg (fun q : Outer.Config => q.l) hrun
  obtain ⟨steps, hsteps, hout⟩ :=
    callback_then_controller d c e t he' (by omega) ht base
      .exhausted (2 * d + 3) hbranch (by trivial)
  exact ⟨steps, hsteps, hout.1⟩

#print axioms fail_last_candidate

end CurrentAdditive.FieldSearchCompletion
