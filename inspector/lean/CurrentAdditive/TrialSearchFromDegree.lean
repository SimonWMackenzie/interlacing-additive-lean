import CurrentAdditive.TrialSearchInitialization
import CurrentAdditive.FirstPassingTotal

/-! The full physical search begins with stacks determined by the public
degree, visits candidates in order, and ends with the frozen firstPassing
tail on stack 0. -/

namespace CurrentAdditive.FieldSearchCompletion

set_option maxHeartbeats 1000000

open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSearchState
open CurrentAdditive.FieldMachineHelper.TrialCounterMachine (counterWord)
open CurrentAdditive.FiniteFieldConstructor.TrialSearch

def initialRegisters : Registers :=
  ⟨none, (false, none, none), (false, none), (false, false, none)⟩

def initialConfig (d : Nat) : Config :=
  ⟨some (.outer .initial), initialRegisters, initialBank d⟩

theorem firstPassing_one : firstPassing 1 = some (monicBits 1 0) := by
  decide

theorem physical_firstPassing_given (d c : Nat) (hd : 2 ≤ d)
    (hfirst : firstPassing d = some (monicBits d c)) :
    ∃ steps ≤ 1 + (c + 1) * prefixBudget d (d / 2),
      let g := run steps (initialConfig d)
      g.l = some (.outer .success) ∧
      g.stk 0 = counterWord d c := by
  let q := run 1 (initialConfig d)
  obtain ⟨hl, hs⟩ := initial_run_nonempty d hd initialRegisters
  change q.l = _ at hl
  change q.stk = _ at hs
  have hcfg : q = ⟨some (.outer .test), q.var, searchBank d 0 1 0⟩ := by
    rw [← initialBank_eq_searchBank d hd]
    rcases q with ⟨l, r, S⟩
    change l = _ at hl
    cases hl
    change S = _ at hs
    cases hs
    rfl
  obtain ⟨v, hv, hout⟩ := run_firstPassing_from_test d c hd hfirst q.var
  refine ⟨1 + v, by omega, ?_⟩
  rw [CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.run_add]
  change (run v q).l = some (.outer .success) ∧
    (run v q).stk 0 = counterWord d c
  rw [hcfg]
  exact hout

theorem physical_firstPassing_total (d : Nat) (hd : 0 < d) :
    ∃ c < 2 ^ d,
      firstPassing d = some (monicBits d c) ∧
      ∃ steps ≤ 1 + 2 ^ d * prefixBudget d (d / 2),
        let g := run steps (initialConfig d)
        g.l = some (.outer .success) ∧
        g.stk 0 = counterWord d c := by
  by_cases hone : d = 1
  · subst d
    refine ⟨0, by norm_num, firstPassing_one, 1, ?_, ?_⟩
    · simp [prefixBudget]
    · exact initial_run_one initialRegisters
  · have hd2 : 2 ≤ d := by omega
    obtain ⟨modulus, hmodulus⟩ := firstPassing_total d hd
    obtain ⟨c, hc, hm⟩ := firstPassing_is_candidate hmodulus
    subst modulus
    obtain ⟨steps, hs, hout⟩ := physical_firstPassing_given d c hd2 hmodulus
    refine ⟨c, hc, hmodulus, steps, ?_, hout⟩
    have hmul : (c + 1) * prefixBudget d (d / 2) ≤
        2 ^ d * prefixBudget d (d / 2) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

#print axioms physical_firstPassing_given
#print axioms physical_firstPassing_total

end CurrentAdditive.FieldSearchCompletion
