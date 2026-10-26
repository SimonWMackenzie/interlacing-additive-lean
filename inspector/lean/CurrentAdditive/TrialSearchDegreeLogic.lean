import CurrentAdditive.TrialSearchFailingDegree

/-! Boolean schedule facts for the exact frozen trial-division predicate. -/

namespace CurrentAdditive.FieldSearchCompletion

open CurrentAdditive.FiniteFieldConstructor.TrialSearch

def pairPass (d c e t : Nat) : Bool :=
  remainder d e (monicBits e t) (monicBits d c) != 0

def degreePass (d c e : Nat) : Bool :=
  (List.range (2 ^ e)).all (pairPass d c e)

theorem trialIrreducible_eq_degrees (d c : Nat) :
    trialIrreducible d c =
      (List.range (d / 2)).all fun e0 => degreePass d c (e0 + 1) := by
  rfl

theorem degreePass_true (d c e : Nat)
    (h : degreePass d c e = true) :
    ∀ t < 2 ^ e, pairPass d c e t = true := by
  intro t ht
  exact (List.all_eq_true.mp h) t (List.mem_range.mpr ht)

theorem degreePass_false_first (d c e : Nat)
    (h : degreePass d c e = false) :
    ∃ f < 2 ^ e,
      pairPass d c e f = false ∧
      ∀ t < f, pairPass d c e t = true := by
  have hex : ∃ t, t < 2 ^ e ∧ pairPass d c e t = false := by
    obtain ⟨t, ht, hp⟩ := List.all_eq_false.mp h
    refine ⟨t, List.mem_range.mp ht, ?_⟩
    cases hv : pairPass d c e t <;> simp_all
  let f := Nat.find hex
  have hspec : f < 2 ^ e ∧ pairPass d c e f = false := Nat.find_spec hex
  refine ⟨f, hspec.1, hspec.2, ?_⟩
  intro t ht
  have hn : ¬(t < 2 ^ e ∧ pairPass d c e t = false) :=
    Nat.find_min hex ht
  have hwithin : t < 2 ^ e := by omega
  cases hv : pairPass d c e t <;> simp_all

#print axioms trialIrreducible_eq_degrees
#print axioms degreePass_true
#print axioms degreePass_false_first

end CurrentAdditive.FieldSearchCompletion
