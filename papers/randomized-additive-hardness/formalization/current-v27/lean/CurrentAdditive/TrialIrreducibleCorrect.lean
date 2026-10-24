import CurrentAdditive.TrialCriterion

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial

theorem trial_irreducible_iff (d tail : ℕ)
    (hd : 0 < d) (htail : tail < 2 ^ d) :
    TrialSearch.trialIrreducible d tail = true ↔
      Irreducible (polynomial (d + 1) (TrialSearch.monicBits d tail)) := by
  let p := polynomial (d + 1) (TrialSearch.monicBits d tail)
  have hmonic : p.Monic := monicBits_monic d tail htail
  have hdeg : p.natDegree = d := monicBits_degree d tail htail
  have hnonzero : p ≠ 0 := hmonic.ne_zero
  have hnonunit : ¬ IsUnit p := Polynomial.not_isUnit_of_natDegree_pos p (by omega)
  rw [trial_iff_no_encoded_factor]
  rw [Polynomial.irreducible_iff_lt_natDegree_lt hnonzero hnonunit]
  constructor
  · intro h ePoly heMonic heRange
    have heRange' : 0 < ePoly.natDegree ∧ ePoly.natDegree ≤ d / 2 := by
      simpa [hdeg, Finset.mem_Ioc] using heRange
    obtain ⟨t, ht, hpoly⟩ := exists_monicBits ePoly.natDegree ePoly
      heMonic rfl
    intro hdiv
    have he : ePoly.natDegree ≤ d := by omega
    have hrem := (remainder_zero_iff_dvd d ePoly.natDegree t tail he ht htail).mpr
      (by simpa [hpoly, p] using hdiv)
    exact (h ePoly.natDegree heRange'.1 heRange'.2 t ht) hrem
  · intro h e he hed t ht
    have he' : e ≤ d := by omega
    have hfmonic := monicBits_monic e t ht
    have hfdegree := monicBits_degree e t ht
    have hrange : (polynomial (e + 1) (TrialSearch.monicBits e t)).natDegree ∈
        Finset.Ioc 0 (p.natDegree / 2) := by
      simpa [hfdegree, hdeg, Finset.mem_Ioc] using And.intro he hed
    have hnot := h _ hfmonic hrange
    intro hrem
    apply hnot
    exact (remainder_zero_iff_dvd d e t tail he' ht htail).mp hrem

#print axioms trial_irreducible_iff

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
