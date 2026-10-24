import EthInapproximability.CurrentPaper.SamplerEnumeration

/-!
# A single fixed-width counter enumerates every trial factor pair

Source: locked v8 Appendix E, `lem:exact-families`, polynomial factor search.
The lower and upper halves of the width-`2*n` counter are the two width-`n`
factors. Exhausting the actual counter without an accepted factor pair is
equivalent to the existing exact executable irreducibility test.
-/

namespace EthInapproximability.CurrentPaper.SamplerFactorEnumeration

open ExecutableSmallBiasSampler SamplerMachine SamplerEnumeration

theorem encodeWord_decodeWord (n : ℕ) (q : List Bool) (hq : q.length = n) :
    encodeWord (decodeWord n q) = q := by
  apply List.ext_getElem
  · simpa using hq.symm
  · intro i hi hj
    simp [encodeWord, decodeWord, List.getElem?_eq_getElem hj]

def lowerWord (n : ℕ) (q : List Bool) : BinaryWord n := decodeWord n (q.take n)

def upperWord (n : ℕ) (q : List Bool) : BinaryWord n := decodeWord n (q.drop n)

theorem lowerWord_encoded {n : ℕ} (u v : BinaryWord n) :
    lowerWord n (encodeWord u ++ encodeWord v) = u := by
  have ht : (encodeWord u ++ encodeWord v).take n = encodeWord u := by
    simpa only [encodeWord_length] using
      (List.take_left : (encodeWord u ++ encodeWord v).take (encodeWord u).length = encodeWord u)
  rw [lowerWord, ht, decodeWord_encodeWord]

theorem upperWord_encoded {n : ℕ} (u v : BinaryWord n) :
    upperWord n (encodeWord u ++ encodeWord v) = v := by
  have ht : (encodeWord u ++ encodeWord v).drop n = encodeWord v := by
    simpa only [encodeWord_length] using
      (List.drop_left : (encodeWord u ++ encodeWord v).drop (encodeWord u).length = encodeWord v)
  rw [upperWord, ht, decodeWord_encodeWord]

theorem counter_decomposition (n : ℕ) (q : List Bool) (hq : q.length = 2 * n) :
    encodeWord (lowerWord n q) ++ encodeWord (upperWord n q) = q := by
  have hlo : (q.take n).length = n := by simp [hq]; omega
  have hhi : (q.drop n).length = n := by simp [hq]; omega
  rw [lowerWord, upperWord, encodeWord_decodeWord n (q.take n) hlo,
    encodeWord_decodeWord n (q.drop n) hhi, List.take_append_drop]

theorem exists_counter_decomposition (n : ℕ) (q : List Bool) (hq : q.length = 2 * n) :
    ∃ u v : BinaryWord n, q = encodeWord u ++ encodeWord v :=
  ⟨lowerWord n q, upperWord n q, (counter_decomposition n q hq).symm⟩

/-- The literal combined counter word with two supplied factor halves. -/
def pairWord {n : ℕ} (u v : BinaryWord n) : BinaryWord (2 * n) :=
  decodeWord (2 * n) (encodeWord u ++ encodeWord v)

theorem encodeWord_pairWord {n : ℕ} (u v : BinaryWord n) :
    encodeWord (pairWord u v) = encodeWord u ++ encodeWord v := by
  apply encodeWord_decodeWord
  simp only [List.length_append, encodeWord_length]
  omega

theorem mem_factor_counter {n : ℕ} (u v : BinaryWord n) :
    encodeWord u ++ encodeWord v ∈ counterWords (2 * n) := by
  rw [← encodeWord_pairWord]
  exact counterWords_contains (pairWord u v)

theorem counter_member_length {n : ℕ} {q : List Bool} (hq : q ∈ counterWords n) :
    q.length = n := by
  rw [counterWords_eq] at hq
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hq
  exact encodeWord_length w

/-- The Boolean produced by the split, product, and comparison controller. -/
def factorPredicate (n : ℕ) (c : BinaryWord n) (q : List Bool) : Bool :=
  decide (Nonconstant (lowerWord n q) ∧ Nonconstant (upperWord n q) ∧
    ∀ j : Fin (2 * n), monicCoeff n c j.val =
      rawProductCoeff (lowerWord n q) (upperWord n q) j.val)

theorem factorPredicate_encoded {n : ℕ} (c u v : BinaryWord n) :
    factorPredicate n c (encodeWord u ++ encodeWord v) =
      (decide (Nonconstant u) && decide (Nonconstant v) &&
        decide (∀ j : Fin (2 * n), monicCoeff n c j.val = rawProductCoeff u v j.val)) := by
  simp only [factorPredicate, lowerWord_encoded, upperWord_encoded, Bool.decide_and,
    Bool.and_assoc]

def factorSearch (n : ℕ) (c : BinaryWord n) : Option (List Bool) :=
  (counterWords (2 * n)).find? (factorPredicate n c)

/-- The counter search excludes exactly the nonconstant factor products,
including all potential leading-zero factor encodings. -/
theorem factorSearch_none_iff (n : ℕ) (c : BinaryWord n) :
    factorSearch n c = none ↔ fixedFactorTest n c = true := by
  rw [factorSearch, List.find?_eq_none, fixedFactorTest, decide_eq_true_eq]
  constructor
  · intro h u v hu hv heq
    have hbad := h (encodeWord u ++ encodeWord v) (mem_factor_counter u v)
    apply hbad
    simp only [factorPredicate_encoded, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hu, hv⟩, heq⟩
  · intro h q hq hp
    obtain ⟨u, v, rfl⟩ := exists_counter_decomposition n q (counter_member_length hq)
    have hb : (Nonconstant u ∧ Nonconstant v) ∧
        ∀ j : Fin (2 * n), monicCoeff n c j.val = rawProductCoeff u v j.val := by
      simpa only [factorPredicate_encoded, Bool.and_eq_true, decide_eq_true_eq] using hp
    exact h u v hb.1.1 hb.1.2 hb.2

theorem factorSearch_none_iff_irreducible {n : ℕ} (hn : 0 < n) (c : BinaryWord n) :
    factorSearch n c = none ↔ irreducibleTest n c = true := by
  rw [factorSearch_none_iff, fixedFactorTest_eq hn]

/-- The outer search's acceptance bit agrees with the original exact test. -/
theorem factorSearch_exhaustion_bit {n : ℕ} (hn : 0 < n) (c : BinaryWord n) :
    decide (factorSearch n c = none) = irreducibleTest n c := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.decide_iff, factorSearch_none_iff_irreducible hn]

end EthInapproximability.CurrentPaper.SamplerFactorEnumeration
