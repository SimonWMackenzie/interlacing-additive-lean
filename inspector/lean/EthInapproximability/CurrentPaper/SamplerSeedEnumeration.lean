import EthInapproximability.CurrentPaper.SamplerFactorEnumeration

/-!
# Exact seed order for the sampler table

Source: locked v8 Appendix E, `lem:exact-families`. The least-significant
half of the binary counter changes first, whereas the original pair labels
change their second component first. Thus the seed's first component is
the upper half and its second component is the lower half. The identities
below preserve every original label and its order, including repeated
output words. They are enumeration semantics, not machine runtime claims.
-/

namespace EthInapproximability.CurrentPaper.SamplerSeedEnumeration

open ExecutableSmallBiasSampler SamplerMachine SamplerEnumeration SamplerFactorEnumeration

theorem counterWords_succ (n : ℕ) :
    counterWords (n + 1) = (counterWords n).flatMap (fun q => [false :: q, true :: q]) := by
  rw [counterWords_eq, counterWords_eq]
  simp only [allWords, List.map_flatMap, List.flatMap_map,
    List.map_cons, List.map_nil, encodeWord_cons]
  rfl

theorem counterWords_append (n m : ℕ) :
    counterWords (n + m) = (counterWords m).flatMap fun upper =>
      (counterWords n).map (fun lower => lower ++ upper) := by
  induction n with
  | zero => simp [counterWords]
  | succ n ih =>
      rw [show n + 1 + m = (n + m) + 1 by omega, counterWords_succ, ih, counterWords_succ]
      simp only [List.flatMap_assoc, List.flatMap_map, List.map_flatMap,
        List.map_cons, List.map_nil, List.cons_append]

theorem wordLabels_apply (n : ℕ) (j : Fin (2 ^ n)) :
    wordLabels n j = (allWords n)[j.val]'(by rw [allWords_length]; exact j.isLt) := rfl

theorem counterWords_labels (n : ℕ) :
    counterWords n = List.ofFn (fun j : Fin (2 ^ n) => encodeWord (wordLabels n j)) := by
  rw [counterWords_eq]
  apply List.ext_getElem
  · simp [allWords_length]
  · intro j hj hk
    simp only [List.getElem_map, List.getElem_ofFn, wordLabels_apply]

theorem ofFn_pair_labels {α : Type*} {m n : ℕ} (f : Fin m × Fin n → α) :
    List.ofFn (fun j : Fin (m * n) => f (finProdFinEquiv.symm j)) =
      (List.ofFn fun x : Fin m => List.ofFn fun y : Fin n => f (x, y)).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext x
  apply congrArg List.ofFn
  funext y
  apply congrArg f
  apply (Equiv.symm_apply_eq finProdFinEquiv).mpr
  apply Fin.ext
  change x.val * n + y.val = y.val + n * x.val
  ring

theorem wordPairLabels_list (n : ℕ) :
    List.ofFn (wordPairLabels n) =
      (List.ofFn fun x : Fin (2 ^ n) =>
        List.ofFn fun y : Fin (2 ^ n) => (wordLabels n x, wordLabels n y)).flatten := by
  have h := ofFn_pair_labels (fun p : Fin (2 ^ n) × Fin (2 ^ n) =>
    (wordLabels n p.1, wordLabels n p.2))
  simpa only [wordPairLabels, pow_two, Equiv.trans_apply, Equiv.prodCongr_apply,
    finCongr_apply, Fin.cast_eq_self] using h

/-- A seed is stored lower component first, so the second seed changes first. -/
def seedEncoding {n : ℕ} (seed : BinaryWord n × BinaryWord n) : List Bool :=
  encodeWord seed.2 ++ encodeWord seed.1

theorem counterWords_seedOrder (n : ℕ) :
    counterWords (2 * n) = List.ofFn (fun j : Fin ((2 ^ n) ^ 2) =>
      seedEncoding (wordPairLabels n j)) := by
  rw [show 2 * n = n + n by omega, counterWords_append]
  simp_rw [counterWords_labels]
  change _ = List.ofFn (seedEncoding ∘ wordPairLabels n)
  rw [← List.map_ofFn, wordPairLabels_list, List.map_flatten]
  simp only [List.map_ofFn, List.flatMap_def, Function.comp_def, seedEncoding]

def seedOfCounter (n : ℕ) (q : List Bool) : BinaryWord n × BinaryWord n :=
  (upperWord n q, lowerWord n q)

@[simp] theorem seedOfCounter_encoding {n : ℕ} (seed : BinaryWord n × BinaryWord n) :
    seedOfCounter n (seedEncoding seed) = seed := by
  simp only [seedOfCounter, seedEncoding, upperWord_encoded, lowerWord_encoded]

theorem counterWords_seeds (n : ℕ) :
    (counterWords (2 * n)).map (seedOfCounter n) = List.ofFn (wordPairLabels n) := by
  rw [counterWords_seedOrder, List.map_ofFn]
  simp only [Function.comp_def, seedOfCounter_encoding]

def counterAt (n : ℕ) (j : Fin ((2 ^ n) ^ 2)) : List Bool :=
  (SamplerMachineIncrement.increment^[j.val]) (List.replicate (2 * n) false)

theorem counterAt_eq (n : ℕ) (j : Fin ((2 ^ n) ^ 2)) :
    counterAt n j = seedEncoding (wordPairLabels n j) := by
  have hj : j.val < 2 ^ (2 * n) := by
    simpa only [show 2 * n = n * 2 by omega, pow_mul] using j.isLt
  have h := congrArg (fun qs : List (List Bool) => qs[j.val]?) (counterWords_seedOrder n)
  simpa only [counterWords, List.getElem?_iterate _ _ _ _ hj, List.getElem?_ofFn,
    j.isLt, ↓reduceDIte, counterAt, Option.some.injEq] using h

/-- Pointwise form used by the actual incrementing table controller. -/
theorem seedOfCounter_counterAt (n : ℕ) (j : Fin ((2 ^ n) ^ 2)) :
    seedOfCounter n (counterAt n j) = wordPairLabels n j := by
  rw [counterAt_eq, seedOfCounter_encoding]

def counterTraceTable (n L : ℕ) : List Bool :=
  (counterWords (2 * n)).flatMap fun q =>
    List.ofFn fun i : Fin L => encodeBit (executableTraceBits n L (seedOfCounter n q) i)

def labelledTraceTable (n L : ℕ) : List Bool :=
  (List.ofFn fun seed : Fin ((2 ^ n) ^ 2) =>
    List.ofFn fun i : Fin L => encodeBit (executableTraceBits n L (wordPairLabels n seed) i)).flatten

/-- Exact seed-major, coordinate-minor output order, not merely a permutation. -/
theorem counterTraceTable_eq (n L : ℕ) :
    counterTraceTable n L = labelledTraceTable n L := by
  rw [counterTraceTable, counterWords_seedOrder]
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_def,
    seedOfCounter_encoding, labelledTraceTable]

theorem counterTraceTable_length (n L : ℕ) :
    (counterTraceTable n L).length = (2 ^ n) ^ 2 * L := by
  rw [counterTraceTable_eq]
  simp [labelledTraceTable, List.length_flatten, List.map_ofFn, Function.comp_def]

/-- The materialized executable evaluator is the original table interface. -/
theorem counterTraceTable_indexed (L B : ℕ) :
    counterTraceTable (SmallBiasSampler.fieldExponent L B) L =
      (List.ofFn fun seed : Fin ((2 ^ SmallBiasSampler.fieldExponent L B) ^ 2) =>
        List.ofFn fun i : Fin L => encodeBit (indexedTraceBits L B seed i)).flatten := by
  simpa only [labelledTraceTable, indexedTraceBits, materializedTraceBits_eq] using
    counterTraceTable_eq (SmallBiasSampler.fieldExponent L B) L

end EthInapproximability.CurrentPaper.SamplerSeedEnumeration
