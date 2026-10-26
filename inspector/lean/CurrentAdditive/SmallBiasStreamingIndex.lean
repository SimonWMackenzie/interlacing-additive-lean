import CurrentAdditive.SmallBiasPrintedPairBridge
import CurrentAdditive.StreamingEquivalence

/-!
# Row-major indexing of the physical streaming word list

Source: v27 Appendix G `yao:finite-field-list`. This identifies each
literal list cell, including duplicate decoded words, with the seed pair
used by `printedPairFieldWord`. It is separate from quotient bit semantics.
-/

namespace CurrentAdditive.SmallBias

open CurrentAdditive.FiniteFieldConstructor

private theorem flatMap_range_getElem?
    {α : Type*} (m n : ℕ) (f : ℕ → ℕ → α)
    (x y : ℕ) (hx : x < m) (hy : y < n) :
    (((List.range m).flatMap fun a =>
      (List.range n).map (f a))[x * n + y]?) = some (f x y) := by
  induction m with
  | zero => omega
  | succ m ih =>
      rw [List.range_succ, List.flatMap_append]
      simp only [List.flatMap_singleton]
      by_cases hxm : x < m
      · have hindex : x * n + y <
            ((List.range m).flatMap fun a =>
              (List.range n).map (f a)).length := by
          simp
          have hm := Nat.mul_le_mul_right n (show x + 1 ≤ m by omega)
          have hstep : x * n + n = (x + 1) * n := by ring
          omega
        rw [List.getElem?_append_left hindex]
        exact ih hxm
      · have hxeq : x = m := by omega
        subst x
        have hindex :
            ((List.range m).flatMap fun a =>
              (List.range n).map (f a)).length ≤ m * n + y := by
          simp
        rw [List.getElem?_append_right hindex]
        have hlen :
            ((List.range m).flatMap fun a =>
              (List.range n).map (f a)).length = m * n := by simp
        rw [hlen, Nat.add_sub_cancel_left]
        rw [List.getElem?_map, List.getElem?_range hy]
        rfl

/-- At the row-major index for a physical seed pair, the streaming list
stores exactly that pair and its own word. No quotient-field property is
needed, and duplicate words remain separately labelled cells. -/
theorem streaming_labelledWords_getElem? (d modulus n : ℕ)
    (x y : Fin (2 ^ d)) :
    let k := (printerPairLabel d (x, y)).val
    (StreamingPrinter.labelledWords d modulus n)[k]? =
      some (x.val, y.val, StreamingPrinter.word d modulus n x y) := by
  dsimp only
  have hindex : (printerPairLabel d (x, y)).val =
      x.val * 2 ^ d + y.val := by
    simp [printerPairLabel, finProdFinEquiv]
    ring
  rw [hindex]
  exact flatMap_range_getElem? (2 ^ d) (2 ^ d)
    (fun a b => (a, b, StreamingPrinter.word d modulus n a b))
    x.val y.val x.isLt y.isLt

/-- Each bit of the streaming word is the direct executable bit equation
`dot x (y^j)`. -/
theorem streaming_word_getElem? (d modulus n : ℕ)
    (x y : Fin (2 ^ d)) (j : Fin n) :
    (StreamingPrinter.word d modulus n x y)[j.val]? =
      some (BitPrinter.bit d modulus x.val y.val j.val) := by
  rw [StreamingEquivalence.streaming_eq_direct]
  simp only [BitPrinter.word, List.getElem?_map, List.getElem?_range j.isLt,
    Option.map_some]

/-- The physical list cell and its selected coordinate are exactly the
label and bit used in the v27 printed-pair matrix. -/
theorem streaming_list_matches_printed_pair_array (b t d modulus : ℕ)
    (ℓ : Fin ((2 ^ d) ^ 2))
    (j : Fin (2 ^ b) × Fin (2 ^ t * 2 ^ t + 1)) :
    let xy := (printerPairLabel d).symm ℓ
    let k := (finProdFinEquiv j).val
    (StreamingPrinter.labelledWords d modulus
        (2 ^ b * (2 ^ t * 2 ^ t + 1)))[ℓ.val]? =
      some (xy.1.val, xy.2.val,
        StreamingPrinter.word d modulus
          (2 ^ b * (2 ^ t * 2 ^ t + 1)) xy.1.val xy.2.val) ∧
    (StreamingPrinter.word d modulus
        (2 ^ b * (2 ^ t * 2 ^ t + 1)) xy.1.val xy.2.val)[k]? =
      some (printedPairFieldWord b t d modulus ℓ j) := by
  dsimp only
  let xy := (printerPairLabel d).symm ℓ
  let k := (finProdFinEquiv j).val
  have hlabel : printerPairLabel d xy = ℓ :=
    (printerPairLabel d).apply_symm_apply ℓ
  constructor
  · simpa only [hlabel] using
      (streaming_labelledWords_getElem? d modulus
        (2 ^ b * (2 ^ t * 2 ^ t + 1)) xy.1 xy.2)
  · simpa only [k, printedPairFieldWord, xy] using
      (streaming_word_getElem? d modulus _ xy.1 xy.2
        (finProdFinEquiv j))

#print axioms CurrentAdditive.SmallBias.streaming_labelledWords_getElem?
#print axioms CurrentAdditive.SmallBias.streaming_word_getElem?
#print axioms CurrentAdditive.SmallBias.streaming_list_matches_printed_pair_array

end CurrentAdditive.SmallBias
