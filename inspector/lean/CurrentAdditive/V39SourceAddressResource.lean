import CurrentAdditive.V39SourceCompiler
import CurrentAdditive.V38EncodedTable

/-! Literal public edge-address selection and its size, for the source emitted
by the strengthened clone compiler. Padding is numerical and handles zero
edges, rather than introducing a promise-dependent edge numbering. -/

namespace CurrentAdditive.V39SourceAddressResource

open CurrentAdditive.V38Source CurrentAdditive.V38Encoded
open CurrentAdditive.V39SourceCompiler
open Paper2.YaoLookup

theorem edgeBits_eq_paddedEdgeBits (e : ℕ) : edgeBits e = paddedEdgeBits e := by
  by_cases h : e = 0
  · simp [h, edgeBits, paddedEdgeBits]
  · rw [paddedEdgeBits, max_eq_right (by omega : 1 ≤ e)]
    rfl

theorem edgeBits_minimal (e m : ℕ) :
    edgeBits e ≤ m ↔ max 1 e ≤ 2 ^ m := by
  rw [edgeBits_eq_paddedEdgeBits]
  exact paddedEdgeBits_minimal e m

theorem capacity_le_twice_succ (e : ℕ) :
    2 ^ edgeBits e ≤ 2 * (e + 1) := by
  by_cases he : e ≤ 1
  · have hz : edgeBits e = 0 := Nat.clog_of_right_le_one he 2
    rw [hz]
    omega
  · have he1 : 1 < e := by omega
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ)) he1
    have hd : 0 < edgeBits e := Nat.clog_pos (by decide) he1
    have heq : 2 ^ edgeBits e = 2 * 2 ^ (edgeBits e - 1) := by
      calc
        _ = 2 ^ (edgeBits e - 1 + 1) := by congr 1; omega
        _ = _ := by rw [pow_succ]; omega
    rw [heq]
    change 2 ^ (edgeBits e - 1) < e at hp
    omega

/-- The least power-of-two address space is bounded by the physically emitted
source word. Empty edge sets have exactly one unused address. -/
theorem source_address_capacity_le_code {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) :
    2 ^ edgeBits (selectedSource G input).2.1 ≤
      2 * (sourceCode G input).length := by
  have hb := capacity_le_twice_succ (selectedSource G input).2.1
  have hc := cloned_counts_le_code G input
  omega

/-- All-input polynomial bound for the selected address capacity. The same
code and source occur in the compiler, decoder, and table indexing. -/
theorem source_address_capacity_poly {t : ℕ} (G : GLSourceInput t) :
    ∃ c d : ℕ, ∀ input,
      2 ^ edgeBits (selectedSource G input).2.1 ≤
        c * (input.length + 1) ^ d := by
  obtain ⟨c, d, hc⟩ := CurrentAdditive.V38Machine.source_encoded_length_poly G
  refine ⟨2 * c, d, fun input => ?_⟩
  calc
    _ ≤ 2 * (sourceCode G input).length := source_address_capacity_le_code G input
    _ ≤ 2 * (c * (input.length + 1) ^ d) := Nat.mul_le_mul_left 2 (hc input)
    _ = _ := by ring

#print axioms edgeBits_eq_paddedEdgeBits
#print axioms edgeBits_minimal
#print axioms capacity_le_twice_succ
#print axioms source_address_capacity_le_code
#print axioms source_address_capacity_poly

end CurrentAdditive.V39SourceAddressResource
