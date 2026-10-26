import Paper2.SCFetch
import Paper2.SCCaps

/-! Lane a-success-clock-owner-2: power-of-a-scale arithmetic and the admitted
fetch clocks (`FetchIndexed.colBound`, `FetchIndexed.rowBound`) in the form
"at most `X^4`" when every code size and index is at most `X` and every word
list is at most `X^2` long. Pure arithmetic. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.SuccessClock2

open Paper2.GeneratorCode Paper2.GeneratorSerialization

theorem xstep {X : ℕ} (hX : 1048576 ≤ X) (i : ℕ) : 1048576 * X ^ i ≤ X ^ (i + 1) := by
  rw [pow_succ]
  calc 1048576 * X ^ i = X ^ i * 1048576 := by ring
    _ ≤ X ^ i * X := Nat.mul_le_mul_left _ hX

theorem xone {X : ℕ} (hX : 1048576 ≤ X) (i : ℕ) : 1 ≤ X ^ i :=
  Nat.one_le_pow _ _ (by omega)

theorem xmono {X : ℕ} (hX : 1048576 ≤ X) {i j : ℕ} (h : i ≤ j) : X ^ i ≤ X ^ j :=
  Nat.pow_le_pow_right (by omega) h

theorem xmul {X a b i j : ℕ} (ha : a ≤ X ^ i) (hb : b ≤ X ^ j) : a * b ≤ X ^ (i + j) := by
  rw [pow_add]; exact Nat.mul_le_mul ha hb

theorem x1 {X : ℕ} (hX : 1048576 ≤ X) : 1048576 * X ≤ X ^ 2 := by
  have := xstep hX 1; simpa using this

theorem colBound_X (col : Code) (cs : List (List Bool)) (y : ℕ) (O : List Bool) {X : ℕ}
    (hX : 1048576 ≤ X) (hc : codeSize col ≤ X) (hF : cs.flatten.length ≤ X ^ 2)
    (hl : cs.length ≤ X) (hy : y ≤ X) (hO : O.length ≤ X ^ 2) :
    FetchIndexed.colBound col cs y O ≤ X ^ 4 := by
  have h := Paper2.SuccessClock.colBound_le col cs y O
  have h2 := x1 hX
  have a1 : codeSize col + 1 ≤ 2 * X := by omega
  have a2 : cs.flatten.length + cs.length + y + O.length + 1 ≤ 5 * X ^ 2 := by omega
  have a3 := Nat.mul_le_mul a1 a2
  have a4 : 2 * X * (5 * X ^ 2) = 10 * X ^ 3 := by ring
  have a5 : 1048576 * X ^ 3 ≤ X ^ 4 := xstep hX 3
  omega

theorem rowBound_X (col row : Code) (cs rs : List (List Bool)) (x : ℕ) (O : List Bool) {X : ℕ}
    (hX : 1048576 ≤ X) (hc : codeSize col ≤ X) (hr : codeSize row ≤ X)
    (hF : cs.flatten.length ≤ X ^ 2) (hG : rs.flatten.length ≤ X ^ 2)
    (hl : cs.length ≤ X) (hm : rs.length ≤ X) (hx : x ≤ X) (hO : O.length ≤ X ^ 2) :
    FetchIndexed.rowBound col row cs rs x O ≤ X ^ 4 := by
  have h := Paper2.SuccessClock.rowBound_le col row cs rs x O
  have h2 := x1 hX
  have a1 : codeSize col + codeSize row + 1 ≤ 3 * X := by omega
  have a2 : cs.flatten.length + rs.flatten.length + cs.length + rs.length + x + O.length + 1 ≤
      7 * X ^ 2 := by omega
  have a3 := Nat.mul_le_mul a1 a2
  have a4 : 3 * X * (7 * X ^ 2) = 21 * X ^ 3 := by ring
  have a5 : 1048576 * X ^ 3 ≤ X ^ 4 := xstep hX 3
  omega

/-- A list of `N ≤ X` words of a codec with `maxLen ≤ X`: at most `X^2` bits, `N ≤ X` words. -/
theorem ofFn_X {α : Type} (ca : RecursiveLabelCodecScratch.PrefixCodec α) (N : ℕ) (f : Fin N → α)
    {X : ℕ} (hN : N ≤ X) (hM : ca.maxLen ≤ X) :
    (List.ofFn (fun j => ca.encode (f j))).flatten.length ≤ X ^ 2 ∧
      (List.ofFn (fun j => ca.encode (f j))).length ≤ X := by
  refine ⟨?_, by simpa using hN⟩
  have h := Paper2.SuccessClock.ofFn_flatten_le ca N f
  have := Nat.mul_le_mul hN hM
  rw [sq]; omega

end Paper2.SuccessClock2

#print axioms Paper2.SuccessClock2.colBound_X
#print axioms Paper2.SuccessClock2.rowBound_X
#print axioms Paper2.SuccessClock2.ofFn_X
