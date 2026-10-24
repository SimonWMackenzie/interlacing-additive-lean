import EthInapproximability.CurrentPaper.SourceClausePrefixLoopPrimitiveBounds

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixLoopPolynomial

open Turing BitMachineEncoding PrefixLoopCost PrefixLoopPolyProbe
open scoped Classical

def inputMass (n : ℕ) (saved output count : List Bool) : ℕ :=
  n + saved.length + output.length + count.length + 1

def scale (q : ℕ) : ℕ := SourceBooleanEncoding.width 2 q + 10
def byteCoefficient (q : ℕ) : ℕ := 8 * (6 * scale q + 6)
noncomputable def primitiveCoefficient (q : ℕ) : ℕ :=
  10000 * (UnaryBinaryEncoding.coefficient + 1) * (scale q) ^ 4
def bankCoefficient (q : ℕ) : ℕ := 100 * (byteCoefficient q + 1)
noncomputable def phaseCoefficient (q : ℕ) : ℕ :=
  primitiveCoefficient q +
    workCount * (bankCoefficient q + stepBound q * primitiveCoefficient q) +
      workCount + 3
noncomputable def callbackCoefficient (q : ℕ) : ℕ :=
  4 * phaseCoefficient q + 3

theorem wordBound_le (n q : ℕ) (saved output count : List Bool) :
    wordBound n q ≤ byteCoefficient q *
      (inputMass n saved output count + 1) := by
  let H := inputMass n saved output count + 1
  let w := SourceBooleanEncoding.width 2 q + 1
  have hn : n ≤ H := by simp [H, inputMass]; omega
  have hH : 1 ≤ H := by omega
  have hmul := Nat.mul_le_mul_right (w + 3) hn
  have hv : variableBound n q ≤ (w + 9) * H := by
    dsimp [variableBound, w]
    nlinarith
  change variableBound n q ≤ scale q * H at hv
  have h6 : 6 * variableBound n q ≤ (6 * scale q) * H := by
    simpa only [mul_assoc] using Nat.mul_le_mul_left 6 hv
  have h6H : 6 ≤ 6 * H := by omega
  change 8 * (6 * variableBound n q + 6) ≤
    8 * (6 * scale q + 6) * H
  calc
    8 * (6 * variableBound n q + 6) ≤
        8 * ((6 * scale q) * H + 6 * H) := by omega
    _ = 8 * (6 * scale q + 6) * H := by ring

theorem savedAt_le (n q k : ℕ) (saved output count : List Bool)
    (hk : k ≤ n) :
    (PrefixLoopIteration.savedAt n q saved k).length ≤
      (byteCoefficient q + 1) *
        (inputMass n saved output count + 1) ^ 2 := by
  let H := inputMass n saved output count + 1
  have hn : n ≤ H := by simp [H, inputMass]; omega
  have hkH : k ≤ H := by omega
  have hs : saved.length ≤ H := by simp [H, inputMass]; omega
  have hword := wordBound_le n q saved output count
  have hprefix := savedAt_length_le n q k saved hk
  have hmul := Nat.mul_le_mul hkH hword
  have hH : 1 ≤ H := by omega
  have hH2 : H ≤ H ^ 2 := by nlinarith
  change (PrefixLoopIteration.savedAt n q saved k).length ≤
    saved.length + k * wordBound n q at hprefix
  change wordBound n q ≤ byteCoefficient q * H at hword
  change (PrefixLoopIteration.savedAt n q saved k).length ≤
    (byteCoefficient q + 1) * H ^ 2
  nlinarith

theorem bankBound_le (n q k : ℕ) (saved output count : List Bool)
    (hk : k ≤ n) :
    bankBound n k q (PrefixLoopIteration.savedAt n q saved k)
        output (PrefixLoopIteration.countAt count k) ≤
      bankCoefficient q * (inputMass n saved output count + 1) ^ 2 := by
  let H := inputMass n saved output count + 1
  have hH : 1 ≤ H := by omega
  have hn : n ≤ H := by simp [H, inputMass]; omega
  have hkH : k ≤ H := by omega
  have ho : output.length ≤ H := by simp [H, inputMass]; omega
  have hc : count.length ≤ H := by simp [H, inputMass]; omega
  have hs := savedAt_le n q k saved output count hk
  have hw := wordBound_le n q saved output count
  have hcount := countAt_length count k
  have hH2 : H ≤ H ^ 2 := by nlinarith
  have hHconst : 1 ≤ H ^ 2 := by omega
  change (PrefixLoopIteration.savedAt n q saved k).length ≤
    (byteCoefficient q + 1) * H ^ 2 at hs
  change wordBound n q ≤ byteCoefficient q * H at hw
  dsimp only [bankBound, bankCoefficient]
  rw [hcount]
  change _ ≤ 100 * (byteCoefficient q + 1) * H ^ 2
  nlinarith [Nat.zero_le (byteCoefficient q * H ^ 2)]

theorem preBound_le (n q k : ℕ) (saved output count : List Bool)
    (hk : k ≤ n) :
    preBound n k q ≤ primitiveCoefficient q *
      (inputMass n saved output count + 1) ^ 4 := by
  let H := inputMass n saved output count + 1
  let w := SourceBooleanEncoding.width 2 q + 1
  have hn : n ≤ H := by simp [H, inputMass]; omega
  have hkH : k ≤ H := by omega
  have hH : 1 ≤ H := by omega
  have hbase : n + k + w + 4 ≤ scale q * H := by
    dsimp [scale, w]
    nlinarith
  have hp := pow_le_pow_left₀ (by omega : 0 ≤ n + k + w + 4) hbase 4
  have hm := Nat.mul_le_mul_left
    (10000 * (UnaryBinaryEncoding.coefficient + 1)) hp
  change 10000 * (UnaryBinaryEncoding.coefficient + 1) *
      (n + k + w + 4) ^ 4 ≤
    10000 * (UnaryBinaryEncoding.coefficient + 1) *
      (scale q) ^ 4 * H ^ 4
  nlinarith [hm]

theorem phaseBound_le (n q k : ℕ) (saved output count : List Bool)
    (hk : k ≤ n) :
    phaseBound n k q (PrefixLoopIteration.savedAt n q saved k)
        output (PrefixLoopIteration.countAt count k) ≤
      phaseCoefficient q * (inputMass n saved output count + 1) ^ 4 := by
  let H := inputMass n saved output count + 1
  have hH : 1 ≤ H := by omega
  have hp := preBound_le n q k saved output count hk
  have hb := bankBound_le n q k saved output count hk
  change preBound n k q ≤ primitiveCoefficient q * H ^ 4 at hp
  change bankBound n k q (PrefixLoopIteration.savedAt n q saved k)
    output (PrefixLoopIteration.countAt count k) ≤
    bankCoefficient q * H ^ 2 at hb
  have h24 : H ^ 2 ≤ H ^ 4 := by
    have h2 : H ≤ H ^ 2 := by nlinarith
    have h := Nat.mul_le_mul h2 h2
    nlinarith [h]
  have hbank : bankBound n k q (PrefixLoopIteration.savedAt n q saved k)
      output (PrefixLoopIteration.countAt count k) ≤
      bankCoefficient q * H ^ 4 := by
    have h := Nat.mul_le_mul_left (bankCoefficient q) h24
    exact hb.trans h
  have hstep := Nat.mul_le_mul_left (stepBound q) hp
  have hstep' : stepBound q * preBound n k q ≤
      (stepBound q * primitiveCoefficient q) * H ^ 4 := by
    simpa only [mul_assoc] using hstep
  have hsum : bankBound n k q (PrefixLoopIteration.savedAt n q saved k)
      output (PrefixLoopIteration.countAt count k) +
      stepBound q * preBound n k q ≤
      (bankCoefficient q + stepBound q * primitiveCoefficient q) * H ^ 4 := by
    calc
      _ ≤ bankCoefficient q * H ^ 4 +
          (stepBound q * primitiveCoefficient q) * H ^ 4 :=
            Nat.add_le_add hbank hstep'
      _ = _ := by ring
  have hmass := Nat.mul_le_mul_left workCount hsum
  have h1 : 1 ≤ H ^ 4 := by
    simpa using (pow_le_pow_left₀ (by omega : 0 ≤ (1 : ℕ)) hH 4)
  have hconst : workCount + 3 ≤ (workCount + 3) * H ^ 4 := by
    simpa only [mul_one] using Nat.mul_le_mul_left (workCount + 3) h1
  change preBound n k q +
      workCount * (bankBound n k q
        (PrefixLoopIteration.savedAt n q saved k) output
        (PrefixLoopIteration.countAt count k) +
          stepBound q * preBound n k q) + workCount + 3 ≤
      phaseCoefficient q * H ^ 4
  calc
    _ ≤ primitiveCoefficient q * H ^ 4 +
        workCount * ((bankCoefficient q +
          stepBound q * primitiveCoefficient q) * H ^ 4) +
          (workCount + 3) * H ^ 4 := by omega
    _ = phaseCoefficient q * H ^ 4 := by
      unfold phaseCoefficient
      ring

theorem callback_cost_le (n q k : ℕ) (saved output count : List Bool)
    (hk : k < n) :
    PrefixFullCallback.cost (q := q) (⟨k, hk⟩ : Fin n)
      (PrefixLoopIteration.savedAt n q saved k) output
      (PrefixLoopIteration.countAt count k) ≤
      callbackCoefficient q *
        (inputMass n saved output count + 1) ^ 4 := by
  have h := callback_cost_le_phase (q := q) (⟨k, hk⟩ : Fin n)
    (PrefixLoopIteration.savedAt n q saved k) output
    (PrefixLoopIteration.countAt count k)
  have hp := phaseBound_le n q k saved output count hk.le
  have hpow : 1 ≤ (inputMass n saved output count + 1) ^ 4 := by
    have hh : 1 ≤ inputMass n saved output count + 1 := by omega
    simpa using (pow_le_pow_left₀ (by omega : 0 ≤ (1 : ℕ)) hh 4)
  dsimp only [callbackCoefficient]
  nlinarith

/-- A literal degree-five polynomial clock for fixed `q`. The coefficient
is assembled from finite program syntax, physical push growth, and the
frozen callback's primitive arithmetic; it is independent of `n` and of
the input words. -/
noncomputable def polynomialClock (n q : ℕ)
    (saved output count : List Bool) : ℕ :=
  4 * n + 3 + n * callbackCoefficient q *
    (inputMass n saved output count + 1) ^ 4

theorem run_polynomial (n q : ℕ) (saved output count : List Bool) :
    ∃ t ≤ polynomialClock n q saved output count,
      ((advance (PrefixLoopCallback.program q))^[t])
        (⟨some (.inr .copyScan), (PrefixLoopCallback.initial, none),
          PrefixLoopMachine.blank n 0 saved output count []⟩ :
          PrefixLoopMachine.Config _ _) =
        ⟨none, (PrefixLoopCallback.initial, none),
          PrefixLoopMachine.blank n n
            ((PrefixLoopIteration.prefixFields n q n).reverse ++ saved)
            output (List.replicate (8 * n) true ++ count) []⟩ := by
  let B := callbackCoefficient q * (inputMass n saved output count + 1) ^ 4
  have hcost : ∀ j, 0 ≤ j → j < n →
      PrefixLoopIteration.callCost n q saved output count j ≤ B := by
    intro j _ hj
    simp only [PrefixLoopIteration.callCost, dif_pos hj]
    exact callback_cost_le n q j saved output count hj
  have htail := PrefixLoopIteration.tailCost_le_uniform n q 0 n B
    saved output count (by omega) hcost
  obtain ⟨t, ht, hr⟩ := PrefixLoopIteration.run n q saved output count
  refine ⟨t, ?_, hr⟩
  unfold polynomialClock
  dsimp only [B] at htail
  rw [Nat.mul_add] at htail
  rw [← mul_assoc] at htail
  omega

#print axioms run_polynomial
#print axioms callback_cost_le
#print axioms PrefixLoopIteration.prefixFields_production

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixLoopPolynomial
