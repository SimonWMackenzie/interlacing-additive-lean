import CurrentAdditive.GenericRecursiveCodeSize
import Paper2.CodeGeneratorExponentPublic

/-! Actual fixed-controller clock for arbitrary recursive base syntax.
The premise measures the entire two-code base syntax, including rational
weight data compiled into branches. -/

namespace Paper2.GenericRecursiveGeneratorClock

set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSource
open Paper2.GeneratorSerialization
open Paper2.CodeRecursiveLoop Paper2.CodeGeneratorClockSum
open Paper2.GenericRecursiveCodeSize

def cap (L k : ℕ) : ℕ := 2 ^ (9 * (k + 1) * (L + 10))

theorem cap_mono {L j k : ℕ} (hjk : j ≤ k) : cap L j ≤ cap L k := by
  apply pow_le_pow_right₀ (by omega)
  dsimp [cap]
  nlinarith

theorem scalar_roundPoly_le (n s q₁ q₂ w Q M A : ℕ)
    (hn : n ≤ M) (hs : s ≤ M) (hq₁ : q₁ ≤ M)
    (hq₂ : q₂ ≤ M) (hw : w ≤ M) (hQ : Q ≤ M) :
    Paper2.CodeGeneratorStepGrowth.roundPoly n s q₁ q₂ w Q A A ≤
      Paper2.CodeGeneratorStepGrowth.roundPoly M M M M M M A A := by
  dsimp [Paper2.CodeGeneratorStepGrowth.roundPoly,
    Paper2.CodeRecursiveStepClock.polynomialClock,
    Paper2.CodeRecursiveStepClock.graphCap,
    Paper2.CodeRecursiveStepClock.taggedCap,
    Paper2.TaggedCompiler.polynomialClock]
  gcongr

theorem cap_dominates_scalar (L k : ℕ) :
    2 ^ L + 1 ≤ cap L k := by
  have h1 : 1 ≤ 2 ^ L := Nat.one_le_pow _ _ (by omega)
  have hexp : L + 1 ≤ 9 * (k + 1) * (L + 10) := by nlinarith
  have hpow : 2 ^ (L + 1) ≤ cap L k := by
    unfold cap
    exact pow_le_pow_right₀ (by omega) hexp
  have hsucc : 2 ^ L + 1 ≤ 2 ^ (L + 1) := by
    rw [pow_succ]
    omega
  exact hsucc.trans hpow

theorem generator_clock_le_coeff
    (n s q₁ q₂ w Q L k : ℕ) (row₀ col₀ : Code)
    (hsmall : 3 ≤ s)
    (hn : n ≤ 2 ^ L) (hs : s ≤ 2 ^ L)
    (hq₁ : q₁ ≤ 2 ^ L) (hq₂ : q₂ ≤ 2 ^ L)
    (hw : w ≤ 2 ^ L) (hQ : Q ≤ 2 ^ L)
    (hbase : baseSize row₀ col₀ ≤ 2 ^ L) :
    CodeRecursiveLoop.totalClock n s q₁ q₂ w Q row₀ col₀ k ≤
      Paper2.CodeGeneratorExponentPublic.coeff * (k + 1) * (cap L k) ^ 6 := by
  let M := 2 ^ L
  let A := cap L k
  have hcode : ∀ j < k,
      let pair := recursiveCodes n s q₁ q₂ w Q row₀ col₀ j
      codeSize pair.1 + codeSize pair.2 + 1 ≤ A := by
    intro j hj
    exact (recursive_size_le_exp n s q₁ q₂ w Q L row₀ col₀ j
      hn hs hq₁ hq₂ hw hQ hbase).trans
      (cap_mono (Nat.le_of_lt hj))
  have hclock := totalClock_le_code_cap n s q₁ q₂ w Q
    row₀ col₀ k A hsmall hcode
  have hmono := scalar_roundPoly_le n s q₁ q₂ w Q M A
    hn hs hq₁ hq₂ hw hQ
  have hmul := Nat.mul_le_mul_left k
    (Nat.add_le_add_right hmono 1)
  have hmajor := Paper2.CodeGeneratorExponentPublic.publicClock_scalar_bound
    M A k (cap_dominates_scalar L k)
  calc
    CodeRecursiveLoop.totalClock n s q₁ q₂ w Q row₀ col₀ k
      ≤ 1 + k *
          (Paper2.CodeGeneratorStepGrowth.roundPoly n s q₁ q₂ w Q A A + 1) :=
        hclock
    _ ≤ 6 * M + 19 + k *
          (Paper2.CodeGeneratorStepGrowth.roundPoly M M M M M M A A + 1) := by
        omega
    _ ≤ Paper2.CodeGeneratorExponentPublic.coeff * (k + 1) * A ^ 6 := hmajor

/-- An explicit singly exponential clock for the generic physical code
builder. The exponent includes the full base-code byte budget. -/
theorem generator_clock_le_exp
    (n s q₁ q₂ w Q L k : ℕ) (row₀ col₀ : Code)
    (hsmall : 3 ≤ s)
    (hn : n ≤ 2 ^ L) (hs : s ≤ 2 ^ L)
    (hq₁ : q₁ ≤ 2 ^ L) (hq₂ : q₂ ≤ 2 ^ L)
    (hw : w ≤ 2 ^ L) (hQ : Q ≤ 2 ^ L)
    (hbase : baseSize row₀ col₀ ≤ 2 ^ L) :
    CodeRecursiveLoop.totalClock n s q₁ q₂ w Q row₀ col₀ k ≤
      2 ^ (Paper2.CodeGeneratorExponentPublic.coeff + (k + 1) +
        (9 * (k + 1) * (L + 10)) * 6) := by
  let C := Paper2.CodeGeneratorExponentPublic.coeff
  let E := 9 * (k + 1) * (L + 10)
  have hC : C ≤ 2 ^ C :=
    Paper2.CodeGeneratorExponentPublic.nat_le_two_pow C
  have hk : k + 1 ≤ 2 ^ (k + 1) :=
    Paper2.CodeGeneratorExponentPublic.nat_le_two_pow (k + 1)
  have hclock := generator_clock_le_coeff n s q₁ q₂ w Q L k
    row₀ col₀ hsmall hn hs hq₁ hq₂ hw hQ hbase
  calc
    CodeRecursiveLoop.totalClock n s q₁ q₂ w Q row₀ col₀ k
      ≤ C * (k + 1) * (cap L k) ^ 6 := hclock
    _ ≤ 2 ^ C * 2 ^ (k + 1) * (cap L k) ^ 6 := by
        gcongr
    _ = 2 ^ (C + (k + 1) + E * 6) := by
        simp only [cap, E, ← pow_mul, ← pow_add]
    _ = 2 ^ (Paper2.CodeGeneratorExponentPublic.coeff + (k + 1) +
          (9 * (k + 1) * (L + 10)) * 6) := rfl

theorem generator_run_exp
    (n s q₁ q₂ w Q L k : ℕ) (row₀ col₀ : Code)
    (hsmall : 3 ≤ s)
    (hn : n ≤ 2 ^ L) (hs : s ≤ 2 ^ L)
    (hq₁ : q₁ ≤ 2 ^ L) (hq₂ : q₂ ≤ 2 ^ L)
    (hw : w ≤ 2 ^ L) (hQ : Q ≤ 2 ^ L)
    (hbase : baseSize row₀ col₀ ≤ 2 ^ L) :
    ∃ t ≤ 2 ^ (Paper2.CodeGeneratorExponentPublic.coeff + (k + 1) +
        (9 * (k + 1) * (L + 10)) * 6),
      ((advance CodeRecursiveLoop.program)^[t])
        (CodeRecursiveLoop.ready n s q₁ q₂ w Q row₀ col₀
          (List.replicate k true)) =
        CodeRecursiveLoop.finished n s q₁ q₂ w Q
          (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).1
          (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).2 := by
  obtain ⟨t, ht, hrun⟩ := CodeRecursiveLoop.run_k
    n s q₁ q₂ w Q row₀ col₀ k hsmall
  exact ⟨t, ht.trans (generator_clock_le_exp n s q₁ q₂ w Q L k
    row₀ col₀ hsmall hn hs hq₁ hq₂ hw hQ hbase), hrun⟩

#print axioms cap_mono
#print axioms generator_clock_le_coeff
#print axioms generator_clock_le_exp
#print axioms generator_run_exp

end Paper2.GenericRecursiveGeneratorClock
