import CurrentAdditive.V39DeadCodeStepGrowth
import CurrentAdditive.V39DeadCodeComplete
import CurrentAdditive.V39DeadCodeSize

/-! Sum the *actual* fixed-controller round clocks, with no runtime
recurrence hidden in the induction. The uniform per-round cap is a separate
arithmetic premise, later discharged from the scheduled source-size cap. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V39DeadCodeClockSum

open Paper2

open Paper2.GeneratorCode Paper2.GeneratorSource
open Paper2.GeneratorSerialization
open CurrentAdditive.V39DeadCodeLoop CurrentAdditive.V39DeadCodeRound
open Paper2.GeneratorSize

theorem roundPoly_mono (n s q₁ q₂ w Q r r' c c' : Nat)
    (hr : r ≤ r') (hc : c ≤ c') :
    V39DeadCodeStepGrowth.roundPoly n s q₁ q₂ w Q r c ≤
      V39DeadCodeStepGrowth.roundPoly n s q₁ q₂ w Q r' c' := by
  dsimp [V39DeadCodeStepGrowth.roundPoly,
    V39DeadCodeStepClock.polynomialClock,
    V39DeadCodeStepClock.graphCap,
    V39DeadCodeStepClock.taggedCap,
    TaggedCompiler.polynomialClock]
  gcongr

theorem totalClock_le_uniform (n s q₁ q₂ w Q : Nat)
    (row col : Code) (k P : Nat)
    (hround : ∀ j < k,
      let pair := CurrentAdditive.V39DeadGenericCode.recursiveCodes n s q₁ q₂ w Q row col j
      V39DeadCodeRound.clock n s q₁ q₂ w Q pair.1 pair.2 ≤ P) :
    totalClock n s q₁ q₂ w Q row col k ≤ 1 + k*(P+1) := by
  induction k generalizing row col with
  | zero => simp [totalClock]
  | succ k ih =>
      let row₁ := V39DeadCodeRow.rowCode q₁ q₂ s w Q col
      let col₁ := CodeRecursiveColumn.columnCode n s q₁ q₂ w Q row
      have h0 : V39DeadCodeRound.clock n s q₁ q₂ w Q row col ≤ P := by
        simpa only [CurrentAdditive.V39DeadGenericCode.recursiveCodes] using hround 0 (by omega)
      have htail : ∀ j < k,
          let pair := CurrentAdditive.V39DeadGenericCode.recursiveCodes n s q₁ q₂ w Q row₁ col₁ j
          V39DeadCodeRound.clock n s q₁ q₂ w Q pair.1 pair.2 ≤ P := by
        intro j hj
        have h := hround (j+1) (by omega)
        simpa only [row₁, col₁, V39DeadCodeLoop.recursiveCodes_shift]
          using h
      have ht := ih row₁ col₁ htail
      dsimp [totalClock]
      dsimp [row₁, col₁] at ht
      rw [Nat.succ_mul]
      omega

theorem totalClock_le_code_cap (n s q₁ q₂ w Q : Nat)
    (row col : Code) (k A : Nat) (hs : 3 ≤ s)
    (hcap : ∀ j < k,
      let pair := CurrentAdditive.V39DeadGenericCode.recursiveCodes n s q₁ q₂ w Q row col j
      codeSize pair.1 + codeSize pair.2 + 1 ≤ A) :
    totalClock n s q₁ q₂ w Q row col k ≤
      1 + k*(V39DeadCodeStepGrowth.roundPoly n s q₁ q₂ w Q A A + 1) := by
  apply totalClock_le_uniform
  intro j hj
  let pair := CurrentAdditive.V39DeadGenericCode.recursiveCodes n s q₁ q₂ w Q row col j
  have hc := hcap j hj
  have hr : codeSize pair.1 ≤ A := by dsimp [pair] at *; omega
  have hc' : codeSize pair.2 ≤ A := by dsimp [pair] at *; omega
  exact (V39DeadCodeStepGrowth.round_clock_le_poly
    n s q₁ q₂ w Q pair.1 pair.2 hs).trans
    (roundPoly_mono n s q₁ q₂ w Q
      (codeSize pair.1) A (codeSize pair.2) A hr hc')


theorem totalClock_seed_le_exp (n p q₁ q₂ s w Q E k : Nat)
    (hs : 3 ≤ s)
    (hn : n ≤ 2^E) (hp : p ≤ 2^E) (hq₁ : q₁ ≤ 2^E) (hq₂ : q₂ ≤ 2^E)
    (hsE : s ≤ 2^E) (hw : w ≤ 2^E) (hQ : Q ≤ 2^E) :
    totalClock n s q₁ q₂ w Q (copies p .bit) (.ticket p) k ≤
      1+k*(V39DeadCodeStepGrowth.roundPoly n s q₁ q₂ w Q
        (2^(9*(k+1)*(E+10))) (2^(9*(k+1)*(E+10)))+1) := by
  apply totalClock_le_code_cap n s q₁ q₂ w Q
    (copies p .bit) (.ticket p) k (2^(9*(k+1)*(E+10))) hs
  intro j hj
  rw [V39DeadGenericCode.seed_eq]
  have h := V39DeadTaggedCompiler.dead_total_le_exp n p q₁ q₂ s w Q E j
    hn hp hq₁ hq₂ hsE hw hQ
  exact h.trans (pow_le_pow_right₀ (by decide) (by gcongr))

def publicCompilerClock (E k : Nat) : Nat :=
  let M := 2^E
  let A := 2^(9*(k+1)*(E+10))
  6*M+19+k*(V39DeadCodeStepGrowth.roundPoly M M M M M M A A+1)

theorem compilerClock_le_public (n p q₁ q₂ s w Q E k : Nat)
    (hs : 3 ≤ s)
    (hn : n ≤ 2^E) (hp : p ≤ 2^E) (hq₁ : q₁ ≤ 2^E) (hq₂ : q₂ ≤ 2^E)
    (hsE : s ≤ 2^E) (hw : w ≤ 2^E) (hQ : Q ≤ 2^E) :
    V39DeadCodeComplete.clock n p s q₁ q₂ w Q k ≤ publicCompilerClock E k := by
  let M := 2^E
  let A := 2^(9*(k+1)*(E+10))
  have hloop := totalClock_seed_le_exp n p q₁ q₂ s w Q E k hs
    hn hp hq₁ hq₂ hsE hw hQ
  have hpoly : V39DeadCodeStepGrowth.roundPoly n s q₁ q₂ w Q A A ≤
      V39DeadCodeStepGrowth.roundPoly M M M M M M A A := by
    dsimp [V39DeadCodeStepGrowth.roundPoly, V39DeadCodeStepClock.polynomialClock,
      V39DeadCodeStepClock.graphCap, V39DeadCodeStepClock.taggedCap,
      TaggedCompiler.polynomialClock]
    gcongr
  have hm := Nat.mul_le_mul_left k (Nat.add_le_add_right hpoly 1)
  have hseed : CodeRecursiveSeedJoin.clock p ≤ 6*M+17 := by
    dsimp [CodeRecursiveSeedJoin.clock, CodeRecursiveSeedJoin.b₁]
    omega
  change CodeRecursiveSeedJoin.clock p +
    totalClock n s q₁ q₂ w Q (copies p .bit) (.ticket p) k+1 ≤
      6*M+19+k*(V39DeadCodeStepGrowth.roundPoly M M M M M M A A+1)
  change totalClock n s q₁ q₂ w Q (copies p .bit) (.ticket p) k ≤
    1+k*(V39DeadCodeStepGrowth.roundPoly n s q₁ q₂ w Q A A+1) at hloop
  omega

#print axioms totalClock_le_uniform
#print axioms totalClock_le_code_cap
#print axioms totalClock_seed_le_exp
#print axioms compilerClock_le_public

end CurrentAdditive.V39DeadCodeClockSum
