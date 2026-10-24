import CurrentAdditive.V39DeadRecursiveCode
import Paper2.GeneratorSize

set_option maxHeartbeats 3000000

namespace CurrentAdditive.V39DeadTaggedCompiler

open Paper2.GeneratorCode Paper2.GeneratorSource Paper2.GeneratorSerialization
open Paper2.GeneratorSize

theorem deadTagged_size (q₁ q₂ s : ℕ) (c : Code) :
    codeSize (deadTaggedCode q₁ q₂ s c) =
      803 + codeSize (rawCode q₁ q₂ s c) + codeSize (fixedTailCode q₁ q₂ s c) +
        codeSize (outerCode q₁ q₂ s c) := by
  simp [deadTaggedCode, codeSize]
  omega

theorem deadTagged_le_scale (n p₀ s q₁ q₂ w Q : ℕ) (c : Code) :
    codeSize (deadTaggedCode q₁ q₂ s c) ≤
      scale n p₀ s q₁ q₂ w Q ^ 6 * (codeSize c + 1) := by
  let T := scale n p₀ s q₁ q₂ w Q
  let X := codeSize c + 1
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  have hX : 1 ≤ X := by omega
  have hR : codeSize (rawCode q₁ q₂ s c) ≤ T ^ 5 * X := raw_le_scale _ _ _ _ _ _ _ _
  have hF : codeSize (fixedTailCode q₁ q₂ s c) ≤ T ^ 5 * X := fixedTail_le_scale _ _ _ _ _ _ _ _
  have hO : codeSize (outerCode q₁ q₂ s c) ≤ T ^ 3 * X := outer_le_scale _ _ _ _ _ _ _ _
  have hp : T ^ 3 * X ≤ T ^ 5 * X := by gcongr <;> omega
  have hO' := hO.trans hp
  have h803 : 803 ≤ T ^ 5 * X := by
    have hs : 803 ≤ T ^ 2 := by nlinarith
    have hp : T ^ 2 ≤ T ^ 5 := by gcongr <;> omega
    exact (hs.trans hp).trans (by simpa using Nat.mul_le_mul_left (T ^ 5) hX)
  have hm : 4 * (T ^ 5 * X) ≤ T ^ 6 * X := by
    calc
      _ = (4 * T ^ 5) * X := by ring
      _ ≤ (T * T ^ 5) * X := by gcongr; omega
      _ = _ := by ring
  rw [deadTagged_size]
  change _ ≤ T ^ 6 * X
  omega

theorem dead_row_step_le (n p₀ s q₁ q₂ w Q : ℕ) (c : Code) :
    codeSize (copies Q (.append (.ticket w) (deadTaggedCode q₁ q₂ s c))) ≤
      scale n p₀ s q₁ q₂ w Q ^ 8 * (codeSize c + 1) := by
  let T := scale n p₀ s q₁ q₂ w Q
  let X := codeSize c + 1
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  have hX : 1 ≤ X := by omega
  have hQ : Q ≤ T := by unfold T scale; omega
  have hw : w + 10 ≤ T := (scalar_le_scale _ _ _ _ _ _ _).2.2.2.2.2.1
  have htag : codeSize (deadTaggedCode q₁ q₂ s c) ≤ T ^ 6 * X :=
    deadTagged_le_scale _ _ _ _ _ _ _ _
  have hpow : T ^ 2 * X ≤ T ^ 7 * X := by gcongr <;> omega
  have hbase : T ^ 2 ≤ T ^ 2 * X := by simpa using Nat.mul_le_mul_left (T ^ 2) hX
  have h4 : 4 ≤ T ^ 7 * X := (by nlinarith : 4 ≤ T ^ 2).trans (hbase.trans hpow)
  have h3 : 3 * (T ^ 7 * X) ≤ T ^ 8 * X := by
    calc
      _ = (3 * T ^ 7) * X := by ring
      _ ≤ (T * T ^ 7) * X := by gcongr; omega
      _ = _ := by ring
  rw [copies_size]
  simp only [codeSize]
  rw [show 3 + (3 + (w + 1)) + codeSize (deadTaggedCode q₁ q₂ s c) + 3 =
    w + 10 + codeSize (deadTaggedCode q₁ q₂ s c) by omega]
  calc
    Q * (w + 10 + codeSize (deadTaggedCode q₁ q₂ s c)) + 4
      ≤ T * (T + T ^ 6 * X) + 4 := by gcongr <;> omega
    _ ≤ T ^ 8 * X := by nlinarith

theorem dead_col_step_le (n p₀ s q₁ q₂ w Q : ℕ) (c : Code) :
    codeSize (.append (.ticket Q) (copies w (graphRowsCode (V := Fin n) q₁ q₂ s c))) ≤
      scale n p₀ s q₁ q₂ w Q ^ 7 * (codeSize c + 1) := by
  have h := recursive_col_le_scale n p₀ s q₁ q₂ w Q c (.emit []) 0
  simpa only [Paper2.GeneratorSource.recursiveCodes] using h

theorem dead_total_step (n p₀ q₁ q₂ s w Q k : ℕ) :
    let T := scale n p₀ s q₁ q₂ w Q
    let old := deadCodes n p₀ q₁ q₂ s w Q k
    let new := deadCodes n p₀ q₁ q₂ s w Q (k + 1)
    codeSize new.1 + codeSize new.2 + 1 ≤
      T ^ 9 * (codeSize old.1 + codeSize old.2 + 1) := by
  let T := scale n p₀ s q₁ q₂ w Q
  let old := deadCodes n p₀ q₁ q₂ s w Q k
  let new := deadCodes n p₀ q₁ q₂ s w Q (k + 1)
  let Z := codeSize old.1 + codeSize old.2 + 1
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  have hZ : 1 ≤ Z := by omega
  have hr₀ : codeSize new.1 ≤ T ^ 8 * (codeSize old.2 + 1) := dead_row_step_le _ _ _ _ _ _ _ _
  have hc₀ : codeSize new.2 ≤ T ^ 7 * (codeSize old.1 + 1) := dead_col_step_le _ _ _ _ _ _ _ _
  have hr : codeSize new.1 ≤ T ^ 8 * Z := hr₀.trans (Nat.mul_le_mul_left _ (by dsimp [Z]; omega))
  have hc : codeSize new.2 ≤ T ^ 8 * Z := by
    apply hc₀.trans
    calc
      _ ≤ T ^ 7 * Z := Nat.mul_le_mul_left _ (by dsimp [Z]; omega)
      _ ≤ T ^ 8 * Z := by gcongr <;> omega
  have hone : 1 ≤ T ^ 8 * Z := by
    have ht : 1 ≤ T ^ 8 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hm : 3 * (T ^ 8 * Z) ≤ T ^ 9 * Z := by
    calc
      _ = (3 * T ^ 8) * Z := by ring
      _ ≤ (T * T ^ 8) * Z := by gcongr; omega
      _ = _ := by ring
  change codeSize new.1 + codeSize new.2 + 1 ≤ T ^ 9 * Z
  omega

theorem dead_total_le_scale (n p₀ q₁ q₂ s w Q k : ℕ) :
    let pair := deadCodes n p₀ q₁ q₂ s w Q k
    codeSize pair.1 + codeSize pair.2 + 1 ≤
      scale n p₀ s q₁ q₂ w Q ^ (9 * (k + 1)) := by
  let T := scale n p₀ s q₁ q₂ w Q
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  induction k with
  | zero =>
    have hp : p₀ ≤ T := (scalar_le_scale _ _ _ _ _ _ _).2.1
    have hbase : 7 * p₀ + 9 ≤ T ^ 2 := by nlinarith
    have hpow : T ^ 2 ≤ T ^ 9 := by gcongr <;> omega
    change codeSize (copies p₀ .bit) + codeSize (.ticket p₀) + 1 ≤ T ^ 9
    rw [copies_size]
    simp only [codeSize]
    omega
  | succ k ih =>
    have hs := dead_total_step n p₀ q₁ q₂ s w Q k
    apply hs.trans
    calc
      _ ≤ T ^ 9 * T ^ (9 * (k + 1)) := Nat.mul_le_mul_left _ ih
      _ = T ^ (9 * (k + 1 + 1)) := by rw [← pow_add]; congr 1; omega

theorem dead_total_le_exp (n p₀ q₁ q₂ s w Q E k : ℕ)
    (hn : n ≤ 2 ^ E) (hp₀ : p₀ ≤ 2 ^ E) (hq₁ : q₁ ≤ 2 ^ E) (hq₂ : q₂ ≤ 2 ^ E)
    (hs : s ≤ 2 ^ E) (hw : w ≤ 2 ^ E) (hQ : Q ≤ 2 ^ E) :
    let pair := deadCodes n p₀ q₁ q₂ s w Q k
    codeSize pair.1 + codeSize pair.2 + 1 ≤ 2 ^ (9 * (k + 1) * (E + 10)) := by
  let T := scale n p₀ s q₁ q₂ w Q
  have h1 : 1 ≤ 2 ^ E := Nat.one_le_pow _ _ (by omega)
  have hT : T ≤ 2 ^ (E + 10) := by
    have hsmall : T ≤ 7 * 2 ^ E + 513 := by dsimp [T, scale]; omega
    rw [pow_add]
    norm_num
    omega
  apply (dead_total_le_scale n p₀ q₁ q₂ s w Q k).trans
  calc
    _ ≤ (2 ^ (E + 10)) ^ (9 * (k + 1)) := Nat.pow_le_pow_left hT _
    _ = _ := by rw [← pow_mul, Nat.mul_comm (E + 10) (9 * (k + 1))]

#print axioms dead_total_le_scale
#print axioms dead_total_le_exp

end CurrentAdditive.V39DeadTaggedCompiler
