import CurrentAdditive.V39DeadCodeExponent
import CurrentAdditive.V39CurrentCodeConstructor

/-! Uniform actual construction clock and stored-code size, including the
implementation dead arm. E bounds all seven widths; F bounds sample count. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V39CurrentCodeConstructor

open Paper2
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open V39DeadTaggedCompiler

theorem transfer_assembly_le (mX mY A : Nat) (row col : Code)
    (hA : 1 ≤ A) (hx : mX ≤ A) (hy : mY ≤ A)
    (hr : codeSize row ≤ A) (hc : codeSize col ≤ A) :
    CodeGeneratorSampleTransfer.transferClock mX mY row col +
      64*(mX+mY+codeSize row+codeSize col+2)^2 + 2 ≤ 4096*A^2 := by
  have ht : CodeGeneratorSampleTransfer.transferClock mX mY row col ≤
      8*A+13 := by
    simp only [CodeGeneratorSampleTransfer.transferClock, encodeCode_length]
    omega
  have hs : mX+mY+codeSize row+codeSize col+2 ≤ 6*A := by omega
  have hs2 := Nat.pow_le_pow_left hs 2
  have ha2 : A ≤ A^2 := by nlinarith
  nlinarith only [ht, hs2, ha2, hA]


theorem deadSampleCode_size (n p q₁ q₂ s w Q k m : Nat) :
    codeSize (deadSampleCode n p q₁ q₂ s w Q k m) =
      m*(codeSize (deadCodes n p q₁ q₂ s w Q k).1+
        codeSize (deadCodes n p q₁ q₂ s w Q k).2+6)+11 := by
  simp only [deadSampleCode, codeSize, GeneratorSize.copies_size]
  ring

theorem sampleCode_size_le_exp (n p q₁ q₂ s w Q E F k m : Nat)
    (hn : n ≤ 2^E) (hp : p ≤ 2^E) (hq₁ : q₁ ≤ 2^E) (hq₂ : q₂ ≤ 2^E)
    (hs : s ≤ 2^E) (hw : w ≤ 2^E) (hQ : Q ≤ 2^E) (hm : m ≤ 2^F) :
    codeSize (deadSampleCode n p q₁ q₂ s w Q k m) ≤
      2^(F+9*(k+1)*(E+10)+5) := by
  let D := 9*(k+1)*(E+10)
  have hsize := dead_total_le_exp n p q₁ q₂ s w Q E k hn hp hq₁ hq₂ hs hw hQ
  have hD : 1 ≤ 2^D := Nat.one_le_two_pow
  have hF : 1 ≤ 2^F := Nat.one_le_two_pow
  rw [deadSampleCode_size]
  have hsum : codeSize (deadCodes n p q₁ q₂ s w Q k).1+
      codeSize (deadCodes n p q₁ q₂ s w Q k).2+6 ≤ 6*2^D := by
    change codeSize (deadCodes n p q₁ q₂ s w Q k).1+
      codeSize (deadCodes n p q₁ q₂ s w Q k).2+1 ≤ 2^D at hsize
    omega
  have hmul := Nat.mul_le_mul hm hsum
  have hprod : 1 ≤ 2^F*2^D := by nlinarith
  calc
    m*(codeSize (deadCodes n p q₁ q₂ s w Q k).1+
      codeSize (deadCodes n p q₁ q₂ s w Q k).2+6)+11
      ≤ 32*(2^F*2^D) := by nlinarith
    _ = 2^(F+D+5) := by rw [pow_add,pow_add]; norm_num; ring
    _ = _ := rfl

theorem sampleClock_le_two_pow (n p q₁ q₂ s w Q E F k m : Nat)
    (hs : 3 ≤ s)
    (hn : n ≤ 2^E) (hp : p ≤ 2^E) (hq₁ : q₁ ≤ 2^E) (hq₂ : q₂ ≤ 2^E)
    (hsE : s ≤ 2^E) (hw : w ≤ 2^E) (hQ : Q ≤ 2^E) (hm : m ≤ 2^F) :
    V39DeadSampleJoin.clock n p s q₁ q₂ w Q k m m ≤
      2^((V39DeadCodeExponent.exponentConstant+18)*(k+1)*(E+10)+2*F+13) := by
  let T := (k+1)*(E+10)
  let D := 9*T
  let A := 2^(D+F)
  let pair := deadCodes n p q₁ q₂ s w Q k
  have hsize := dead_total_le_exp n p q₁ q₂ s w Q E k hn hp hq₁ hq₂ hsE hw hQ
  have hDA : 2^D ≤ A := pow_le_pow_right₀ (by decide) (by omega)
  have hFA : 2^F ≤ A := pow_le_pow_right₀ (by decide) (by omega)
  have hsize' : codeSize pair.1+codeSize pair.2+1 ≤ 2^D := by
    simpa only [pair,D,T,Nat.mul_assoc] using hsize
  have hr : codeSize pair.1 ≤ A := by omega
  have hc : codeSize pair.2 ≤ A := by omega
  have hover := transfer_assembly_le m m A pair.1 pair.2
    (Nat.one_le_two_pow) (hm.trans hFA) (hm.trans hFA) hr hc
  have hraw := V39DeadSampleResult.clock_output_sensitive n p s q₁ q₂ w Q k m m
  rw [V39CurrentCodeConstructor.seedCodes_eq] at hraw
  have hcompiler := V39DeadCodeExponent.compilerClock_le_two_pow
    n p q₁ q₂ s w Q E k hs hn hp hq₁ hq₂ hsE hw hQ
  have hoverexp : 4096*A^2 = 2^(12+18*T+2*F) := by
    dsimp [A,D]
    rw [← pow_mul]
    change 2^12*2^((9*T+F)*2) = 2^(12+18*T+2*F)
    rw [← pow_add]
    congr 1
    ring
  have hsum : V39DeadSampleJoin.clock n p s q₁ q₂ w Q k m m ≤
      2^(V39DeadCodeExponent.exponentConstant*T)+2^(12+18*T+2*F) := by
    rw [← hoverexp]
    have hcompiler' : V39DeadCodeComplete.clock n p s q₁ q₂ w Q k ≤
        2^(V39DeadCodeExponent.exponentConstant*T) := by
      simpa only [T,Nat.mul_assoc] using hcompiler
    dsimp only at hraw
    dsimp only [pair] at hover
    omega
  let X := V39DeadCodeExponent.exponentConstant*T
  let Y := 12+18*T+2*F
  have hx : 2^X ≤ 2^(X+Y) := pow_le_pow_right₀ (by decide) (by omega)
  have hy : 2^Y ≤ 2^(X+Y) := pow_le_pow_right₀ (by decide) (by omega)
  calc
    V39DeadSampleJoin.clock n p s q₁ q₂ w Q k m m ≤ 2^X+2^Y := hsum
    _ ≤ 2^(X+Y)+2^(X+Y) := Nat.add_le_add hx hy
    _ = 2^(X+Y+1) := by rw [pow_succ]; omega
    _ = _ := by dsimp [X,Y,T]; congr 1; ring

#print axioms sampleCode_size_le_exp
#print axioms sampleClock_le_two_pow

end CurrentAdditive.V39CurrentCodeConstructor
