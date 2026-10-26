import CurrentAdditive.V39PhysicalShapeSample
import CurrentAdditive.V39PhysicalFullSample

set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V39PhysicalShapeSample
noncomputable section

open Paper2 Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
open V38Schedule V39PublicSchedule V39FullSampleResources

/- Only arithmetic data are sealed here: the value and its identity.
No execution, correctness, or resource proposition is stored in this datum. -/
private noncomputable opaque coefficientDatum :
    {C : ℕ // C=CodeGeneratorExponentPublic.coeff} :=
  ⟨CodeGeneratorExponentPublic.coeff,rfl⟩

def shapeExponent : ℕ := coefficientDatum.val+109
attribute [local irreducible] shapeExponent V39PhysicalSample.fullPhysicalExponent
  CodeGeneratorExponentPublic.coeff CodeGeneratorExponent.coefficient
  CodeGeneratorReentryBound.factor CodeGeneratorStepGrowth.stepPush

theorem coefficient_exponential_bound (C E k F : ℕ)
    (hF : F ≤ C*(k+1)*((2^E+1)^(18*(k+1)))^6) :
    F ≤ 2^((C+109)*(k+1)*(E+1)) := by
  let T := (k+1)*(E+1)
  let A := (2^E+1)^(18*(k+1))
  have hp1 : 2^E+1 ≤ 2^(E+1) := by
    rw [pow_succ]
    have ho : 1 ≤ 2^E := Nat.one_le_two_pow
    omega
  have hA : A ≤ 2^(18*T) := by
    calc
      A ≤ (2^(E+1))^(18*(k+1)) := Nat.pow_le_pow_left hp1 _
      _ = 2^(18*T) := by rw [← pow_mul]; dsimp only [T]; congr 1; ring
  have hA6 : A^6 ≤ 2^(108*T) := by
    calc
      A^6 ≤ (2^(18*T))^6 := Nat.pow_le_pow_left hA 6
      _ = 2^(108*T) := by rw [← pow_mul]; congr 1; ring
  have hT : 1 ≤ T := by dsimp only [T]; nlinarith
  have hkT : k+1 ≤ T := by dsimp only [T]; nlinarith
  have hk : k+1 ≤ 2^T := (Nat.lt_two_pow_self.le).trans
    (Nat.pow_le_pow_right (by decide) hkT)
  have hc : C ≤ 2^C := Nat.lt_two_pow_self.le
  calc
    F ≤ C*(k+1)*A^6 := hF
    _ ≤ 2^C*2^T*2^(108*T) := by gcongr
    _ = 2^(C+T+108*T) := by rw [pow_add,pow_add]
    _ ≤ 2^((C+109)*T) := by
      apply Nat.pow_le_pow_right (by decide)
      have hm := Nat.mul_le_mul_left C hT
      nlinarith
    _ = _ := by dsimp only [T]; congr 1; ring

theorem combine_exponential_clocks (a b c T x y z : ℕ) (hT : 1 ≤ T)
    (hx : x ≤ 2^(a*T)) (hy : y ≤ 2^(b*T)) (hz : z ≤ 2^(c*T)) :
    x+y+z+2 ≤ 2^((a+b+(c+4))*T) := by
  let D := a+b+c
  have hx' := hx.trans (Nat.pow_le_pow_right (show 0<(2:ℕ) by decide)
    (Nat.mul_le_mul_right T (show a≤D by dsimp only [D]; omega)))
  have hy' := hy.trans (Nat.pow_le_pow_right (show 0<(2:ℕ) by decide)
    (Nat.mul_le_mul_right T (show b≤D by dsimp only [D]; omega)))
  have hz' := hz.trans (Nat.pow_le_pow_right (show 0<(2:ℕ) by decide)
    (Nat.mul_le_mul_right T (show c≤D by dsimp only [D]; omega)))
  have hone : 1 ≤ 2^(D*T) := Nat.one_le_two_pow
  calc
    x+y+z+2 ≤ 8*2^(D*T) := by omega
    _ = 2^(D*T+3) := by rw [pow_add]; norm_num; ring
    _ ≤ 2^((a+b+(c+4))*T) := by
      apply Nat.pow_le_pow_right (by decide)
      dsimp only [D]
      nlinarith

theorem shape_clock_le_exp (n p q₁ q₂ s w Q E k : ℕ) (hE : 9 ≤ E)
    (hs : 3 ≤ s) (hn : n ≤ 2^E) (hp : p ≤ 2^E) (hq₁ : q₁ ≤ 2^E)
    (hq₂ : q₂ ≤ 2^E) (hsE : s ≤ 2^E) (hw : w ≤ 2^E) (hQ : Q ≤ 2^E) :
    CodeGeneratorComplete.clock n p s q₁ q₂ w Q k ≤
      2^(shapeExponent*(k+1)*(E+1)) := by
  let M := 2^E
  let A := (M+1)^(18*(k+1))
  let T := (k+1)*(E+1)
  have hM : 512 ≤ M := by
    change 2^9 ≤ 2^E
    exact Nat.pow_le_pow_right (by decide) hE
  have hloop := CodeGeneratorClockSum.totalClock_seed_le_cap M n p s q₁ q₂ w Q k
    hM hn hp hs hsE hq₁ hq₂ hw hQ
  have hpoly : CodeGeneratorStepGrowth.roundPoly n s q₁ q₂ w Q A A ≤
      CodeGeneratorStepGrowth.roundPoly M M M M M M A A := by
    dsimp [CodeGeneratorStepGrowth.roundPoly,CodeRecursiveStepClock.polynomialClock,
      CodeRecursiveStepClock.graphCap,CodeRecursiveStepClock.taggedCap,TaggedCompiler.polynomialClock]
    gcongr
  have hseed : CodeRecursiveSeedJoin.clock p ≤ 6*M+17 := by
    dsimp [CodeRecursiveSeedJoin.clock,CodeRecursiveSeedJoin.b₁]
    omega
  have hclock : CodeGeneratorComplete.clock n p s q₁ q₂ w Q k ≤
      6*M+19+k*(CodeGeneratorStepGrowth.roundPoly M M M M M M A A+1) := by
    have hm := Nat.mul_le_mul_left k (Nat.add_le_add_right hpoly 1)
    unfold CodeGeneratorComplete.clock
    change CodeRecursiveLoop.totalClock n s q₁ q₂ w Q (copies p .bit) (.ticket p) k ≤
      1+k*(CodeGeneratorStepGrowth.roundPoly n s q₁ q₂ w Q A A+1) at hloop
    omega
  have hMA : M+1 ≤ A := by
    have h := pow_le_pow_right₀ (show 1 ≤ M+1 by omega) (show 1 ≤ 18*(k+1) by omega)
    simpa only [pow_one] using h
  have hscalar := CodeGeneratorExponentPublic.publicClock_scalar_bound M A k hMA
  rw [shapeExponent,coefficientDatum.property]
  exact coefficient_exponential_bound CodeGeneratorExponentPublic.coeff E k
    (CodeGeneratorComplete.clock n p s q₁ q₂ w Q k) (hclock.trans hscalar)

#print axioms shape_clock_le_exp

def fullExponent : ℕ := V39PhysicalSample.fullPhysicalExponent+17*shapeExponent+104

theorem full_clock_le_exp (n : ℕ) (c : ℚ) (L edgeCount k : ℕ) (δv ζ : ℚ)
    (hn : n ≤ 2^L) (htest : FullTests c L edgeCount δv ζ) :
    clock n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L)
      k (sampleSide L k) (V39PhysicalSample.fullPrecision n L k)
      (V39PhysicalSample.fullReservation L k) ≤ 2^(fullExponent*((k+1)*L)) := by
  let T := (k+1)*L
  have hL : 16 ≤ L := htest.2.2.1
  have hT : 1 ≤ T := by dsimp [T]; nlinarith
  obtain ⟨hnE,hp,hq₁,hq₂,hs,hw,hQ⟩ := full_widths_le_pow n L hL hn
  have hs3 : 3 ≤ fullS L := by have h := fullS_ge_256 L; omega
  have hshape := shape_clock_le_exp n (seedWidth L) (fullQ₁ L) (fullQ₂ L)
    (fullS L) (fullW L) (fullQ L) (fullWidthExponent L) k (by unfold fullWidthExponent; omega)
    hs3 hnE hp hq₁ hq₂ hs hw hQ
  have hshape' : CodeGeneratorComplete.clock n (seedWidth L) (fullS L)
      (fullQ₁ L) (fullQ₂ L) (fullW L) (fullQ L) k ≤ 2^((17*shapeExponent)*T) := by
    apply hshape.trans
    apply Nat.pow_le_pow_right (by decide)
    have hm := Nat.mul_le_mul_left (shapeExponent*(k+1)) (show 16*L+1 ≤ 17*L by omega)
    simpa only [T,fullWidthExponent,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hm
  have hsample := V39PhysicalSample.full_physical_clock_le n c L edgeCount k δv ζ hn htest
  have hcopy : copyClock n (seedWidth L) (fullQ₁ L) (fullQ₂ L)
      (fullS L) (fullW L) (fullQ L) k ≤ 2^(100*T) := by
    let M := 2^fullWidthExponent L
    have hk : k ≤ T := by dsimp [T]; nlinarith
    have hMT : M ≤ 2^(16*T) := Nat.pow_le_pow_right (by decide)
      (by unfold fullWidthExponent; dsimp [T]; nlinarith)
    have hkk : k ≤ 2^(16*T) := hk.trans ((Nat.lt_two_pow_self.le).trans
      (Nat.pow_le_pow_right (by decide) (by omega)))
    have hsum : publicLength n (seedWidth L) (fullQ₁ L) (fullQ₂ L)
        (fullS L) (fullW L) (fullQ L) k ≤ 8*2^(16*T) := by
      unfold publicLength
      change n ≤ M at hnE
      change seedWidth L ≤ M at hp
      change fullQ₁ L ≤ M at hq₁
      change fullQ₂ L ≤ M at hq₂
      change fullS L ≤ M at hs
      change fullW L ≤ M at hw
      change fullQ L ≤ M at hQ
      omega
    have hone : 1 ≤ 2^(16*T) := Nat.one_le_two_pow
    calc
      copyClock n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) k ≤
          256*2^(16*T) := by unfold copyClock; omega
      _ = 2^(16*T+8) := by rw [pow_add]; norm_num; ring
      _ ≤ 2^(100*T) := Nat.pow_le_pow_right (by decide) (by omega)
  have hsample' : V39PhysicalSample.clock n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) k (sampleSide L k) (V39PhysicalSample.fullPrecision n L k)
      (V39PhysicalSample.fullReservation L k) ≤ 2^(V39PhysicalSample.fullPhysicalExponent*T) := hsample
  have hall := combine_exponential_clocks V39PhysicalSample.fullPhysicalExponent (17*shapeExponent)
    100 T _ _ _ hT hsample' hshape' hcopy
  change _ ≤ 2^(fullExponent*T)
  have he : V39PhysicalSample.fullPhysicalExponent+17*shapeExponent+(100+4)=fullExponent := rfl
  rw [he] at hall
  unfold clock
  omega

#print axioms shape_clock_le_exp
#print axioms full_clock_le_exp

end
end CurrentAdditive.V39PhysicalShapeSample
