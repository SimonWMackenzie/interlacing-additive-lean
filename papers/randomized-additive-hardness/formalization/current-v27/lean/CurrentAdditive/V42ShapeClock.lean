import CurrentAdditive.V39PhysicalShapeClock
import CurrentAdditive.V42PhysicalSampleClock
namespace CurrentAdditive.V42ShapeClock
noncomputable section
open Paper2 Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
open V42RuntimeSchedule V39PhysicalShapeSample
def fullExponent : ℕ := V42PhysicalSampleClock.fullPhysicalExponent+17*shapeExponent+104

theorem full_clock_le_exp (n : ℕ) (c : ℚ) (L edgeCount k : ℕ) (δv ζ : ℚ)
    (hn : n ≤ 2^L) (htest : FullTests c L edgeCount δv ζ) :
    clock n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L)
      k (sampleSide L k) (V42RuntimeSchedule.precision n L k)
      (V42RuntimeSchedule.reservation L k) ≤ 2^(fullExponent*((k+1)*L)) := by
  let T := (k+1)*L
  have hL : 16 ≤ L := htest.1.2.2.1
  have hT : 1 ≤ T := by dsimp [T]; nlinarith
  obtain ⟨hnE,hp,hq₁,hq₂,hs,hw,hQ⟩ := full_widths_le_pow n L hn htest.2
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
  have hsample := V42PhysicalSampleClock.full_physical_clock_le n c L edgeCount k δv ζ hn htest
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
      (fullW L) (fullQ L) k (sampleSide L k) (V42RuntimeSchedule.precision n L k)
      (V42RuntimeSchedule.reservation L k) ≤ 2^(V42PhysicalSampleClock.fullPhysicalExponent*T) := hsample
  have hall := combine_exponential_clocks V42PhysicalSampleClock.fullPhysicalExponent (17*shapeExponent)
    100 T _ _ _ hT hsample' hshape' hcopy
  change _ ≤ 2^(fullExponent*T)
  have he : V42PhysicalSampleClock.fullPhysicalExponent+17*shapeExponent+(100+4)=fullExponent := rfl
  rw [he] at hall
  unfold clock
  omega

#print axioms shape_clock_le_exp
#print axioms full_clock_le_exp

end
end CurrentAdditive.V42ShapeClock

