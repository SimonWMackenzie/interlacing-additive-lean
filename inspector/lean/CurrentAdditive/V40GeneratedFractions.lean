import CurrentAdditive.V39PublicGeneratedSchedule

namespace CurrentAdditive.V40GeneratedFractions
noncomputable section
set_option maxHeartbeats 4000000
open V38Schedule V39GeneratedConstruction
structure Fr where
  num : Nat
  den : Nat
  deriving DecidableEq
namespace Fr
def value (a : Fr) : ℚ := (a.num:ℚ)/a.den
def nat (n : Nat) : Fr := ⟨n,1⟩
def mul (a b : Fr) : Fr := ⟨a.num*b.num,a.den*b.den⟩
def div (a b : Fr) : Fr := ⟨a.num*b.den,a.den*b.num⟩
def divNat (a : Fr) (n : Nat) : Fr := ⟨a.num,a.den*n⟩
def pow (a : Fr) (n : Nat) : Fr := ⟨a.num^n,a.den^n⟩
def cross (a b : Fr) : Nat×Nat := (a.num*b.den,b.num*a.den)
def ofRat (q : ℚ) : Fr := ⟨q.num.toNat,q.den⟩
@[simp] theorem nat_value (n : Nat) : (nat n).value=(n:ℚ) := by simp [nat,value]
@[simp] theorem mul_value (a b : Fr) : (mul a b).value=a.value*b.value := by simp [mul,value,mul_div_mul_comm]
@[simp] theorem div_value (a b : Fr) : (div a b).value=a.value/b.value := by
  simp [div,value,div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_left_comm,mul_comm]
@[simp] theorem divNat_value (a : Fr) (n : Nat) : (divNat a n).value=a.value/n := by simp [divNat,value,div_div]
@[simp] theorem pow_value (a : Fr) (n : Nat) : (pow a n).value=a.value^n := by simp [pow,value,div_pow]
theorem ofRat_value (q : ℚ) (hq : 0≤q) : (ofRat q).value=q := by
  have hn : (q.num.toNat:ℤ)=q.num := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hnq : (q.num.toNat:ℚ)=(q.num:ℚ) := by exact_mod_cast hn
  simp only [ofRat,value,hnq,Rat.num_div_den]
theorem ofRat_num_pos (q : ℚ) (hq : 0<q) : 0<(ofRat q).num := by
  have hn := Rat.num_pos.mpr hq
  change 0<q.num.toNat
  omega
theorem cross_iff (a b : Fr) (ha : 0<a.den) (hb : 0<b.den) :
    a.value≤b.value ↔ (cross a b).1≤(cross a b).2 := by
  unfold value cross
  rw [div_le_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hb)]
  norm_cast
end Fr

def ceilDiv (a b : Nat) := (a+b-1)/b

theorem ceil_fraction (a b : Nat) (hb : 0<b) :
    Nat.ceil ((a:ℚ)/b)=ceilDiv a b := by
  change Nat.ceil ((a:ℚ)/b)=a⌈/⌉b
  have hbq : (0:ℚ)<b := by exact_mod_cast hb
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hbq).mpr
    have h : a≤b*(a⌈/⌉b) := (ceilDiv_le_iff_le_mul hb).mp le_rfl
    exact_mod_cast (by simpa [mul_comm] using h)
  · apply (ceilDiv_le_iff_le_mul hb).mpr
    have h := (div_le_iff₀ hbq).mp (Nat.le_ceil ((a:ℚ)/b))
    have hn : a≤Nat.ceil ((a:ℚ)/b)*b := by exact_mod_cast h
    simpa [mul_comm] using hn

#print axioms ceil_fraction
#print axioms Fr.cross_iff
end
end CurrentAdditive.V40GeneratedFractions
