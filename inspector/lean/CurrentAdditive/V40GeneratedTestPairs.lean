import CurrentAdditive.V40GeneratedFractions
namespace CurrentAdditive.V40GeneratedTestPairs
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
open V38Schedule V39GeneratedConstruction V40GeneratedFractions

def cN (p : SourceConstants) := p.deletion.num.toNat
def cD (p : SourceConstants) := p.deletion.den
def gN (p : SourceConstants) := p.gamma.num.toNat
def gD (p : SourceConstants) := p.gamma.den

def etaFr (p : SourceConstants) (L : Nat) := Fr.divNat (Fr.ofRat p.deletion) (generatedS L)
def deltaFr (p : SourceConstants) (n m : Nat) :=
  Fr.divNat (Fr.mul (Fr.ofRat p.gamma) (Fr.nat m)) (2*p.degree*n)
def zetaFr (p : SourceConstants) := Fr.divNat (Fr.ofRat p.gamma) 24
def rhoFr (L : Nat) := Fr.divNat (Fr.nat 1) (generatedN L)
def xFr (L : Nat) := Fr.divNat (Fr.nat 1) (generatedN L^8)
def scaledEtaFr (p : SourceConstants) (L : Nat) :=
  Fr.mul (Fr.mul (Fr.nat (generatedS L)) (etaFr p L)) (Fr.nat (2^16))
def unitCount (b : Nat) := 2^90*2^((b+63)/64)
def etaCount (p : SourceConstants) (L : Nat) :=
  ceilDiv (2^92*cD p^2*generatedS L^2*2^((6*L+72)/64)) (cN p^2)
def restCount (p : SourceConstants) (L : Nat) :=
  ceilDiv (2^100*cD p^2*generatedS L^2*generatedW L^2*2^((L+63)/64)) (cN p^2)
def c128Fr := Fr.ofRat C128

/-- Exactly twenty comparisons. No passing-candidate guard is used to
simplify a rejected candidate, a truncated subtraction, or an integer quotient. -/
def fractionPairs (p : SourceConstants) (n m L : Nat) : Fin 20 → Fr×Fr :=
  let s := generatedS L
  let q₁ := generatedQ₁ L
  let q₂ := generatedQ₂ L
  let w := generatedW L
  let Q := generatedQ L
  let η := etaFr p L
  let x := xFr L
  let S := Fr.nat s
  let W := Fr.nat w
  ![(Fr.nat 256,S),
    (scaledEtaFr p L,Fr.nat 1),
    (scaledEtaFr p L,deltaFr p n m),
    (scaledEtaFr p L,Fr.divNat (zetaFr p) 256),
    (Fr.nat (pow2Ceil (4*s*m)),Fr.nat q₂),
    (Fr.mul (Fr.nat 4) (Fr.mul (Fr.pow S 2) (rhoFr L)),Fr.nat 1),
    (Fr.mul (Fr.nat 8) (Fr.mul S (Fr.nat q₁)),Fr.divNat (Fr.mul (zetaFr p) (Fr.nat q₂)) 16),
    (Fr.mul (Fr.nat q₂) x,Fr.divNat (Fr.nat 1) 10000),
    (Fr.mul S x,Fr.divNat (Fr.nat 1) 10000),
    (Fr.mul W x,Fr.divNat (Fr.nat 1) 10000),
    (Fr.mul (Fr.nat 2) (Fr.mul (Fr.pow W 2) x),Fr.div η (Fr.mul (Fr.nat 16) (Fr.divNat (Fr.nat 255) 256))),
    (Fr.mul (Fr.mul (Fr.pow W 2) (Fr.nat q₂)) x,Fr.nat 1),
    (Fr.mul (Fr.mul (Fr.mul (Fr.divNat (Fr.nat 4) 256) W) (Fr.nat q₂)) x,Fr.divNat η 32),
    (Fr.nat (unitCount (9+6*L)),Fr.nat (w/128)),
    (Fr.nat (unitCount (11+6*L)),Fr.nat (s*q₂)),
    (Fr.div c128Fr (Fr.pow S 128),Fr.divNat (Fr.divNat (Fr.nat 1) (512*Q)) 4),
    (Fr.nat (2*etaCount p L),Fr.nat (w/4)),
    (Fr.nat (Kstar (2*L) s*(2*etaCount p L)),Fr.divNat (Fr.mul η W) 16),
    (Fr.nat (unitCount (8*L)),Fr.nat (s/128)),
    (Fr.nat (128*(restCount p L+1)),Fr.nat Q)]

def literalPairs (p : SourceConstants) (n m L : Nat) : Fin 20 → Nat×Nat :=
  fun i => Fr.cross (fractionPairs p n m L i).1 (fractionPairs p n m L i).2

def literalTests (p : SourceConstants) (n m L : Nat) : Prop :=
  ∀ i, (literalPairs p n m L i).1≤(literalPairs p n m L i).2

def fractionTests (p : SourceConstants) (n m L : Nat) : Prop :=
  ∀ i, (fractionPairs p n m L i).1.value≤(fractionPairs p n m L i).2.value

@[simp] theorem eta_value (p : SourceConstants) (L : Nat) :
    (etaFr p L).value=generatedEta p.deletion L := by
  simp only [etaFr,Fr.divNat_value,Fr.ofRat_value _ p.deletion_pos.le,generatedEta]
@[simp] theorem delta_value (p : SourceConstants) (n m : Nat) :
    (deltaFr p n m).value=sourceDeltaV p.gamma p.degree n m := by
  simp [deltaFr,Fr.ofRat_value _ p.gamma_pos.le,sourceDeltaV]
@[simp] theorem zeta_value (p : SourceConstants) : (zetaFr p).value=sourceZeta p.gamma := by
  simp [zetaFr,Fr.ofRat_value _ p.gamma_pos.le,sourceZeta]
@[simp] theorem rho_value (L : Nat) : (rhoFr L).value=generatedRho L := by simp [rhoFr,generatedRho]
@[simp] theorem x_value (L : Nat) : (xFr L).value=generatedX L := by simp [xFr,generatedX]
@[simp] theorem scaledEta_value (p : SourceConstants) (L : Nat) :
    (scaledEtaFr p L).value=(generatedS L:ℚ)*generatedEta p.deletion L*2^16 := by
  simp only [scaledEtaFr,Fr.mul_value,Fr.nat_value,eta_value,Nat.cast_pow,Nat.cast_ofNat]
theorem c128_pos : 0<C128 := by
  unfold C128
  exact pow_pos (div_pos (by norm_num) (sq_pos_of_pos (by norm_num))) _
@[simp] theorem c128_value : c128Fr.value=C128 := Fr.ofRat_value _ c128_pos.le
@[simp] theorem unitCount_eq (b : Nat) : unitCount b=ebar b 1 := (V38Cutoff.ebar_unit b).symm

theorem cN_pos (p : SourceConstants) : 0<cN p := Fr.ofRat_num_pos _ p.deletion_pos

theorem etaCount_eq (p : SourceConstants) (L : Nat) :
    etaCount p L=ebar (9+generatedQlog L) (generatedEta p.deletion L/2) := by
  have hc : (cN p:ℚ)≠0 := by exact_mod_cast (cN_pos p).ne'
  have hd : (cD p:ℚ)≠0 := by exact_mod_cast p.deletion.den_pos.ne'
  have hs : (generatedS L:ℚ)≠0 := by unfold generatedS; positivity
  rw [etaCount,←ceil_fraction _ _ (by exact pow_pos (cN_pos p) 2)]
  unfold ebar
  congr 1
  have hdel := (Fr.ofRat_value p.deletion p.deletion_pos.le).symm
  change p.deletion=(cN p:ℚ)/cD p at hdel
  rw [generatedEta,hdel]
  push_cast
  unfold generatedQlog
  have he : 9+6*L+63=6*L+72 := by omega
  rw [he]
  field_simp <;> norm_num

theorem restCount_eq (p : SourceConstants) (L : Nat) :
    restCount p L=ebar L (deltaU (generatedEta p.deletion L) (generatedW L)/2) := by
  have hc : (cN p:ℚ)≠0 := by exact_mod_cast (cN_pos p).ne'
  have hd : (cD p:ℚ)≠0 := by exact_mod_cast p.deletion.den_pos.ne'
  have hs : (generatedS L:ℚ)≠0 := by unfold generatedS; positivity
  have hw : (generatedW L:ℚ)≠0 := by unfold generatedW generatedN; positivity
  rw [restCount,←ceil_fraction _ _ (by exact pow_pos (cN_pos p) 2)]
  unfold ebar
  congr 1
  have hdel := (Fr.ofRat_value p.deletion p.deletion_pos.le).symm
  change p.deletion=(cN p:ℚ)/cD p at hdel
  rw [deltaU,generatedEta,hdel]
  push_cast
  field_simp <;> norm_num

#print axioms etaCount_eq
#print axioms restCount_eq
end
end CurrentAdditive.V40GeneratedTestPairs
