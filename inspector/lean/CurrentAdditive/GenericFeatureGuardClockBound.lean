import CurrentAdditive.GenericFeatureGuardedDescriptor
import CurrentAdditive.FeatureAlphabetPolynomial64
import CurrentAdditive.FeatureOuterScalarArithmetic

/-! The actual guarded descriptor callback has a uniform degree-five clock.
The proof uses the checked alphabet scan and pays its copies and cleanup. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.GenericFeatureGuardClockBound
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open FeatureAlphabetClockBounds64
open MinimumRatioContext

def guardCoefficient (D : Nat) : Nat := 1000+1000*(GenericFeatureGuardInvoke.M D).pushBound

theorem guard_arithmetic (b p : Nat) :
    (2*b+2)+(8*(b+1)+10)+(2*(b+(8*(b+1)+10)*p)+2)+
      (8*(b+(8*(b+1)+10)*p)+8+2)+3 ≤ (1000+1000*p)*(b+1) := by
  nlinarith

theorem guard_clock_le (D : Nat) (c : List (Nat × Nat)) :
    GenericFeatureGuardInvoke.clock D c ≤
      guardCoefficient D*((CylinderFeatureCodec.encodeFeature c).length+1) := by
  simpa only [GenericFeatureGuardInvoke.clock,MachineInvokeFull.uniformBound,
    GenericFeatureGuardInvoke.stack_count,guardCoefficient] using
    guard_arithmetic (CylinderFeatureCodec.encodeFeature c).length
      (GenericFeatureGuardInvoke.M D).pushBound

/-- These closed data store exact numerical equalities only; no run or bound
is certified by them. Opaqueness prevents reduction of fixed program tables. -/
private noncomputable opaque growthDatum :
    {G : Nat // G=BitMachineStackGrowth.perStep FeatureEligibleDescriptor96.beforeClear} :=
  ⟨BitMachineStackGrowth.perStep FeatureEligibleDescriptor96.beforeClear,rfl⟩

def growth : Nat := growthDatum.val

theorem growth_eq : growth=BitMachineStackGrowth.perStep FeatureEligibleDescriptor96.beforeClear :=
  growthDatum.property

private noncomputable opaque coefficientDatum (D : Nat) :
    {C : Nat // C=guardCoefficient D+
      (1+64*growth)*(FeatureAlphabetPolynomial64.coefficient+32)+69} :=
  ⟨guardCoefficient D+(1+64*growth)*(FeatureAlphabetPolynomial64.coefficient+32)+69,rfl⟩

def coefficient (D : Nat) : Nat := (coefficientDatum D).val
attribute [local irreducible] growth coefficient

theorem coefficient_eq (D : Nat) : coefficient D=guardCoefficient D+
    (1+64*growth)*(FeatureAlphabetPolynomial64.coefficient+32)+69 := by unfold coefficient; exact (coefficientDatum D).property

theorem alphabet_count (ys : List Nat) :
    ys.length ≤ (SourceListEncoding.encode (FeatureBoundedAlphabet64.original ys)).length := by
  have h := CylinderRawInputProjection.input_measure_le (FeatureBoundedAlphabet64.original ys)
  unfold CylinderProductionProjectionClock.inputMeasure at h
  simpa [FeatureBoundedAlphabet64.original,FeatureInnerAlphabetRun64.labelWords] using
    (show (FeatureBoundedAlphabet64.original ys).length ≤
      (SourceListEncoding.encode (FeatureBoundedAlphabet64.original ys)).length by omega)

theorem clock_le (D : Nat) (j : Nat) (c : List (Nat × Nat)) (ys : List Nat) (body : List Bool) :
    GenericFeatureGuardedDescriptor.clock D j c ys body ≤
      coefficient D*(inputSize j c ys body+1)^5 := by
  let L := inputSize j c ys body
  have hys : ys.length ≤ L := (alphabet_count ys).trans (by dsimp [L,inputSize]; omega)
  have hdesc : (CylinderFeatureCodec.encodeFeature c).length ≤ L := by dsimp [L,inputSize]; omega
  have hlinear : L+1 ≤ (L+1)^5 := le_self_pow (by omega) (by decide)
  have hscan := FeatureAlphabetPolynomial64.scanClock_le j c ys body
  have halpha : (SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)).length≤L := by
    dsimp [L,inputSize,FeatureBoundedAlphabet64.original]; omega
  have hbody : body.length≤L := by dsimp [L,inputSize]; omega
  have hj : j.bits.length≤L := by dsimp [L,inputSize]; omega
  have hext : (body++GenericFeatureEligibleDescriptor.extensions j c ys).length≤L := by
    dsimp [L,inputSize,extensions,GenericFeatureEligibleDescriptor.extensions]
    simp only [List.length_append]
    omega
  have hprefix : FeatureEligibleDescriptor96.prefixClock j c ys body ≤
      (FeatureAlphabetPolynomial64.coefficient+32)*(L+1)^5 := by
    exact FeatureOuterScalarArithmetic.prefix_bound _ L _ _ _ _ _ _ _
      halpha hbody hj hys hdesc hext hscan hlinear
  have hguard := guard_clock_le D c
  have hg : GenericFeatureGuardInvoke.clock D c ≤ guardCoefficient D*(L+1)^5 :=
    hguard.trans (Nat.mul_le_mul_left _ ((Nat.add_le_add_right hdesc 1).trans hlinear))
  have heligible : GenericFeatureEligibleDescriptor.clock j c ys body ≤
      (1+64*growth)*(FeatureAlphabetPolynomial64.coefficient+32)*(L+1)^5+67 := by
    unfold GenericFeatureEligibleDescriptor.clock
    rw [←growth_eq]
    exact FeatureOuterScalarArithmetic.eligible _ _ growth _ hprefix
  have hone : 1 ≤ (L+1)^5 := (by omega : 1≤L+1).trans hlinear
  rw [coefficient_eq]
  unfold GenericFeatureGuardedDescriptor.clock
  exact FeatureOuterScalarArithmetic.guarded _ _ _ _ _ _ hg heligible hone

#print axioms clock_le
end CurrentAdditive.GenericFeatureGuardClockBound
