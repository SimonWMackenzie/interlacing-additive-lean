import CurrentAdditive.GaussWholeStepSizeCaps
import CurrentAdditive.GaussCanonicalFieldClock

namespace CurrentAdditive.GaussWholeStepClockCaps
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
open EthInapproximability.CurrentPaper
open GaussWholeStepSizeCaps GaussCellPolynomialClock

def fieldsCap (n b : Nat) : Nat := 32*b+36+
  GaussPivotQuadraticClock32.totalCoefficient*(200*(n+b+1)+1)^2+
  100*(n+b+1)+2
def frontBank (n : Nat) : Nat := bankCap n (frontCap n)
def rewriteBudget (n : Nat) : Nat := rewriteCap (frontBank n)
def rewriteBank (n : Nat) : Nat := bankCap n (frontCap n+2+rewriteBudget n)
def wholeClock (n : Nat) : Nat := frontCap n+2+rewriteBudget n+1+
  fieldsCap n (rewriteBank n)+rewriteBank n+2*(200*(n+rewriteBank n+1))+8

theorem prepare_clock_le (S : Fin 64 → List Bool) (b : Nat)
    (hb : ∀j,(S j).length≤b) : GaussNextFieldsPrepare64.clock S≤32*b+36 := by
  have hs : (∑i : Fin 30,(S (GaussNextFieldsPrepare64.resetBank i)).length)≤30*b := by
    calc
      _ ≤ ∑_i : Fin 30,b := Finset.sum_le_sum (fun i _ => hb _)
      _ =30*b := by simp
  unfold GaussNextFieldsPrepare64.clock GaussNextFieldsPrepare64.resetClock
  have h:=hb 56
  omega

theorem pivot_clock_le {m k : Nat} (s : GaussControlTrace.State m k)
    (S : Fin 64 → List Bool) (b : Nat) (hr : s.r < m) (hc : s.c < k)
    (hcount : s.r=s.pivots.length)
    (hb : ∀j,(S j).length≤b)
    (h22 : S 22=GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B) :
    GaussNextStateFields64.pivotClock s S hr hc≤fieldsCap
      (GaussControlTrace.statePacket s).length b := by
  have hp:=prepare_clock_le S b hb
  have hc':=GaussCanonicalFieldClock.byteCharge_canonical_linear s hr hc hcount
  change GaussPivotByteSize32.byteCharge s
    (GaussNextFieldsPrepare64.foreign [true]
      (GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B)) hr hc≤_ at hc'
  have hm : (GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B).length≤b := by
    rw [←h22]; exact hb 22
  have hcharge : GaussPivotByteSize32.byteCharge s
      (GaussNextFieldsPrepare64.foreign [true]
        (GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B)) hr hc≤
      200*((GaussControlTrace.statePacket s).length+b+1) := hc'.trans (by gcongr)
  unfold GaussNextStateFields64.pivotClock fieldsCap
  calc
    _ ≤ (32*b+36)+GaussPivotQuadraticClock32.totalCoefficient*
      (200*((GaussControlTrace.statePacket s).length+b+1)+1)^2+2 := by gcongr
    _ ≤ _ := by omega

theorem noPivot_clock_le {m k : Nat} (s : GaussControlTrace.State m k)
    (S : Fin 64 → List Bool) (b : Nat) (hb : ∀j,(S j).length≤b) :
    GaussNextStateFieldsFrame64.noPivotClock s S (S 22)≤fieldsCap
      (GaussControlTrace.statePacket s).length b := by
  have hp:=prepare_clock_le S b hb
  have hc:=GaussCanonicalFieldClock.noPivot_clock_linear s (S 22)
  change GaussNoPivotClock32.clock s (GaussNextFieldsPrepare64.foreign [false] (S 22))≤_ at hc
  have hm:=hb 22
  unfold GaussNextStateFieldsFrame64.noPivotClock fieldsCap
  omega

theorem bankCap_mono {n a b : Nat} (hab : a≤b) : bankCap n a≤bankCap n b := by
  unfold bankCap; gcongr

theorem frontBank_le_rewriteBank (n : Nat) : frontBank n≤rewriteBank n := by
  apply bankCap_mono
  omega

theorem fieldsCap_mono {n a b : Nat} (hab : a≤b) : fieldsCap n a≤fieldsCap n b := by
  unfold fieldsCap; gcongr

theorem frontBank_polynomial : PolynomialBound (fun _ n => frontBank n) :=
  add second (mul (constant pushConstant) front_polynomial)
theorem rewriteBudget_polynomial : PolynomialBound (fun _ n => rewriteBudget n) := by
  exact polynomial_compose (f:=rewriteCap) rewrite_polynomial frontBank_polynomial
theorem rewriteBank_polynomial : PolynomialBound (fun _ n => rewriteBank n) :=
  add second (mul (constant pushConstant)
    (add (add front_polynomial (constant 2)) rewriteBudget_polynomial))
theorem fields_polynomial : PolynomialBound (fun _ n => fieldsCap n (rewriteBank n)) := by
  have hsum:=add (add second rewriteBank_polynomial) (constant 1)
  exact add (add (add (add (mul (constant 32) rewriteBank_polynomial) (constant 36))
    (mul (constant _) (power (add (mul (constant 200) hsum) (constant 1)) 2)))
    (mul (constant 100) hsum)) (constant 2)
theorem whole_polynomial : PolynomialBound (fun _ n => wholeClock n) := by
  have hanswer:=mul (constant 200) (add (add second rewriteBank_polynomial) (constant 1))
  exact add (add (add (add (add (add (add front_polynomial (constant 2))
    rewriteBudget_polynomial) (constant 1)) fields_polynomial) rewriteBank_polynomial)
    (mul (constant 2) hanswer)) (constant 8)

#print axioms prepare_clock_le
#print axioms pivot_clock_le
#print axioms noPivot_clock_le
#print axioms whole_polynomial
end
end CurrentAdditive.GaussWholeStepClockCaps
