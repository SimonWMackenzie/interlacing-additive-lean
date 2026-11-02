import CurrentAdditive.FeatureSeedMachine96
import CurrentAdditive.GaussCellPolynomialClock

namespace CurrentAdditive.FeatureSeedClock96
noncomputable section
open EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioContext GaussCellPolynomialClock FeatureSeedPrepare
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] PolynomialBound CylinderRawInputProjection.coefficient
  CylinderRawInputProjection.qMachine CylinderRawInputProjection.alphabetMachine GaussRowCount.machine

def labelCap (n : Nat) := n+CylinderRawInputProjection.coefficient*(n+1)^3*A.pushBound
def innerCap (n : Nat) := 2*(96*(13+n+2*labelCap n))+96
def outputCap (n : Nat) := 2*(innerCap n+n)+2
def clockCap (n : Nat) :=
  MachineInvokeFull.uniformBound Q (List.replicate n true) (10*(n+1))+
  MachineInvokeFull.uniformBound A (List.replicate n true) (CylinderRawInputProjection.coefficient*(n+1)^3)+
  MachineInvokeFull.uniformBound C (List.replicate (labelCap n) true) (GaussRowCount.polynomialClock (labelCap n))+
    2*n+2+5+(2*innerCap n+2)+(2*outputCap n+2)+2

attribute [local irreducible] labelCap innerCap outputCap FeatureSeedLayout.bank

theorem label_length {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    (SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords (alphabet.map Prod.fst).toList)).length ≤
      labelCap (CylinderRawInputProjection.input alphabet source).length := by
  have h := BitMachine.output_length_bound A
    (CylinderRawInputProjection.alphabet_output_polynomial alphabet source)
  simpa [labelCap,CylinderProductionProjection.labelWords,
    FeatureInnerAlphabetRun64.labelWords,List.map_map] using h

theorem label_count {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    (alphabet.map Prod.fst).toList.length ≤
      labelCap (CylinderRawInputProjection.input alphabet source).length := by
  have h := GaussRowCount.rows_le_input
    (FeatureInnerAlphabetRun64.labelWords (alphabet.map Prod.fst).toList)
  simpa [FeatureInnerAlphabetRun64.labelWords] using h.trans (label_length alphabet source)

theorem finite_sum_bound {K : Nat} (f : Fin K → Nat) (b : Nat)
    (h : ∀ i,f i ≤ b) : (∑ i,f i) ≤ K*b := by
  calc
    _ ≤ ∑ _i : Fin K,b := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

theorem inner_length (raw : List Bool) (ys : List Nat) (n : Nat)
    (hr : raw.length ≤ n)
    (hl : (SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)).length ≤ labelCap n)
    (hc : ys.length ≤ labelCap n) :
    (BitMachineBankCodec.encode (FeatureSeedLayout.bank raw ys)).length ≤ innerCap n := by
  have hp : ∀ i : Fin 96,(FeatureSeedLayout.bank raw ys i).length ≤ 13+n+2*labelCap n := by
    intro i
    simp only [FeatureSeedLayout.bank]
    split_ifs <;> (try simp only [FeatureSeedLayout.seedPacket_bytes,FeatureSeedLayout.seedBody_bytes,
      FeatureSeedMachine.seedBytes,List.length_cons,List.length_nil,List.length_replicate]) <;> omega
  have hsum := finite_sum_bound (fun i : Fin 96 => (FeatureSeedLayout.bank raw ys i).length)
    (13+n+2*labelCap n) hp
  dsimp only at hsum
  rw [BitMachineBankCodec.encode_length]
  unfold innerCap
  omega

theorem output_length (raw : List Bool) (q : Nat) (ys : List Nat) (n : Nat)
    (hi : (BitMachineBankCodec.encode (FeatureSeedLayout.bank raw ys)).length ≤ innerCap n)
    (hq : q ≤ n) :
    (FeatureSeedLayout.output raw q ys).length ≤ outputCap n := by
  rw [FeatureSeedLayout.output,BitMachineBankCodec.encode_length]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    List.length_replicate,Nat.add_zero]
  unfold outputCap
  omega

theorem invocation_mono (M : BitMachine.Machine) (xs ys : List Bool) (a b : Nat)
    (hl : xs.length ≤ ys.length) (ht : a ≤ b) :
    MachineInvokeFull.uniformBound M xs a ≤ MachineInvokeFull.uniformBound M ys b := by
  unfold MachineInvokeFull.uniformBound
  gcongr

theorem clock_le {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    FeatureSeedMachine96.clock (CylinderRawInputProjection.input alphabet source) q
      (alphabet.map Prod.fst).toList ≤
        clockCap (CylinderRawInputProjection.input alphabet source).length := by
  let raw := CylinderRawInputProjection.input alphabet source
  let ys := (alphabet.map Prod.fst).toList
  let labels := SourceListEncoding.encode (FeatureInnerAlphabetRun64.labelWords ys)
  let n := raw.length
  have hl : labels.length ≤ labelCap n := label_length alphabet source
  have hc : ys.length ≤ labelCap n := label_count alphabet source
  have hq : q ≤ n := by
    simpa only [Matrix.cons_val_zero,List.length_replicate] using
      CylinderRawInputProjection.field_length_le alphabet source 0
  have hi := inner_length raw ys n (by rfl) hl hc
  have ho := output_length raw q ys n hi hq
  have hr := GaussRowCount.polynomialClock_mono hl
  have hm := invocation_mono C labels (List.replicate (labelCap n) true)
    (GaussRowCount.polynomialClock labels.length) (GaussRowCount.polynomialClock (labelCap n))
    (by simpa only [List.length_replicate] using hl) hr
  change FeatureSeedMachine96.clock raw q ys ≤ clockCap n
  unfold FeatureSeedMachine96.clock FeatureSeedPrepare.clock clockCap
  simp only [MachineInvokeFull.uniformBound,List.length_replicate] at hm ⊢
  dsimp only [labels,n] at hm hi ho ⊢
  omega

theorem clock_polynomial : PolynomialBound (fun _ n => clockCap n) := by
  have hl : PolynomialBound (fun _ n => labelCap n) := by
    unfold labelCap
    repeat' first | exact second | exact (constant _) | apply add | apply mul
  have hi : PolynomialBound (fun _ n => innerCap n) := by
    unfold innerCap
    repeat' first | exact hl | exact second | exact (constant _) | apply add | apply mul
  have ho : PolynomialBound (fun _ n => outputCap n) := by
    unfold outputCap
    exact add (mul (constant 2) (add hi second)) (constant 2)
  have hr : PolynomialBound (fun _ n => GaussRowCount.polynomialClock (labelCap n)) := by
    unfold GaussRowCount.polynomialClock GaussRowCount.itemEnvelope
    repeat' first | exact hl | exact (constant _) | apply add | apply mul
  have hq := uniform_invocation Q second (mul (constant 10) (add second (constant 1)))
  have ha := uniform_invocation A second
    (mul (constant CylinderRawInputProjection.coefficient) (power (add second (constant 1)) 3))
  have hc := uniform_invocation C hl hr
  unfold clockCap
  repeat' first | exact hq | exact ha | exact hc | exact hi | exact ho | exact second |
    exact (constant _) | apply add | apply mul

theorem exists_clock_bound : ∃ C e : Nat, ∀ s n,clockCap n ≤ C*(s+n+1)^e := by
  have h := clock_polynomial
  unfold PolynomialBound at h
  exact h

def coefficient : Nat := exists_clock_bound.choose
def exponent : Nat := exists_clock_bound.choose_spec.choose

theorem cap_polynomial (n : Nat) : clockCap n ≤ coefficient*(n+1)^exponent := by
  simpa only [coefficient,exponent,Nat.zero_add] using exists_clock_bound.choose_spec.choose_spec 0 n

/-- One fixed machine and one fixed polynomial work for every raw production
input. No prepared field, supplied run, or output-length bound is a premise. -/
theorem outputs_polynomial {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    FeatureSeedMachine96.machine.OutputsWithin (CylinderRawInputProjection.input alphabet source)
      (FeatureSeedLayout.output (CylinderRawInputProjection.input alphabet source) q
        (alphabet.map Prod.fst).toList)
      (coefficient*((CylinderRawInputProjection.input alphabet source).length+1)^exponent) :=
  BitMachine.outputsWithin_mono _ (FeatureSeedMachine96.outputs alphabet source)
    ((clock_le alphabet source).trans (cap_polynomial _))

#print axioms label_length
#print axioms clock_le
#print axioms clock_polynomial
#print axioms outputs_polynomial
end
end CurrentAdditive.FeatureSeedClock96
