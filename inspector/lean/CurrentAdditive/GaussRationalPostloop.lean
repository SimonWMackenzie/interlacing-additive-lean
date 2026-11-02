import CurrentAdditive.GaussMatrixPostloopMachines

namespace CurrentAdditive.GaussRationalPostloop
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
open EthInapproximability.CurrentPaper
open GaussCertificateVectorABI GaussFirstFreeCandidate
open GaussCellPolynomialClock

def relationCoefficient := Classical.choose GaussMatrixPostloopMachines.relation_polynomial
def relationExponent := Classical.choose (Classical.choose_spec GaussMatrixPostloopMachines.relation_polynomial)
def decisionCoefficient := Classical.choose GaussMatrixPostloopMachines.decision_polynomial
def decisionExponent := Classical.choose (Classical.choose_spec GaussMatrixPostloopMachines.decision_polynomial)

theorem decision_outputs {m k : Nat} (B : Fin m → Fin k → ℚ)
    (h01 : ∀i j,B i j=0 ∨ B i j=1) (hm : 0 < m) :
    GaussMatrixPostloopMachines.decisionMachine.OutputsWithin (GaussPhysical.encodeTypedMatrix B)
      [decide (SequentialTotality.typedFree (GaussControlTrace.after B k).pivots≠none)]
      (decisionCoefficient*((GaussPhysical.encodeTypedMatrix B).length+1)^decisionExponent) := by
  let A : Matrix (Fin m) (Fin k) ℤ := fun i j => if B i j=0 then 0 else 1
  have ha : ∀i j,A i j=0 ∨ A i j=1 := by intro i j; by_cases h : B i j=0 <;> simp [A,h]
  have he : (fun i j => (A i j : ℚ))=B := by
    funext i j
    rcases h01 i j with hz | ho
    · simp [A,hz]
    · simp [A,ho]
  obtain ⟨hout,hnone⟩ := GaussMatrixPostloopMachines.decision_outputs A ha hm
  simp only [he] at hout hnone
  have hb : (SequentialTotality.typedFree (GaussControlTrace.after B k).pivots≠none) ↔
      GaussPivotPrefixPhysical.prefixCount (GaussPivotPacketBridge.natPivots (GaussControlTrace.after B k).pivots)<k := by
    constructor
    · intro h; by_contra hnot; exact h (hnone.mpr hnot)
    · intro h hn; exact (hnone.mp hn) h
  have hbits : decide (SequentialTotality.typedFree (GaussControlTrace.after B k).pivots≠none)=
      decide (GaussPivotPrefixPhysical.prefixCount
        (GaussPivotPacketBridge.natPivots (GaussControlTrace.after B k).pivots)<k) := by simp only [hb]
  rw [←hbits] at hout
  apply BitMachine.outputsWithin_mono _ hout
  simpa only [Nat.zero_add] using
    (Classical.choose_spec (Classical.choose_spec GaussMatrixPostloopMachines.decision_polynomial))
      0 (GaussPhysical.encodeTypedMatrix B).length

theorem relation_outputs {m k : Nat} (B : Fin m → Fin k → ℚ)
    (h01 : ∀i j,B i j=0 ∨ B i j=1) (hm : 0 < m)
    (hdependent : SequentialTotality.typedFree (GaussControlTrace.after B k).pivots≠none) :
    let s:=GaussControlTrace.after B k
    ∃f : Fin k,∃hf : f.val ≤ m,
      postloopPacket s.B s.pivots=some (vectorPacket (Array.ofFn (directCandidate s.B f hf))) ∧
      GaussMatrixPostloopMachines.relationMachine.OutputsWithin (GaussPhysical.encodeTypedMatrix B)
        (vectorPacket (Array.ofFn (directCandidate s.B f hf)))
        (relationCoefficient*((GaussPhysical.encodeTypedMatrix B).length+1)^relationExponent) := by
  let A : Matrix (Fin m) (Fin k) ℤ := fun i j => if B i j=0 then 0 else 1
  have ha : ∀i j,A i j=0 ∨ A i j=1 := by intro i j; by_cases h : B i j=0 <;> simp [A,h]
  have he : (fun i j => (A i j : ℚ))=B := by
    funext i j
    rcases h01 i j with hz | ho
    · simp [A,hz]
    · simp [A,ho]
  have hd : SequentialTotality.typedFree
      (GaussControlTrace.after (fun i j => (A i j : ℚ)) k).pivots≠none := by simpa only [he] using hdependent
  obtain ⟨f,hf,_,hpost,hout⟩ := GaussMatrixPostloopMachines.relation_outputs A ha hm hd
  simp only [he] at hpost hout
  refine ⟨f,hf,hpost,BitMachine.outputsWithin_mono _ hout ?_⟩
  simpa only [Nat.zero_add] using
    (Classical.choose_spec (Classical.choose_spec GaussMatrixPostloopMachines.relation_polynomial))
      0 (GaussPhysical.encodeTypedMatrix B).length

theorem certified_value (a : Array (Array ℚ))
    (cert : {x : Array ℚ // SequentialCode.IsDependence a x})
    (hcert : MaterializedGauss.certifiedMaterializedDependence a=some cert) :
    MaterializedGauss.materializedArrayDependence a=some cert.val := by
  cases h : MaterializedGauss.materializedArrayDependence a with
  | none => simp [MaterializedGauss.certifiedMaterializedDependence,h] at hcert
  | some x =>
    simp only [MaterializedGauss.certifiedMaterializedDependence,h] at hcert
    split_ifs at hcert with hx
    cases hcert
    rfl

/-- The physically printed relation is exactly the coefficient array used
by the actual certified compression algorithm, in original column order. -/
theorem certificate_outputs (a : Array (Array ℚ))
    (h01 : ∀i j,SequentialArrayBridge.matrixOfArray a i j=0 ∨ SequentialArrayBridge.matrixOfArray a i j=1)
    (hm : 0 < a.size)
    (hdependent : SequentialTotality.typedFree
      (GaussControlTrace.after (SequentialArrayBridge.matrixOfArray a) (SequentialCode.columnCount a)).pivots≠none)
    (cert : {x : Array ℚ // SequentialCode.IsDependence a x})
    (hcert : MaterializedGauss.certifiedMaterializedDependence a=some cert) :
    GaussMatrixPostloopMachines.relationMachine.OutputsWithin
      (GaussPhysical.encodeTypedMatrix (SequentialArrayBridge.matrixOfArray a)) (vectorPacket cert.val)
      (relationCoefficient*((GaussPhysical.encodeTypedMatrix (SequentialArrayBridge.matrixOfArray a)).length+1)^relationExponent) := by
  let B:=SequentialArrayBridge.matrixOfArray a
  let k:=SequentialCode.columnCount a
  obtain ⟨f,hf,hpost,hout⟩:=relation_outputs B h01 hm hdependent
  have hp:=postloopPacket_eq_materialized B
  have hg:=GaussControlTrace.after_exact B k
  have hc:=certified_value a cert hcert
  have he : postloopPacket (GaussControlTrace.after B k).B (GaussControlTrace.after B k).pivots=
      some (vectorPacket cert.val) := by
    rw [hg.1,hg.2,hp]
    simpa only [MaterializedGauss.materializedArrayDependence,Option.map_map,Function.comp_def,
      Option.map_some] using congrArg (Option.map vectorPacket) hc
  rw [hpost] at he
  rw [Option.some.inj he] at hout
  exact hout

#print axioms decision_outputs
#print axioms relation_outputs
#print axioms certificate_outputs
end
end CurrentAdditive.GaussRationalPostloop
