import CurrentAdditive.GaussWholeRationalInput

namespace CurrentAdditive.CylinderWholeGauss
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open EthInapproximability.CurrentPaper
open CylinderFeatureCodec SequentialCode

theorem matrix_zero_one (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    ∀i j,SequentialArrayBridge.matrixOfArray (cylinders q D alphabet source) i j=0 ∨
      SequentialArrayBridge.matrixOfArray (cylinders q D alphabet source) i j=1 := by
  let a:=cylinders q D alphabet source
  have hpos:=SequentialSourceCode.generatedFeatures_pos q D alphabet
  have hK : columnCount a=source.size := by
    simpa [a,cylinders] using SequentialCompressionTotality.featureRows_columnCount
      (generatedFeatures q D alphabet).size
      (fun v j => generatedFeatureValue v (generatedFeatures q D alphabet)[j]) source hpos
  intro i j
  have hi : i.val < (cylinders q D alphabet source).size:=i.isLt
  have hj : j.val < (cylinders q D alphabet source)[i.val].size := by
    rw [cylinders_columns q D alphabet source i.val hi]
    simpa only [←hK] using j.isLt
  have hz:=cylinder_entry_zero_one q D alphabet source i.val j.val hi hj
  simpa [SequentialArrayBridge.matrixOfArray,cell,Array.getElem?_eq_getElem hi,
    Array.getElem?_eq_getElem hj] using hz

theorem outputs (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    let B:=SequentialArrayBridge.matrixOfArray (cylinders q D alphabet source)
    GaussWholeMatrixMachine.machine.OutputsWithin (cylinderMatrixBits q D alphabet source)
      (GaussControlTrace.statePacket (GaussControlTrace.after B
        (columnCount (cylinders q D alphabet source))))
      (GaussWholeMatrixMachine.clock (cylinderMatrixBits q D alphabet source).length) := by
  let a:=cylinders q D alphabet source
  let B:=SequentialArrayBridge.matrixOfArray a
  have hm : 0 < a.size := by
    rw [show a.size=(generatedFeatures q D alphabet).size from cylinders_rows q D alphabet source]
    exact SequentialSourceCode.generatedFeatures_pos q D alphabet
  have hout:=GaussWholeRationalInput.outputs B (matrix_zero_one q D alphabet source) hm
  have hb:=CylinderGaussABI.cylinder_to_gauss_bytes q D alphabet source
  change cylinderMatrixBits q D alphabet source=GaussPhysical.encodeTypedMatrix B at hb
  rw [←hb] at hout
  exact hout

#print axioms matrix_zero_one
#print axioms outputs
end
end CurrentAdditive.CylinderWholeGauss
