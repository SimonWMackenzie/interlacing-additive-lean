import CurrentAdditive.SequentialSourceCode
import CurrentAdditive.CodeDCodecV2

/-!
The literal, ordered cylinder data passed between the deterministic `Code_D`
controller and the rational elimination stage.  The pair indices and source
labels are preserved, even when two labels decode to the same word.  This file
is a semantic codec; the finite-stack enumeration/serialization program and
its clock are separate obligations.

Source: selected v27 Appendix H, `det:code`, especially the cylinder vector.
-/

namespace CurrentAdditive.CylinderFeatureCodec

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open SequentialCode CurrentAdditive.CodeDCodec

def pairBank (p : Nat × Nat) : Bank 2 :=
  fun i => if i = 0 then p.1.bits else p.2.bits

def encodePair (p : Nat × Nat) : List Bool := encode (pairBank p)

def decodePair (bits : List Bool) : Option (Nat × Nat) := do
  let S ← decode 2 bits
  let i := bitsValue (S 0)
  let y := bitsValue (S 1)
  if i.bits = S 0 && y.bits = S 1 then some (i, y) else none

@[simp] theorem decodePair_encodePair (p : Nat × Nat) :
    decodePair (encodePair p) = some p := by
  rcases p with ⟨i, y⟩
  simp [decodePair, encodePair, pairBank]

def encodeFeature (f : List (Nat × Nat)) : List Bool :=
  CodeDCodecV2.encodeItems (f.map encodePair)

def decodeFeature (bits : List Bool) : Option (List (Nat × Nat)) := do
  let items ← CodeDCodecV2.decodeItems bits
  items.mapM decodePair

def encodeFeatures (fs : Array (List (Nat × Nat))) : List Bool :=
  CodeDCodecV2.encodeItems (fs.toList.map encodeFeature)

def generatedFeatureBits (q D : Nat) (alphabet : Array Nat) : List Bool :=
  encodeFeatures (generatedFeatures q D alphabet)

@[simp] theorem decode_encodeFeature (f : List (Nat × Nat)) :
    CodeDCodecV2.decodeItems (encodeFeature f) = some (f.map encodePair) := by
  simp [encodeFeature]

private theorem mapM_pair (f : List (Nat × Nat)) :
    (f.map encodePair).mapM decodePair = some f := by
  induction f with
  | nil => rfl
  | cons p ps ih => simp [List.mapM_cons, ih]

@[simp] theorem decodeFeature_encodeFeature (f : List (Nat × Nat)) :
    decodeFeature (encodeFeature f) = some f := by
  simpa [decodeFeature, encodeFeature] using mapM_pair f

@[simp] theorem decode_encodeFeatures (fs : Array (List (Nat × Nat))) :
    CodeDCodecV2.decodeItems (encodeFeatures fs) = some (fs.toList.map encodeFeature) := by
  simp [encodeFeatures]

theorem generatedFeatureBits_order (q D : Nat) (alphabet : Array Nat) :
    CodeDCodecV2.decodeItems (generatedFeatureBits q D alphabet) =
      some ((generatedFeatures q D alphabet).toList.map encodeFeature) := by
  simp [generatedFeatureBits]

def zeroRat : RawRat := ⟨false, (0 : Nat).bits, [true]⟩
def oneRat : RawRat := ⟨false, (1 : Nat).bits, [true]⟩

@[simp] theorem zeroRat_value : zeroRat.value = 0 := by
  simp [zeroRat, RawRat.value, bitsValue,
    EthInapproximability.CurrentPaper.BitMachineBinaryMultiply.msbValue]

@[simp] theorem oneRat_value : oneRat.value = 1 := by
  norm_num [oneRat, RawRat.value, bitsValue,
    EthInapproximability.CurrentPaper.BitMachineBinaryMultiply.msbValue]

theorem zeroRat_valid : zeroRat.Valid := by
  simp [zeroRat, RawRat.Valid,
    EthInapproximability.CurrentPaper.BitMachineBinaryMultiply.msbValue]

theorem oneRat_valid : oneRat.Valid := by
  simp [oneRat, RawRat.Valid,
    EthInapproximability.CurrentPaper.BitMachineBinaryMultiply.msbValue]

@[simp] theorem decode_zeroRat :
    decodeRawRat (encodeRawRat zeroRat) = some zeroRat :=
  decodeRawRat_encodeRawRat zeroRat zeroRat_valid

@[simp] theorem decode_oneRat :
    decodeRawRat (encodeRawRat oneRat) = some oneRat :=
  decodeRawRat_encodeRawRat oneRat oneRat_valid

def encodeZeroOne (x : ℚ) : List Bool :=
  encodeRawRat (if x = 0 then zeroRat else oneRat)

def encodeRows (A : Array (Array ℚ)) : List Bool :=
  CodeDCodecV2.encodeItems (A.toList.map (fun row =>
    CodeDCodecV2.encodeItems (row.toList.map encodeZeroOne)))

def cylinders (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) : Array (Array ℚ) :=
  let features := generatedFeatures q D alphabet
  featureRows features.size
    (fun v j => generatedFeatureValue v features[j]) source

def cylinderMatrixBits (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) : List Bool :=
  encodeRows (cylinders q D alphabet source)

theorem cylinderMatrixBits_rows (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    CodeDCodecV2.decodeItems (cylinderMatrixBits q D alphabet source) =
      some ((featureRows (generatedFeatures q D alphabet).size
        (fun v j => generatedFeatureValue v
          (generatedFeatures q D alphabet)[j]) source).toList.map
        (fun row => CodeDCodecV2.encodeItems (row.toList.map encodeZeroOne))) := by
  simp [cylinderMatrixBits, cylinders, encodeRows]

theorem cylinders_rows (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    (cylinders q D alphabet source).size =
      (generatedFeatures q D alphabet).size := by
  simp [cylinders, featureRows]

theorem cylinders_columns (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) (i : Nat)
    (hi : i < (cylinders q D alphabet source).size) :
    (cylinders q D alphabet source)[i].size = source.size := by
  simp [cylinders, featureRows]

theorem generatedFeatureValue_zero_one {q : Nat} (v : Fin q → Nat)
    (f : List (Nat × Nat)) :
    generatedFeatureValue v f = 0 ∨ generatedFeatureValue v f = 1 := by
  unfold generatedFeatureValue
  split_ifs <;> simp

theorem cylinder_entry_zero_one (q D : Nat) (alphabet : Array Nat)
    (source : Array ((Fin q → Nat) × ℚ)) (i j : Nat)
    (hi : i < (cylinders q D alphabet source).size)
    (hj : j < (cylinders q D alphabet source)[i].size) :
    (cylinders q D alphabet source)[i][j] = 0 ∨
      (cylinders q D alphabet source)[i][j] = 1 := by
  have hj' : j < source.size := by
    simpa [cylinders, featureRows] using hj
  have hi' : i < (generatedFeatures q D alphabet).size := by
    simpa [cylinders, featureRows] using hi
  simpa [cylinders, featureRows] using
    (generatedFeatureValue_zero_one source[j].1
      (generatedFeatures q D alphabet)[i])

#print axioms generatedFeatureBits_order
#print axioms cylinderMatrixBits_rows
#print axioms cylinder_entry_zero_one

end CurrentAdditive.CylinderFeatureCodec
