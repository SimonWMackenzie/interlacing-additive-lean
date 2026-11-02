import CurrentAdditive.Endpoint

/-! The byte target for the post-Gauss coefficient writer: a V2 counted list
of canonical RawRat records, in original source-column order. This is a
semantic ABI and does not assert a physical writer. -/

namespace CurrentAdditive.GaussCertificateVectorABI

open CurrentAdditive.CodeDCodec

def coefficientPacket (q : ℚ) : List Bool :=
  encodeRawRat (GaussPhysical.rawOfRat q)

def vectorPacket (x : Array ℚ) : List Bool :=
  CodeDCodecV2.encodeItems (x.toList.map coefficientPacket)

def decodeVectorPacket (input : List Bool) : Option (List ℚ) :=
  match CodeDCodecV2.decodeItems input with
  | none => none
  | some xs =>
      match xs.mapM decodeRawRat with
      | none => none
      | some rs => some (rs.map RawRat.value)

def postloopPacket {m k : Nat} (B : Fin m → Fin k → ℚ)
    (ps : List (Fin m × Fin k)) : Option (List Bool) :=
  (GaussCertificateProbe.fastPostloop B ps).map vectorPacket

theorem vectorPacket_decode (x : Array ℚ) :
    CodeDCodecV2.decodeItems (vectorPacket x) =
      some (x.toList.map coefficientPacket) := by
  simp [vectorPacket, CodeDCodecV2.decodeItems_encodeItems]

theorem coefficientPacket_decode (q : ℚ) :
    decodeRawRat (coefficientPacket q) =
      some (GaussPhysical.rawOfRat q) := by
  exact decodeRawRat_encodeRawRat _ (GaussPhysical.rawOfRat_valid q)

private theorem decode_coefficients (xs : List ℚ) :
    (xs.map coefficientPacket).mapM decodeRawRat =
      some (xs.map GaussPhysical.rawOfRat) := by
  induction xs with
  | nil => rfl
  | cons q xs ih =>
      simp [List.mapM_cons, coefficientPacket_decode, ih]

theorem decodeVectorPacket_vectorPacket (x : Array ℚ) :
    decodeVectorPacket (vectorPacket x) = some x.toList := by
  simp only [decodeVectorPacket, vectorPacket,
    CodeDCodecV2.decodeItems_encodeItems]
  rw [decode_coefficients]
  simp [Function.comp_def, GaussPhysical.rawOfRat_value]

theorem postloopPacket_eq_materialized {m k : Nat}
    (A : Fin m → Fin k → ℚ) :
    let out := MaterializedGauss.echelonMaterialized A 0 0 k
    postloopPacket out.1 out.2 =
      (MaterializedGauss.dependenceMaterialized A).map
        (fun x => vectorPacket (Array.ofFn x)) := by
  dsimp only [postloopPacket]
  rw [GaussCertificateProbe.fastPostloop_eq_on_echelon]
  simp [Option.map_map, Function.comp_def]

theorem postloopPacket_valid (a : Array (Array ℚ))
    (h : a.size < SequentialCode.columnCount a) :
    let out := MaterializedGauss.echelonMaterialized
      (SequentialArrayBridge.matrixOfArray a) 0 0
      (SequentialCode.columnCount a)
    ∃ x, postloopPacket out.1 out.2 = some (vectorPacket x) ∧
      decodeVectorPacket (vectorPacket x) = some x.toList ∧
      SequentialCode.dependenceCheck a x = true := by
  obtain ⟨x, hx, hcheck⟩ := GaussCertificateProbe.fastPostloop_check a h
  refine ⟨x, ?_, decodeVectorPacket_vectorPacket x, hcheck⟩
  simp [postloopPacket, hx]

#print axioms postloopPacket_eq_materialized
#print axioms postloopPacket_valid

end CurrentAdditive.GaussCertificateVectorABI
