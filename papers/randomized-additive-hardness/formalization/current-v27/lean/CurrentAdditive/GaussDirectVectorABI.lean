import CurrentAdditive.GaussDirectPostloop
import CurrentAdditive.GaussCertificateVectorABI

/-! Byte-for-byte target for a physical writer using the simplified Gauss
formula. The theorem identifies its intended V2 packet with the existing
postloop certificate packet; it does not claim that the writer exists yet. -/

namespace CurrentAdditive.GaussDirectVectorABI

open CurrentAdditive.GaussFirstFreeCandidate
open CurrentAdditive.GaussCertificateVectorABI
open CurrentAdditive.SequentialTotality

theorem directVector_is_postloop {m k : Nat}
    (A : Fin m → Fin k → ℚ) (hkm : m < k) :
    let out := MaterializedGauss.echelonMaterialized A 0 0 k
    ∃ (f : Fin k) (hf : f.val ≤ m),
      postloopPacket out.1 out.2 =
        some (vectorPacket (Array.ofFn (directCandidate out.1 f hf))) := by
  obtain ⟨f, hf, hfree, heq⟩ :=
    GaussDirectPostloop.directCandidate_on_materialized A hkm
  let out := MaterializedGauss.echelonMaterialized A 0 0 k
  change ∃ (f : Fin k) (hf : f.val ≤ m),
    postloopPacket out.1 out.2 =
      some (vectorPacket (Array.ofFn (directCandidate out.1 f hf)))
  refine ⟨f, hf, ?_⟩
  have hfree' : typedFree out.2 = some f := hfree
  have hfast := GaussCertificateProbe.fastPostloop_eq_on_echelon A
  change GaussCertificateProbe.fastPostloop out.1 out.2 =
    (MaterializedGauss.dependenceMaterialized A).map Array.ofFn at hfast
  have hdep : MaterializedGauss.dependenceMaterialized A =
      some (typedCandidate out.1 out.2 f) := by
    change (typedFree out.2).map (typedCandidate out.1 out.2) = _
    rw [hfree']
    rfl
  unfold postloopPacket
  rw [hfast]
  rw [hdep]
  simp only [Option.map_some]
  congr 1
  apply congrArg vectorPacket
  congr 1
  funext j
  exact (heq j).symm

theorem vectorPacket_injective : Function.Injective vectorPacket := by
  intro x y h
  have hv := congrArg decodeVectorPacket h
  rw [decodeVectorPacket_vectorPacket,
    decodeVectorPacket_vectorPacket] at hv
  cases x with
  | mk xs =>
    cases y with
    | mk ys => simpa using (Option.some.inj hv)

theorem directVector_valid (a : Array (Array ℚ))
    (h : a.size < SequentialCode.columnCount a) :
    let A := SequentialArrayBridge.matrixOfArray a
    let out := MaterializedGauss.echelonMaterialized A 0 0
      (SequentialCode.columnCount a)
    ∃ (f : Fin (SequentialCode.columnCount a))
        (hf : f.val ≤ a.size),
      postloopPacket out.1 out.2 =
        some (vectorPacket (Array.ofFn (directCandidate out.1 f hf))) ∧
      SequentialCode.dependenceCheck a
        (Array.ofFn (directCandidate out.1 f hf)) = true := by
  let A := SequentialArrayBridge.matrixOfArray a
  let out := MaterializedGauss.echelonMaterialized A 0 0
    (SequentialCode.columnCount a)
  obtain ⟨f, hf, hpacket⟩ := directVector_is_postloop A h
  obtain ⟨x, hx, _, hcheck⟩ :=
    GaussCertificateVectorABI.postloopPacket_valid a h
  have hp : vectorPacket x =
      vectorPacket (Array.ofFn (directCandidate out.1 f hf)) := by
    have hsame := hpacket.symm.trans hx
    exact Option.some.inj hsame.symm
  have hxeq : x = Array.ofFn (directCandidate out.1 f hf) :=
    vectorPacket_injective hp
  change ∃ (f : Fin (SequentialCode.columnCount a))
      (hf : f.val ≤ a.size),
    postloopPacket out.1 out.2 =
      some (vectorPacket (Array.ofFn (directCandidate out.1 f hf))) ∧
    SequentialCode.dependenceCheck a
      (Array.ofFn (directCandidate out.1 f hf)) = true
  exact ⟨f, hf, hpacket, by simpa [hxeq] using hcheck⟩

#print axioms directVector_is_postloop
#print axioms directVector_valid

end CurrentAdditive.GaussDirectVectorABI
