import CurrentAdditive.GaussActualVectorFused
import CurrentAdditive.GaussDirectVectorABI

/-! The first-free index carried by the physical producer selects the same
dependence vector as the admitted postloop certificate packet. -/

namespace CurrentAdditive.GaussCandidateCertificate

open CurrentAdditive.GaussFirstFreeCandidate
open CurrentAdditive.GaussCertificateVectorABI
open CurrentAdditive.SequentialTotality

theorem firstFree_vector_is_postloop {m k : Nat}
    (A : Fin m → Fin k → ℚ) (hkm : m < k)
    (f : Fin k) (hf : f.val ≤ m)
    (hfree : typedFree (GaussControlTrace.after A k).pivots = some f) :
    let s := GaussControlTrace.after A k
    postloopPacket s.B s.pivots =
      some (vectorPacket (Array.ofFn (directCandidate s.B f hf))) := by
  let s := GaussControlTrace.after A k
  let out := MaterializedGauss.echelonMaterialized A 0 0 k
  have hs := GaussControlTrace.after_k A
  have hB : s.B = out.1 := hs.1
  have hp : s.pivots = out.2 := hs.2
  have hfree' : typedFree out.2 = some f := by
    change typedFree s.pivots = some f at hfree
    simpa only [hp] using hfree
  obtain ⟨g, hg, hfreeg, heqg⟩ :=
    GaussDirectPostloop.directCandidate_on_materialized A hkm
  have hfg : f = g := Option.some.inj (hfree'.symm.trans hfreeg)
  subst g
  have heq : ∀ j, directCandidate out.1 f hf j =
      typedCandidate out.1 out.2 f j := heqg
  have hfast := GaussCertificateProbe.fastPostloop_eq_on_echelon A
  change GaussCertificateProbe.fastPostloop out.1 out.2 =
    (MaterializedGauss.dependenceMaterialized A).map Array.ofFn at hfast
  have hdep : MaterializedGauss.dependenceMaterialized A =
      some (typedCandidate out.1 out.2 f) := by
    change (typedFree out.2).map (typedCandidate out.1 out.2) = _
    rw [hfree']
    rfl
  change postloopPacket s.B s.pivots =
    some (vectorPacket (Array.ofFn (directCandidate s.B f hf)))
  rw [hB, hp]
  unfold postloopPacket
  rw [hfast, hdep]
  simp only [Option.map_some]
  congr 1
  apply congrArg vectorPacket
  congr 1
  funext j
  exact (heq j).symm

#print axioms firstFree_vector_is_postloop

end CurrentAdditive.GaussCandidateCertificate
