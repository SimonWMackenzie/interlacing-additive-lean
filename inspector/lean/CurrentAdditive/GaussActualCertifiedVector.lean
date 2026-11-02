import CurrentAdditive.GaussCandidateCertificate

/-! The one physical work-list/coefficient run has the exact postloop
certificate as its final packet. This still starts from a post-Gauss state
packet and retained width; producing that state is a separate machine stage. -/

namespace CurrentAdditive.GaussActualCertifiedVector

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GaussCertificateVectorABI
open CurrentAdditive.GaussFirstFreeCandidate

theorem actual_certified_vector {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hkm : m < k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    let S := GaussStateMatrixContext.inputBank
      (GaussControlTrace.statePacket s) k
    ∃ (f : Fin k) (hf : f.val ≤ m) (t : Nat)
      (T : GaussWideVectorInvoke.OldBank → List Bool),
      t ≤ GaussActualVectorFused.totalClock s f ∧
      postloopPacket s.B s.pivots =
        some (vectorPacket (Array.ofFn (directCandidate s.B f hf))) ∧
      ((advance GaussWideVectorInvoke.program)^[t])
        (⟨some GaussWideVectorInvoke.start, GaussWideVectorInvoke.control,
          GaussWideVectorInvoke.wide S⟩ :
          TM2.Cfg (fun _ : GaussWideVectorInvoke.Bank => Bool) _ _) =
        ⟨none, GaussWideVectorInvoke.control,
          Function.update (GaussWideVectorInvoke.wide T)
            GaussWideVectorInvoke.slots.target
            (vectorPacket (Array.ofFn (directCandidate s.B f hf)))⟩ := by
  obtain ⟨f, hf, t, T, hfree, ht, hr⟩ :=
    GaussActualVectorFused.actual_vector_fused A h01 hkm
  refine ⟨f, hf, t, T, ht, ?_, hr⟩
  exact GaussCandidateCertificate.firstFree_vector_is_postloop
    (fun i j => (A i j : ℚ)) hkm f hf hfree

#print axioms actual_certified_vector

end CurrentAdditive.GaussActualCertifiedVector
