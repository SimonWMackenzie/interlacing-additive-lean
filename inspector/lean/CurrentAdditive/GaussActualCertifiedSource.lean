import CurrentAdditive.GaussActualCertifiedVector

/-! Source-level semantic validity of the vector produced by the actual
post-Gauss physical certificate program, for a 0-1 integral source matrix. -/

namespace CurrentAdditive.GaussActualCertifiedSource

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GaussCertificateVectorABI
open CurrentAdditive.GaussFirstFreeCandidate

theorem actual_vector_passes_check
    (a : Array (Array ℚ))
    (A : Matrix (Fin a.size) (Fin (SequentialCode.columnCount a)) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hwide : a.size < SequentialCode.columnCount a)
    (hA : ∀ i j, (A i j : ℚ) = SequentialArrayBridge.matrixOfArray a i j) :
    let k := SequentialCode.columnCount a
    let Aq : Fin a.size → Fin k → ℚ := fun i j => (A i j : ℚ)
    let s := GaussControlTrace.after Aq k
    let S := GaussStateMatrixContext.inputBank (GaussControlTrace.statePacket s) k
    ∃ (f : Fin k) (hf : f.val ≤ a.size) (t : Nat)
      (T : GaussWideVectorInvoke.OldBank → List Bool),
      t ≤ GaussActualVectorFused.totalClock s f ∧
      SequentialCode.dependenceCheck a
        (Array.ofFn (directCandidate s.B f hf)) = true ∧
      ((advance GaussWideVectorInvoke.program)^[t])
        (⟨some GaussWideVectorInvoke.start, GaussWideVectorInvoke.control,
          GaussWideVectorInvoke.wide S⟩ :
          TM2.Cfg (fun _ : GaussWideVectorInvoke.Bank => Bool) _ _) =
        ⟨none, GaussWideVectorInvoke.control,
          Function.update (GaussWideVectorInvoke.wide T)
            GaussWideVectorInvoke.slots.target
            (vectorPacket (Array.ofFn (directCandidate s.B f hf)))⟩ := by
  let k := SequentialCode.columnCount a
  let Aq : Fin a.size → Fin k → ℚ := fun i j => (A i j : ℚ)
  let s := GaussControlTrace.after Aq k
  let out := MaterializedGauss.echelonMaterialized
    (SequentialArrayBridge.matrixOfArray a) 0 0 k
  have heqA : Aq = SequentialArrayBridge.matrixOfArray a := by
    funext i j
    exact hA i j
  have houtB : s.B = out.1 := by
    dsimp only [s, out]
    rw [heqA]
    exact (GaussControlTrace.after_k
      (SequentialArrayBridge.matrixOfArray a)).1
  have houtP : s.pivots = out.2 := by
    dsimp only [s, out]
    rw [heqA]
    exact (GaussControlTrace.after_k
      (SequentialArrayBridge.matrixOfArray a)).2
  obtain ⟨f, hf, t, T, ht, hp, hr⟩ :=
    GaussActualCertifiedVector.actual_certified_vector A h01 hwide
  obtain ⟨x, hx, _, hcheck⟩ :=
    GaussCertificateVectorABI.postloopPacket_valid a hwide
  have hsame : vectorPacket x =
      vectorPacket (Array.ofFn (directCandidate s.B f hf)) := by
    have hp' : postloopPacket out.1 out.2 =
        some (vectorPacket (Array.ofFn (directCandidate s.B f hf))) := by
      change postloopPacket s.B s.pivots =
        some (vectorPacket (Array.ofFn (directCandidate s.B f hf))) at hp
      rw [houtB, houtP] at hp
      simpa only [houtB] using hp
    exact Option.some.inj (hx.symm.trans hp')
  have hxv : x = Array.ofFn (directCandidate s.B f hf) :=
    GaussDirectVectorABI.vectorPacket_injective hsame
  refine ⟨f, hf, t, T, ht, ?_, hr⟩
  simpa only [hxv] using hcheck

#print axioms actual_vector_passes_check

end CurrentAdditive.GaussActualCertifiedSource
