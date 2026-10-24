import CurrentAdditive.GaussUniformMatrixSupport

/-! Charge the complete adapted request list to the full support k≤m*M. -/

namespace CurrentAdditive.GaussRequestSupportLength

open CurrentAdditive.GaussNestedMatrixMap

theorem listBytes_mono_size (n L R : Nat) (h : L ≤ R) :
    listBytes n L ≤ listBytes n R := by
  unfold listBytes
  gcongr

theorem actual_request_full_support {m k Mparam : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hk : k ≤ m*Mparam)
    (t : Nat) (ht : t ≤ k)
    (r pivot : Fin m) (c : Fin k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let B := (CurrentAdditive.GaussControlTrace.after Aq t).B
    (encodeNested (GaussAdaptedMatrixMap.adaptedMatrix B r pivot c)).length ≤
      listBytes m (listBytes (m*Mparam)
        (GaussUniformMatrixActual.requestCap m)) := by
  have h := GaussAdaptedRequestLength.actual_encoded_adapted_length_le
    A h01 t ht r pivot c
  exact h.trans
    (listBytes_mono_size m _ _
      (GaussMatrixSupportClock.listBytes_mono k (m*Mparam)
        (GaussUniformMatrixActual.requestCap m) hk))

#print axioms actual_request_full_support

end CurrentAdditive.GaussRequestSupportLength
