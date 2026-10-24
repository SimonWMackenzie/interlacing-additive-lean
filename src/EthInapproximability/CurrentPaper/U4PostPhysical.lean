import EthInapproximability.CurrentPaper.U4PostBody

/-!
# Unit 4 (Paper B): `PostBody` and `PostPhysical` DISCHARGED

Lane owner:b-unit4-shell-3 (private, 26 September 2026).

The predecessor's named interface `Unit4ItemAssembly.PostBody M Mpost Cp Ep` (imported
unchanged, frozen `b-unit4-shell-owner-2/U4ItemAssembly`) holds for the ONE fixed machine
`Body.postMachine M` with `Cp = (20 * 2883 ^ 3 + 400) * (M.stackCount + 30) ^ 2` and `Ep = 6`,
for every `M`. Hence `Unit4ItemAssembly.PostPhysical M` for every `M`.
-/

namespace EthInapproximability.CurrentPaper.Unit4Post.Body

variable (M : BitMachine.Machine)

def Cp (sc : ℕ) : ℕ := (20 * 2883 ^ 3 + 400) * (sc + 30) ^ 2

theorem postTime_bound (sc wl Pl n k m r y p : ℕ)
    (hw : n + k + m + r + m * r + y ≤ wl)
    (hP : Pl = 2 * (2 ^ (2 * p) + y + k) + (sc + 4))
    (hp : Exponent.pexp n k = p) :
    postTime (sc + 4 + 19) wl Pl (Local.localBound n k m r y) (sc + 4 + 25) ≤
      Cp sc * (wl + 1) ^ 6 * (2 ^ (2 * p)) ^ 6 := by
  have hQ1 : 1 ≤ 2 ^ (2 * p) := Nat.one_le_two_pow
  have h2p : 2 ^ p ≤ 2 ^ (2 * p) := Nat.pow_le_pow_right (by omega) (by omega)
  have hSX : sc + 4 + 19 + wl + 1 ≤ (sc + 30) * (wl + 1) := by
    have e1 : wl ≤ (sc + 30) * wl := Nat.le_mul_of_pos_left wl (by omega)
    have e2 : (sc + 30) * (wl + 1) = (sc + 30) * wl + (sc + 30) := by ring
    omega
  generalize hX : wl + 1 = X at hSX ⊢
  generalize hQ : 2 ^ (2 * p) = Q at hQ1 h2p hP
  have hX1 : 1 ≤ X := by omega
  generalize hZ : X * Q = Z
  have hZX : X ≤ Z := by rw [← hZ]; exact Nat.le_mul_of_pos_right X (by omega)
  have hZQ : Q ≤ Z := by rw [← hZ]; exact Nat.le_mul_of_pos_left Q (by omega)
  have hZ1 : 1 ≤ Z := le_trans hX1 hZX
  have hZ2 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) Z
  have hZ6 : Z ≤ Z ^ 6 := Nat.le_self_pow (by norm_num) Z
  -- the writer's clock
  have hwb := PadWriter.padded_clock m r p
  have hi1 : 2 * 2 ^ p + m + r + m * r + 1 ≤ 6 * Z := by omega
  have hi2 : (2 * 2 ^ p + m + r + m * r + 1) ^ 2 ≤ 36 * Z ^ 2 := by
    calc (2 * 2 ^ p + m + r + m * r + 1) ^ 2 ≤ (6 * Z) ^ 2 := Nat.pow_le_pow_left hi1 2
      _ = 36 * Z ^ 2 := by ring
  have hi3 : 2 * 2 ^ p + 80 * (2 * 2 ^ p + m + r + m * r + 1) ^ 2 + 1 ≤ 2883 * Z ^ 2 := by
    omega
  have hi4 : (2 * 2 ^ p + 80 * (2 * 2 ^ p + m + r + m * r + 1) ^ 2 + 1) ^ 3 ≤
      2883 ^ 3 * Z ^ 6 := by
    calc (2 * 2 ^ p + 80 * (2 * 2 ^ p + m + r + m * r + 1) ^ 2 + 1) ^ 3
        ≤ (2883 * Z ^ 2) ^ 3 := Nat.pow_le_pow_left hi3 3
      _ = 2883 ^ 3 * Z ^ 6 := by ring
  have hWB : MatrixTableWriter.writerBound (2 ^ p) (2 ^ p)
      (PadWriter.callbackBound (2 ^ p) (2 ^ p) m r (m * r)) ≤ 20 * 2883 ^ 3 * Z ^ 6 := by
    calc _ ≤ 20 * (2 * 2 ^ p + 80 * (2 * 2 ^ p + m + r + m * r + 1) ^ 2 + 1) ^ 3 := hwb
      _ ≤ 20 * (2883 ^ 3 * Z ^ 6) := Nat.mul_le_mul_left 20 hi4
      _ = 20 * 2883 ^ 3 * Z ^ 6 := by ring
  -- the fixed width factor
  generalize hS : sc + 30 = S at hSX
  have hS1 : 1 ≤ S := by omega
  have hprod : (2 * (sc + 4 + 25) + 1) * (sc + 4 + 19 + wl + 1) ≤ 2 * (S ^ 2 * Z) := by
    calc (2 * (sc + 4 + 25) + 1) * (sc + 4 + 19 + wl + 1) ≤ (2 * S) * (S * X) :=
          Nat.mul_le_mul (by omega) hSX
      _ = 2 * (S ^ 2 * X) := by ring
      _ ≤ 2 * (S ^ 2 * Z) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hZX)
  generalize hB : S ^ 2 * Z ^ 6 = B
  have hS2 : 1 ≤ S ^ 2 := Nat.one_le_pow _ _ hS1
  have hZ6B : Z ^ 6 ≤ B := by rw [← hB]; exact Nat.le_mul_of_pos_left _ hS2
  have hSZB : S ^ 2 * Z ≤ B := by rw [← hB]; exact Nat.mul_le_mul_left _ hZ6
  have hSS : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) S
  have hSB : S ≤ B := by
    calc S ≤ S ^ 2 := hSS
      _ = S ^ 2 * 1 := (mul_one _).symm
      _ ≤ S ^ 2 * Z := Nat.mul_le_mul_left _ hZ1
      _ ≤ B := hSZB
  have hZB : Z ≤ B := le_trans hZ6 hZ6B
  have hgoal : Cp sc * X ^ 6 * Q ^ 6 = (20 * 2883 ^ 3 + 400) * B := by
    rw [← hB, ← hZ, ← hS, Cp]
    ring
  rw [hgoal]
  have hpq : Exponent.pexp n k = p := hp
  unfold postTime Local.localBound Exponent.bound
  rw [hpq]
  clear hwb hi1 hi2 hi3 hi4 hgoal
  omega

/-- **`PostBody` discharged** for the ONE fixed post machine, for every estimator machine `M`. -/
theorem post_body :
    Unit4ItemAssembly.PostBody M (postMachine M) (Cp M.stackCount) 6 := by
  intro n k m r y R hm hr
  have h := post_outputs M n k y R hm hr
  apply BitMachine.outputsWithin_mono _ h
  have hw : n + k + m + r + m * r + y ≤
      (Unit4ItemAssembly.hb2Word n k m r y (MatrixMaterialization.rowMajor R)).length := by
    have he := BitMachineBankCodec.encode_length
      (![List.replicate n true, List.replicate k true, List.replicate m true,
        List.replicate r true, MatrixMaterialization.rowMajor R, List.replicate y true] :
          Fin 6 → List Bool)
    simp [Fin.sum_univ_six] at he
    unfold Unit4ItemAssembly.hb2Word
    omega
  have hP : (SignedMidpointApproxCanonical.packet M
      (FinalPadding.table R (Exponent.pexp n k) hm hr) y k).length =
      2 * (2 ^ (2 * Exponent.pexp n k) + y + k) + (M.stackCount + 4) := by
    unfold SignedMidpointApproxCanonical.packet
    rw [BitMachineBankCodec.encode_length, Fin.sum_univ_add]
    have hs1 : (∑ i : Fin M.stackCount, (SignedMidpointApproxCanonical.bank M
        (FinalPadding.table R (Exponent.pexp n k) hm hr) y k (Fin.castAdd 4 i)).length) =
        2 ^ (2 * Exponent.pexp n k) := by
      simp only [SignedMidpointApproxCanonical.bank, SignedMidpointApproxPacket.stackEquiv,
        finSumFinEquiv_symm_apply_castAdd]
      simp [apply_ite, FinalPadding.table_length]
    have hs2 : (∑ i : Fin 4, (SignedMidpointApproxCanonical.bank M
        (FinalPadding.table R (Exponent.pexp n k) hm hr) y k (Fin.natAdd M.stackCount i)).length)
        = y + k := by
      simp only [SignedMidpointApproxCanonical.bank, SignedMidpointApproxPacket.stackEquiv,
        finSumFinEquiv_symm_apply_natAdd]
      simp [Fin.sum_univ_four]
    rw [hs1, hs2]
    simp only [SignedMidpointApproxPacket.Width]
    omega
  exact postTime_bound M.stackCount _ _ n k m r y (Exponent.pexp n k) hw hP rfl

/-- **`PostPhysical` holds for every estimator machine.** -/
theorem post_physical : Unit4ItemAssembly.PostPhysical M :=
  ⟨postMachine M, Cp M.stackCount, 6, post_body M⟩

end EthInapproximability.CurrentPaper.Unit4Post.Body
