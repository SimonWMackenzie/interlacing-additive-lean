import CurrentAdditive.V39UniformResource

namespace CurrentAdditive.V39UniformResource

open CurrentAdditive.DeterministicIteration

universe u v

/-- A fixed polynomial charge on the final complete encoding fits one public
exponent. This applies separately to a measured writer clock and to its full
binary output length; no physical implementation is inferred from the bound. -/
theorem polynomial_charge_at_final_envelope
    (N A C₁ k Z f e : ℕ) (hN : 2 ≤ N) (hA : 1 ≤ A)
    (hZ : Z ≤ N^(C₁*A^k)) :
    f*Z^e ≤ N^((f+C₁*e)*A^k) := by
  have hN1 : 1 ≤ N := by omega
  have hAk : 1 ≤ A^k := Nat.one_le_pow _ _ hA
  have hf : f ≤ N^f :=
    (self_le_two_pow f).trans (Nat.pow_le_pow_left hN f)
  have hZpow := Nat.pow_le_pow_left hZ e
  have hexp : f+(C₁*A^k)*e ≤ (f+C₁*e)*A^k := by
    have hh := Nat.mul_le_mul_left f hAk
    nlinarith
  calc
    f*Z^e ≤ N^f*(N^(C₁*A^k))^e := Nat.mul_le_mul hf hZpow
    _ = N^(f+(C₁*A^k)*e) := by rw [← pow_mul, ← pow_add]
    _ ≤ N^((f+C₁*e)*A^k) := Nat.pow_le_pow_right hN1 hexp

/-- A common explicit exponent for rounds, startup and final materialization.
The constants `f,e` bound both startup on `N` and finishing on the final
complete encoding, and hence are fixed before the input or round count. -/
def completeExponent (c d f e : ℕ) : ℕ :=
  (seedExponent c d+1)+(f+seedExponent c d*e)+(f+e)+2

theorem completeExponent_positive (c d f e : ℕ) :
    1 ≤ completeExponent c d f e := by
  simp only [completeExponent]
  omega

/-- The full charged construction time, including startup and a final fixed
polynomial in the actual complete encoding, has the manuscript's uniform
`N^(C₀*A^k)` form. The same bound applies to output length when that length
obeys the displayed final polynomial. All arithmetic includes `k=0`. -/
theorem complete_construction_resource
    {Graph : Type u} {State : Type v}
    (C : Construction Graph State) (G : Graph) (N c d f e k startup finish output : ℕ)
    (hN : 2 ≤ N) (V : ValidContract C G)
    (hseed : C.size (C.seed G) ≤ c*N^d)
    (hsize : ∀ R, C.valid G R →
      C.size (C.step G R) ≤ c*(envelope C N R)^d)
    (hclock : ∀ R, C.valid G R →
      C.stepTime R ≤ c*(envelope C N R)^d)
    (hstartup : startup ≤ f*N^e)
    (hfinish : finish ≤ f*(envelope C N (state C G k))^e)
    (houtput : output ≤ f*(envelope C N (state C G k))^e) :
    startup+totalStepTime C G k+finish ≤
        N^(completeExponent c d f e*(amplification c d)^k) ∧
    output ≤ N^(completeExponent c d f e*(amplification c d)^k) := by
  let A := amplification c d
  let C₁ := seedExponent c d
  let H := (C₁+1)+(f+C₁*e)+(f+e)
  have hA : 1 ≤ A := (by omega : 1 ≤ 2).trans (amplification_ge_two c d)
  have hAk : 1 ≤ A^k := Nat.one_le_pow _ _ hA
  have hN1 : 1 ≤ N := by omega
  have R := resourceContract_of_fixed_polynomial C G N c d hN hseed hsize hclock
  have hZ : envelope C N (state C G k) ≤ N^(C₁*A^k) :=
    growth_iteration C G N A C₁ k V R
  have hfinal : f*(envelope C N (state C G k))^e ≤ N^((f+C₁*e)*A^k) :=
    polynomial_charge_at_final_envelope N A C₁ k _ f e hN hA hZ
  have hround : totalStepTime C G k ≤ N^((C₁+1)*A^k) :=
    total_time_power C G N A C₁ k hN (amplification_ge_two c d) V R
  have hstart : startup ≤ N^((f+e)*A^k) := by
    have hbase : N ≤ N^(1*A^k) := by
      simpa only [one_mul] using Nat.le_self_pow (by omega) N
    have hh := polynomial_charge_at_final_envelope N A 1 k N f e hN hA hbase
    simpa only [one_mul] using hstartup.trans hh
  have hstartH : startup ≤ N^(H*A^k) := hstart.trans
    (Nat.pow_le_pow_right hN1 (Nat.mul_le_mul_right _ (by dsimp [H]; omega)))
  have hroundH : totalStepTime C G k ≤ N^(H*A^k) := hround.trans
    (Nat.pow_le_pow_right hN1 (Nat.mul_le_mul_right _ (by dsimp [H]; omega)))
  have hfinalH : f*(envelope C N (state C G k))^e ≤ N^(H*A^k) := hfinal.trans
    (Nat.pow_le_pow_right hN1 (Nat.mul_le_mul_right _ (by dsimp [H]; omega)))
  have hthree : 3 ≤ N^2 := by nlinarith
  have hsum : startup+totalStepTime C G k+finish ≤ N^((H+2)*A^k) := by
    calc
      startup+totalStepTime C G k+finish ≤ 3*N^(H*A^k) := by
        have hf := hfinish.trans hfinalH
        omega
      _ ≤ N^2*N^(H*A^k) := Nat.mul_le_mul_right _ hthree
      _ = N^(2+H*A^k) := by rw [pow_add]
      _ ≤ N^((H+2)*A^k) := by
        apply Nat.pow_le_pow_right hN1
        nlinarith
  have hout : output ≤ N^((H+2)*A^k) :=
    (houtput.trans hfinalH).trans
      (Nat.pow_le_pow_right hN1 (Nat.mul_le_mul_right _ (by omega : H ≤ H+2)))
  exact ⟨hsum, hout⟩

#print axioms polynomial_charge_at_final_envelope
#print axioms completeExponent_positive
#print axioms complete_construction_resource

end CurrentAdditive.V39UniformResource
