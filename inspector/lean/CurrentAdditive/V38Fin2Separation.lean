import CurrentAdditive.V38Fin2PrefixParts

namespace CurrentAdditive.V38Fin2Prefix

open Paper2 Workspace.Types.Protocol
open CurrentAdditive.ArbitraryPrefix
open scoped BigOperators

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]
  {t : ℕ}

theorem prefix_part_mass_sum (μ : FiniteLaw X) (R : Set X)
    {W : Type*} [Fintype W] [DecidableEq W] (code : X → W) :
    ∑ w, μ.prob (fun x => x ∈ R ∧ code x = w) = μ.prob (· ∈ R) := by
  classical
  unfold FiniteLaw.prob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ R
  · simp [hx]
  · simp [hx]

/-- Exact source separation for width `2^t`: its actual prefix parts are
in bijection with the original blocks and have strictly small foreign mass. -/
theorem dominant_prefix_parts
    (μ : PositiveRationalLaw X)
    (F : X → Z → Bool) (source : FiniteLaw S)
    (decode : S → Fin (2^t) → Z)
    (R : Fin (2^t) → Set X) (K : Set S)
    (d : ℕ) (ρ z : ℝ)
    (ht : 1 ≤ t) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hscale : (2 : ℝ)^t*ρ ≤ 1)
    (hblock : ExactBlockBound μ F source decode d ρ)
    (hrow : ∀ i, z ≤ μ.toFiniteLaw.prob (· ∈ R i))
    (hgap : 2*(2 : ℝ)^t*ρ < z)
    (hK : (18/25 : ℝ) ≤ source.prob (· ∈ K))
    (P : Protocol (Fin (2^t) × X) S Bool)
    (hcost : P.cost ≤ d+t)
    (heval : ∀ i, ∀ x ∈ R i, ∀ s ∈ K,
      P.eval (i,x) s = F x (decode s i)) :
    SourceProtocolPrefixTree.CompleteAlicePrefix t P ∧
    ∃ dom : Fin (2^t) ≃ Fin (2^t),
      (∀ w, z/(2 : ℝ)^t ≤ μ.toFiniteLaw.prob
        (fun x => x ∈ R (dom w) ∧
          NPCC.Protocol.prefixCodeRaw t P (dom w,x) = w)) ∧
      (∀ w j, j ≠ dom w → μ.toFiniteLaw.prob
        (fun x => x ∈ R j ∧ NPCC.Protocol.prefixCodeRaw t P (j,x) = w) < 2*ρ) ∧
      (∀ w, z-2*((2^t : ℕ)-1 : ℕ)*ρ < μ.toFiniteLaw.prob
        (fun x => x ∈ R (dom w) ∧
          NPCC.Protocol.prefixCodeRaw t P (dom w,x) = w)) := by
  classical
  have hpref := complete_alice_prefix μ F source decode Finset.univ R K d t ρ z
    hd hρ hscale hblock (by simp) (by simpa using hrow) hgap hK P hcost
    (by intro i _; exact heval i)
  obtain ⟨f, hf, hfmass⟩ := assigned_prefix_parts μ F source decode
    Finset.univ R K d t ρ z hd hρ hscale hblock (by simp)
    (by simpa using hrow) hgap hK P hcost (by intro i _; exact heval i)
  let dom : Fin (2^t) ≃ Fin (2^t) :=
    Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have hmass (w : Fin (2^t)) : z/(2 : ℝ)^t ≤ μ.toFiniteLaw.prob
      (fun x => x ∈ R (dom w) ∧ NPCC.Protocol.prefixCodeRaw t P (dom w,x) = w) :=
    (hfmass w).2
  have hstrong (w : Fin (2^t)) : 2*ρ < μ.toFiniteLaw.prob
      (fun x => x ∈ R (dom w) ∧ NPCC.Protocol.prefixCodeRaw t P (dom w,x) = w) := by
    have hpow : (0 : ℝ) < (2 : ℝ)^t := by positivity
    have hz : 2*ρ < z/(2 : ℝ)^t := (lt_div_iff₀ hpow).2 (by nlinarith)
    exact hz.trans_le (hmass w)
  have hsmall (w j : Fin (2^t)) (hne : j ≠ dom w) : μ.toFiniteLaw.prob
      (fun x => x ∈ R j ∧ NPCC.Protocol.prefixCodeRaw t P (j,x) = w) < 2*ρ := by
    by_contra hn
    have hj : 2*ρ ≤ μ.toFiniteLaw.prob
        (fun x => x ∈ R j ∧ NPCC.Protocol.prefixCodeRaw t P (j,x) = w) := le_of_not_gt hn
    let Q : Finset (Fin (2^t)) := {dom w,j}
    let Rows : Fin (2^t) → Set X := fun i =>
      {x | x ∈ R i ∧ NPCC.Protocol.prefixCodeRaw t P (i,x) = w}
    have hscale2 : (2 : ℝ)^1*ρ ≤ 1 := by
      exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ht) hρ.le).trans hscale
    have hlo := hblock 1 Q Rows K (by omega) hscale2 (by simp [Q,hne,Ne.symm hne])
      (by
        intro i hi
        simp only [Q,Finset.mem_insert,Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · simpa only [Rows,pow_one] using (hstrong w).le
        · simpa only [Rows,pow_one] using hj)
      (by linarith : (9/25 : ℝ) ≤ source.prob (· ∈ K))
    let P' := NPCC.Protocol.rowSubtreeAtRaw t P w
    have hcost' : P'.cost ≤ d := by
      have hh := SourceProtocolPrefixTree.subtree_cost_add_le t P hpref w
      dsimp [P']
      omega
    have heval' : ∀ i ∈ Q, ∀ x ∈ Rows i, ∀ s ∈ K,
        P'.eval (i,x) s = F x (decode s i) := by
      intro i _ x hx s hs
      have hh := SourceProtocolPrefixTree.subtree_eval_of_prefix t P hpref w
        (i,x) s hx.2
      exact hh.trans (heval i x hx.1 s hs)
    have hu := selected_suffix_upper (fun a s => F a.2 (decode s a.1))
      Q Rows K P' d hcost' heval'
    omega
  refine ⟨hpref,dom,hmass,hsmall,?_⟩
  intro w
  let m : Fin (2^t) → ℝ := fun v => μ.toFiniteLaw.prob
    (fun x => x ∈ R (dom w) ∧ NPCC.Protocol.prefixCodeRaw t P (dom w,x) = v)
  have hsum : ∑ v, m v = μ.toFiniteLaw.prob (· ∈ R (dom w)) :=
    prefix_part_mass_sum μ.toFiniteLaw (R (dom w))
      (fun x => NPCC.Protocol.prefixCodeRaw t P (dom w,x))
  have hothers : ∑ v ∈ (Finset.univ : Finset (Fin (2^t))).erase w, m v <
      2*((2^t : ℕ)-1 : ℕ)*ρ := by
    have hcard : ((Finset.univ : Finset (Fin (2^t))).erase w).card = 2^t-1 := by simp
    have hnonempty : ((Finset.univ : Finset (Fin (2^t))).erase w).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      have htwo : 2 ≤ (2 : ℕ)^t := by
        calc
          2 = 2^1 := by norm_num
          _ ≤ 2^t := pow_le_pow_right₀ (by omega) ht
      have hzero := Finset.card_eq_zero.mpr h
      omega
    calc
      _ < ∑ _v ∈ (Finset.univ : Finset (Fin (2^t))).erase w, 2*ρ := by
        apply Finset.sum_lt_sum_of_nonempty hnonempty
        intro v hv
        have hvw : v ≠ w := (Finset.mem_erase.mp hv).1
        have hne : dom w ≠ dom v := fun h => hvw (dom.injective h).symm
        exact hsmall v (dom w) hne
      _ = _ := by rw [Finset.sum_const, hcard]; push_cast; ring
  have hsplit : (∑ v ∈ (Finset.univ : Finset (Fin (2^t))).erase w, m v)+m w =
      μ.toFiniteLaw.prob (· ∈ R (dom w)) := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ w)]
    exact hsum
  have hr := hrow (dom w)
  dsimp [m] at hsplit ⊢
  linarith

#print axioms dominant_prefix_parts

end CurrentAdditive.V38Fin2Prefix
