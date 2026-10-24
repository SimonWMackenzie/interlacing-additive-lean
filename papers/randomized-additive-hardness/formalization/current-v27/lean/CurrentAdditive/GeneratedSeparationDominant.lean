import CurrentAdditive.GeneratedSeparationPrefix

/-! Appendix I `det:separation`: two heavy original blocks cannot enter the
same depth-`t` Alice part of the actual indexed protocol. -/

namespace CurrentAdditive.GeneratedSeparation

open Paper2 Workspace.Types.Protocol
open CurrentAdditive.ArbitraryPrefix

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]
  {t : ℕ}

noncomputable def partMass (μ : FiniteLaw X)
    (P : Protocol (Fin (2^t) × X) S Bool)
    (R : Fin (2^t) → Set X)
    (j i : Fin (2^t)) : ℝ :=
  μ.prob (fun x => x ∈ R i ∧
    NPCC.Protocol.prefixCodeRaw t P (i,x) = j)

/-- No terminal Alice-prefix part can hold two original blocks of mass at
least `2ρ`: the actual residual protocol would cost at least `d+1` bits. -/
theorem no_two_heavy_blocks
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    (decode : S → Fin (2^t) → Z)
    (hwise : IsDWise 8 source decode ν.toFiniteLaw)
    (R : Fin (2^t) → Set X) (K : Set S)
    (d : ℕ) (ρ : ℝ) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hscale : 2*ρ ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (hK : (18/25 : ℝ) ≤ source.prob (· ∈ K))
    (P : Protocol (Fin (2^t) × X) S Bool)
    (hp : Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix t P)
    (hcost : P.cost ≤ d+t)
    (heval : ∀ i : Fin (2^t), ∀ x ∈ R i, ∀ s ∈ K,
      P.eval (i,x) s = F x (decode s i))
    (j i k : Fin (2^t)) (hik : i ≠ k) :
    ¬ (2*ρ ≤ partMass μ.toFiniteLaw P R j i ∧
      2*ρ ≤ partMass μ.toFiniteLaw P R j k) := by
  classical
  rintro ⟨hi, hk⟩
  let Good : Finset (Fin (2^t)) := {i,k}
  let Rj : Fin (2^t) → Set X := fun a =>
    {x | x ∈ R a ∧ NPCC.Protocol.prefixCodeRaw t P (a,x) = j}
  have hGood : 2^(1-1)+1 ≤ Good.card := by
    simp [Good, hik]
  have hrow : ∀ a ∈ Good,
      (2 : ℝ)^1 * ρ ≤ μ.toFiniteLaw.prob (· ∈ Rj a) := by
    intro a ha
    have hai : a = i ∨ a = k := by simpa [Good] using ha
    rcases hai with rfl | rfl
    · simpa [partMass, Rj] using hi
    · simpa [partMass, Rj] using hk
  have hK' : (9/25 : ℝ) ≤ source.prob (· ∈ K) := by linarith
  have hl := CurrentAdditive.ArbitraryPrefix.exactboost μ ν F source decode
    hwise Good Rj K d 1 ρ (by omega) hd hρ (by simpa using hscale)
    hprofile hGood hrow hK'
  let Pj := NPCC.Protocol.rowSubtreeAtRaw t P j
  have hcostj : Pj.cost ≤ d := by
    have hc := Paper2.SourceProtocolPrefixTree.subtree_cost_add_le t P hp j
    dsimp [Pj]
    omega
  have hevalj : ∀ a ∈ Good, ∀ x ∈ Rj a, ∀ s ∈ K,
      Pj.eval (a,x) s = F x (decode s a) := by
    intro a ha x hx s hs
    have hpreeq := Paper2.SourceProtocolPrefixTree.subtree_eval_of_prefix
      t P hp j (a,x) s hx.2
    rw [hpreeq]
    exact heval a x hx.1 s hs
  have hu := selected_suffix_upper
    (fun a s => F a.2 (decode s a.1)) Good Rj K Pj d hcostj hevalj
  omega

#print axioms CurrentAdditive.GeneratedSeparation.no_two_heavy_blocks

/-- Pure finite weighted matching. A block has total mass above `2qρ`, while
each part can have only one block at threshold `2ρ`. The strict mass gap
eliminates all finite-carrier rounding assumptions. -/
theorem weighted_dominant_matching
    (t : ℕ) (ht : 1 ≤ t) (ρ z : ℝ)
    (M : Fin (2^t) → Fin (2^t) → ℝ)
    (hblock : ∀ i, z ≤ ∑ j, M j i)
    (hgap : 2 * ((2^t : ℕ) : ℝ) * ρ < z)
    (hsingle : ∀ j i k, i ≠ k →
      ¬ (2*ρ ≤ M j i ∧ 2*ρ ≤ M j k)) :
    ∃ dom : Fin (2^t) ≃ Fin (2^t),
      ∀ j, z - (2^t-1 : ℕ) * (2*ρ) < M j (dom j) ∧
        (∀ i, i ≠ dom j → M j i < 2*ρ) := by
  classical
  have hnonempty : (Finset.univ : Finset (Fin (2^t))).Nonempty :=
    ⟨⟨0, Nat.two_pow_pos t⟩, Finset.mem_univ _⟩
  have hpart (i : Fin (2^t)) : ∃ j, 2*ρ ≤ M j i := by
    by_contra hn
    have hsmall : ∀ j : Fin (2^t), M j i < 2*ρ := by
      intro j
      by_contra hnot
      exact hn ⟨j, le_of_not_gt hnot⟩
    have hs := Finset.sum_lt_sum_of_nonempty hnonempty
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2^t)))) => hsmall j)
    have hs' : (∑ j : Fin (2^t), M j i) <
        ((2^t : ℕ) : ℝ) * (2*ρ) := by
      simpa [Finset.sum_const, nsmul_eq_mul] using hs
    have hb := hblock i
    nlinarith
  let f : Fin (2^t) → Fin (2^t) := fun i => Classical.choose (hpart i)
  have hf (i : Fin (2^t)) : 2*ρ ≤ M (f i) i :=
    Classical.choose_spec (hpart i)
  have hfi : Function.Injective f := by
    intro i k hfk
    by_contra hik
    exact hsingle (f i) i k hik ⟨hf i, by simpa [hfk] using hf k⟩
  have hfb : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hfi, rfl⟩
  let e : Fin (2^t) ≃ Fin (2^t) := Equiv.ofBijective f hfb
  let dom : Fin (2^t) ≃ Fin (2^t) := e.symm
  refine ⟨dom, ?_⟩
  intro j
  have hheavy (k : Fin (2^t)) : 2*ρ ≤ M k (dom k) := by
    have hh := hf (dom k)
    have he : f (dom k) = k := e.apply_symm_apply k
    rw [he] at hh
    exact hh
  have hforeign (k : Fin (2^t)) (hkj : k ≠ j) :
      M k (dom j) < 2*ρ := by
    by_contra hn
    have hdom : dom j ≠ dom k := by
      intro heq
      exact hkj (dom.injective heq.symm)
    exact hsingle k (dom j) (dom k) hdom
      ⟨le_of_not_gt hn, hheavy k⟩
  have hneErase : ((Finset.univ : Finset (Fin (2^t))).erase j).Nonempty := by
    have hcard : 2 ≤ 2^t := by
      have hh : 2^1 ≤ 2^t := pow_le_pow_right₀ (by omega) ht
      simpa using hh
    have hc : ((Finset.univ : Finset (Fin (2^t))).erase j).card =
        2^t-1 := by simp
    apply Finset.card_pos.mp
    rw [hc]
    omega
  have hsum := Finset.sum_lt_sum_of_nonempty hneErase
    (fun k hk => hforeign k (by
      exact Finset.ne_of_mem_erase hk))
  have hsum' : (∑ k ∈ (Finset.univ : Finset (Fin (2^t))).erase j,
      M k (dom j)) < ((2^t-1 : ℕ) : ℝ) * (2*ρ) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum
  have hpartition := Finset.sum_erase_add
    (s := (Finset.univ : Finset (Fin (2^t))))
    (f := fun k => M k (dom j)) (Finset.mem_univ j)
  have hb := hblock (dom j)
  constructor
  · rw [← hpartition] at hb
    linarith
  · intro i hne
    by_contra hn
    exact hsingle j (dom j) i (Ne.symm hne)
      ⟨hheavy j, le_of_not_gt hn⟩

#print axioms CurrentAdditive.GeneratedSeparation.weighted_dominant_matching

omit [Fintype S] in
private theorem part_mass_sum_ge (μ : FiniteLaw X)
    (P : Protocol (Fin (2^t) × X) S Bool)
    (R : Fin (2^t) → Set X) (i : Fin (2^t)) :
    μ.prob (· ∈ R i) ≤ ∑ j : Fin (2^t), partMass μ P R j i := by
  classical
  have hcover : (fun x : X => x ∈ R i) =
      (fun x => ∃ j ∈ (Finset.univ : Finset (Fin (2^t))),
        x ∈ R i ∧ NPCC.Protocol.prefixCodeRaw t P (i,x) = j) := by
    funext x
    simp only [Finset.mem_univ, true_and]
    apply propext
    constructor
    · intro hx
      exact ⟨NPCC.Protocol.prefixCodeRaw t P (i,x), hx, rfl⟩
    · rintro ⟨_, hx, _⟩
      exact hx
  rw [hcover]
  simpa only [partMass] using
    μ.prob_exists_le_sum (Finset.univ : Finset (Fin (2^t)))
      (fun j x => x ∈ R i ∧ NPCC.Protocol.prefixCodeRaw t P (i,x) = j)

/-- Source-faithful Appendix I separation, for the actual finite indexed
eight-wise source and any correct protocol on its retained rectangle. The
prefix is syntactically complete, and each of its `2^t` parts has one uniquely
dominant original block. -/
theorem generated_source_separation
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    (decode : S → Fin (2^t) → Z)
    (hwise : IsDWise 8 source decode ν.toFiniteLaw)
    (R : Fin (2^t) → Set X) (K : Set S)
    (d : ℕ) (ρ z : ℝ) (ht : 1 ≤ t) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (hrow : ∀ i : Fin (2^t), z ≤ μ.toFiniteLaw.prob (· ∈ R i))
    (hgap : 2 * ((2^t : ℕ) : ℝ) * ρ < z)
    (hK : (18/25 : ℝ) ≤ source.prob (· ∈ K))
    (P : Protocol (Fin (2^t) × X) S Bool)
    (hcost : P.cost ≤ d+t)
    (heval : ∀ i : Fin (2^t), ∀ x ∈ R i, ∀ s ∈ K,
      P.eval (i,x) s = F x (decode s i)) :
    Paper2.SourceProtocolPrefixTree.CompleteAlicePrefix t P ∧
    ∃ dom : Fin (2^t) ≃ Fin (2^t),
      ∀ j, z - (2^t-1 : ℕ) * (2*ρ) <
          partMass μ.toFiniteLaw P R j (dom j) ∧
        (∀ i, i ≠ dom j → partMass μ.toFiniteLaw P R j i < 2*ρ) := by
  classical
  let i₀ : Fin (2^t) := ⟨0, Nat.two_pow_pos t⟩
  have hz1 : z ≤ 1 :=
    (hrow i₀).trans (μ.toFiniteLaw.prob_le_one (· ∈ R i₀))
  have hscale : (2 : ℝ)^t * ρ ≤ 1 := by
    have hp : 0 ≤ (2 : ℝ)^t * ρ := by positivity
    have hh : ((2^t : ℕ) : ℝ) = (2 : ℝ)^t := by norm_cast
    rw [hh] at hgap
    linarith
  have hscale2 : 2*ρ ≤ 1 := by
    have hpow : 2 ≤ 2^t := by
      have hh : 2^1 ≤ 2^t := pow_le_pow_right₀ (by omega) ht
      simpa using hh
    have hh : (2 : ℝ) ≤ (2 : ℝ)^t := by exact_mod_cast hpow
    nlinarith
  have hgap' : 2 * (2 : ℝ)^t * ρ < z := by
    simpa using hgap
  have hp := complete_alice_prefix μ ν F source decode hwise
    Finset.univ R K d t ρ z hd hρ hscale hprofile
    (by simp) (by simpa using hrow) hgap' hK P hcost
    (by intro i _ x hx s hs; exact heval i x hx s hs)
  refine ⟨hp, ?_⟩
  apply weighted_dominant_matching t ht ρ z
    (partMass μ.toFiniteLaw P R)
  · intro i
    exact (hrow i).trans (part_mass_sum_ge μ.toFiniteLaw P R i)
  · exact hgap
  · intro j i k hik
    exact no_two_heavy_blocks μ ν F source decode hwise R K d ρ
      hd hρ hscale2 hprofile hK P hp hcost heval j i k hik

#print axioms CurrentAdditive.GeneratedSeparation.generated_source_separation

end CurrentAdditive.GeneratedSeparation
