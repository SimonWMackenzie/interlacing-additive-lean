import CurrentAdditive.GeneratedTwoStreamPairedParent
import Paper2.TwoStreamConversation

/-! The first ordinary-column query on the actual indexed two-stream source. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceRemainingConversationNumerics
open Workspace.Types.Protocol

variable {X Y Rw Raw F : Type*}
  [Fintype X] [Fintype Y] [Fintype Rw] [Nonempty Rw]
  [Fintype Raw] [Fintype F] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- At a live node, a first ordinary-column message can fit the source
budget only at capacity one with exactly one surviving physical bin. The
original row set and its per-bin selector images are used throughout. -/
theorem ordinary_node_forces_one
    (R₀ : X → Y → Bool)
    (M : Rw → ((src.outer.Label × src.gamma.Label) ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → src.inner.Label)
    (hordinary : ∀ r c, M r (.inl c) =
      T src R₀ (selector r) (src.outer.decode c.1 (bin r)))
    (input : Raw → Rw) (σ : Raw → src.inner.Label)
    (Q : Finset (Fin s)) (support : Fin s → Finset Raw)
    (hsel : ∀ i ∈ Q, ∀ w ∈ support i, σ w = selector (input w))
    (hbin : ∀ i ∈ Q, ∀ w ∈ support i, bin (input w) = i)
    (O : Set (src.outer.Label × src.gamma.Label))
    (hO : (4/5 : ℝ) < (ordinaryLaw src).toFiniteLaw.prob (· ∈ O))
    (H a r : ℕ) (hr : r ≤ a) (hH : 2 ≤ H) (x : ℝ) (hx : 0 < x)
    (hD : 8 ≤ D) (hs : s = 2^a)
    (hsmall : SourceSupportSchedule.floor s x 0 ≤ 1/8)
    (hprofile : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x (H : ℤ))
    (hmass : ∀ i ∈ Q, SourceSupportSchedule.floor s x r ≤
      ProjectedSupportStep.mass src.inner.law.toFiniteLaw σ (support i))
    (hbig : (3/4 : ℝ) * ((s : ℝ)/(2 : ℝ)^r) ≤ Q.card)
    (query : ((src.outer.Label × src.gamma.Label) ⊕ F) → Bool)
    (left right : Protocol ((src.outer.Label × src.gamma.Label) ⊕ F) Rw Bool)
    (hvalue : ∀ i ∈ Q, ∀ w ∈ support i, ∀ c ∈ O,
      (Protocol.aNode query left right).eval (.inl c) (input w) =
        M (input w) (.inl c))
    (hcost : (Protocol.aNode query left right).cost ≤ H+(a-r)) :
    a-r=0 ∧ Q.card=1 := by
  classical
  let R : Set Rw := Paper2.TwoStreamConversation.nodeRows Q support input
  obtain ⟨b, hchild, hchild9⟩ :=
    TwoStreamColumnStep.exists_dense_child (ordinaryLaw src).toFiniteLaw O
      Sum.inl query hO
  let Ochild := TwoStreamColumnStep.ordinaryChild O Sum.inl query b
  have hvalueR : ∀ row ∈ R, ∀ c ∈ O,
      (Protocol.aNode query left right).eval (.inl c) row = M row (.inl c) := by
    rintro row ⟨i, hi, w, hw, rfl⟩ c hc
    exact hvalue i hi w hw c hc
  have hchildcost : Compression.restrictionD
      (fun row c => M row (.inl c)) R Ochild + 1 ≤
      (Protocol.aNode query left right).cost :=
    TwoStreamColumnStep.ordinary_restriction_add_one_le
      (fun row c => M row (.inl c)) R O Sum.inl query left right
      hvalueR b
  have hmatrix : Compression.restrictionD M R (Sum.inl '' Ochild) =
      Compression.restrictionD (fun row c => M row (.inl c)) R Ochild := by
    have h := Paper2.restrictionD_pullback_image M id Sum.inl R Ochild
    simpa using h.symm
  have hbudget : Compression.restrictionD M R (Sum.inl '' Ochild)+1 ≤
      H+(a-r) := by
    rw [hmatrix]
    exact hchildcost.trans hcost
  let k := a-r
  have hcap : (s : ℝ)/(2 : ℝ)^r = (2 : ℝ)^k :=
    capacity_eq_pow hs hr
  have hscale := capacity_scale hx.le hsmall hs hr
  let e := coordinateEnumeration Q
  have he : Function.Injective e := coordinateEnumeration_injective Q
  have hfloorEq : SourceSupportSchedule.floor s x r =
      2*(2 : ℝ)^k*x := by
    rw [hs, SourceSupportSchedule.floor_capacity a r x hr]
  have hrow : ∀ j : Fin Q.card, 2*(2 : ℝ)^k*x ≤
      src.inner.law.toFiniteLaw.prob
        (fun z => ∃ row ∈ R, bin row = e j ∧ selector row = z) := by
    intro j
    have hf := hmass (e j) (coordinateEnumeration_mem Q j)
    rw [hfloorEq] at hf
    change 2*(2 : ℝ)^k*x ≤ _ at hf
    have hm : ProjectedSupportStep.mass src.inner.law.toFiniteLaw σ
        (support (e j)) ≤ src.inner.law.toFiniteLaw.prob
          (fun z => ∃ row ∈ R, bin row = e j ∧ selector row = z) := by
      apply src.inner.law.toFiniteLaw.prob_mono
      rintro z ⟨w, hw, hz⟩
      exact ⟨input w, Paper2.TwoStreamConversation.nodeRows_mem Q support input
        (coordinateEnumeration_mem Q j) hw,
        hbin (e j) (coordinateEnumeration_mem Q j) w hw,
        (hsel (e j) (coordinateEnumeration_mem Q j) w hw).symm.trans hz⟩
    exact hf.trans hm
  have hbig' : (3/4 : ℝ)*(2 : ℝ)^k ≤ Q.card := by
    simpa only [← hcap] using hbig
  by_cases hk : 2 ≤ k
  · have hcount := SourceSupportSchedule.power_block_count hk hbig'
    have hrow' : ∀ j : Fin Q.card, (2 : ℝ)^k*x ≤
        src.inner.law.toFiniteLaw.prob
          (fun z => ∃ row ∈ R, bin row = e j ∧ selector row = z) := by
      intro j
      have hp := hrow j
      nlinarith [show 0 ≤ (2 : ℝ)^k*x by positivity]
    have hlower := selected_ordinary_original_lower src R₀ M bin selector
      hordinary H k Q.card x hD (by omega) hH hx hscale.1 hprofile
      e he (by simpa using hcount) R Ochild hrow' hchild9
    omega
  · by_cases hkone : k=1
    · have hcount : 2 ≤ Q.card := by
        apply SourceSupportSchedule.two_block_count
        simpa [hkone] using hbig'
      have hrow' : ∀ j : Fin Q.card, (2 : ℝ)^1*x ≤
          src.inner.law.toFiniteLaw.prob
            (fun z => ∃ row ∈ R, bin row = e j ∧ selector row = z) := by
        intro j
        have hh := hrow j
        simp only [hkone, pow_one] at hh
        nlinarith [show 0 ≤ x by positivity]
      have hlower := selected_ordinary_original_lower src R₀ M bin selector
        hordinary H 1 Q.card x hD (by omega) hH hx
        (by simpa only [pow_one] using hscale.2) hprofile
        e he (by simpa using hcount) R Ochild hrow' hchild9
      omega
    · have hkzero : k=0 := by omega
      by_contra hcard
      have hcard' : 2 ≤ Q.card := by
        have hh : 0 < Q.card := by
          have : (0 : ℝ) < Q.card := by
            have hh : (3/4 : ℝ) ≤ Q.card := by simpa [hkzero] using hbig'
            linarith
          exact_mod_cast this
        omega
      have hrow' : ∀ j : Fin Q.card, (2 : ℝ)^1*x ≤
          src.inner.law.toFiniteLaw.prob
            (fun z => ∃ row ∈ R, bin row = e j ∧ selector row = z) := by
        intro j
        simpa [hkzero] using hrow j
      have hlower := selected_ordinary_original_lower src R₀ M bin selector
        hordinary H 1 Q.card x hD (by omega) hH hx
        (by simpa only [pow_one] using hscale.2) hprofile
        e he (by simpa using hcard') R Ochild hrow' hchild9
      omega

#print axioms ordinary_node_forces_one

end CurrentAdditive.DeterministicIndexedMatrix.Sources
