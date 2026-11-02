import CurrentAdditive.V39PairedObstruction
import CurrentAdditive.GeneratedTwoStreamLiveStops

/-! Current two-stream local terminals. Uses exactly the source's two
thresholds; ordinary retained mass above 3/4 gives a true child above 3/8.
The paired parent is tested before projecting its joint selector labels. -/

namespace CurrentAdditive.V39TwoStreamScalarCost
open Paper2 Workspace.Types.Protocol
variable {S J W Ω A C : Type*} [Fintype S] [Fintype J]
  [Fintype W] [Fintype Ω]
theorem one_bin_cost (μ : FiniteLaw S) (ν : FiniteLaw J) (κ : FiniteLaw Ω)
    (T : S → J → Bool) (H : ℕ) (x : ℝ)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile T μ ν x (H : ℤ))
    (σ : W → S) (φ : Ω → J) (hφ : κ.PushesTo ν φ)
    (F : Finset W) (O : Set Ω)
    (hF : x ≤ ProjectedSupportStep.mass μ σ F)
    (hO : (3 / 5 : ℝ) ≤ κ.prob (· ∈ O))
    (input : W → C) (col : Ω → A) (P : Protocol A C Bool)
    (hP : ∀ w ∈ F, ∀ c ∈ O, P.eval (col c) (input w) = T (σ w) (φ c)) :
    H ≤ P.cost := by
  classical
  let Q := Workspace.UpperBound.Protocol.comap
    (fun w : (F : Set W) => input w.val) (fun c : O => col c.val)
    (Workspace.UpperBound.Protocol.transpose P)
  have hQ : Q.Computes (fun (w : (F : Set W)) (c : O) => T (σ w.val) (φ c.val)) := by
    intro w c
    rw [Workspace.UpperBound.Protocol.comap_eval,
      Workspace.UpperBound.Protocol.transpose_eval]
    exact hP w.val w.property c.val c.property
  have hupper : Compression.restrictionD (fun w c => T (σ w) (φ c))
      (F : Set W) O ≤ P.cost := by
    have hle : Compression.restrictionD (fun w c => T (σ w) (φ c))
        (F : Set W) O ≤ Q.cost := Nat.sInf_le ⟨Q, rfl, hQ⟩
    simpa only [Q, Workspace.UpperBound.Protocol.comap_cost,
      Workspace.UpperBound.Protocol.transpose_cost] using hle
  rw [restrictionD_pullback_image T σ φ (F : Set W) O] at hupper
  have hcol : (3 / 5 : ℝ) ≤ ν.prob (· ∈ φ '' O) :=
    hO.trans (FiniteLaw.prob_le_image κ ν φ hφ O)
  have hrow : x ≤ μ.prob (· ∈ σ '' (F : Set W)) := hF
  have hl := hprofile ⟨0, by omega⟩ (σ '' (F : Set W)) (φ '' O) hrow
    (by simpa using hcol)
  simp only [Fin.val_zero, Nat.cast_zero, sub_zero] at hl
  have hnat : H ≤ Compression.restrictionD T (σ '' (F : Set W)) (φ '' O) := by
    exact_mod_cast hl
  exact hnat.trans hupper

end CurrentAdditive.V39TwoStreamScalarCost

namespace CurrentAdditive.V39TwoStreamTerminals

open Paper2 Paper2.SourceProjection Paper2.SourceRemainingConversationNumerics
open Paper2.ProjectedSupportFrontier
open CurrentAdditive.ArbitraryPrefix
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open Workspace.Types.Protocol

/-- Literal current 4*epsilon slack, including epsilon zero. -/
theorem ordinary_density {Ω : Type*} [Fintype Ω] (κ : FiniteLaw Ω)
    (O : Set Ω) (q : ℕ) (x ε δ : ℝ) (hx : 0 ≤ x)
    (hO : 1-ε ≤ κ.prob (· ∈ O)) (hδ : δ ≤ 1)
    (hslack : 2*q*x+4*ε < δ) :
    0 ≤ ε ∧ ε < 1/4 ∧ (3/4 : ℝ) < κ.prob (· ∈ O) := by
  have hp := κ.prob_le_one (· ∈ O)
  have ht : 0 ≤ 2*(q : ℝ)*x := by positivity
  constructor
  · linarith
  constructor <;> linarith

/-- The original ordinary inputs give a genuine 3/8-mass child. -/
theorem exists_dense_child {Ω B : Type*} [Fintype Ω]
    (κ : FiniteLaw Ω) (O : Set Ω) (col : Ω → B) (query : B → Bool)
    (hO : (3/4 : ℝ) < κ.prob (· ∈ O)) :
    ∃ b, (3/8 : ℝ) < κ.prob (· ∈ TwoStreamColumnStep.ordinaryChild O col query b) ∧
      (9/25 : ℝ) ≤ κ.prob (· ∈ TwoStreamColumnStep.ordinaryChild O col query b) := by
  have hp := TwoStreamColumnStep.ordinary_partition κ O col query
  by_cases hf : (3/8 : ℝ) < κ.prob (· ∈ TwoStreamColumnStep.ordinaryChild O col query false)
  · exact ⟨false,hf,by linarith⟩
  · exact ⟨true,by linarith,by linarith⟩

variable {X Y I Rw Raw F E B C : Type*}
  [Fintype X] [Fintype Y] [Fintype I] [Fintype Rw] [Nonempty Rw]
  [Fintype Raw] [Fintype F] [Fintype E]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem selected_ordinary_exact_lower
    (R₀ : X → Y → Bool) (H a n : ℕ) (x : ℝ)
    (hD : 8 ≤ D) (ha : 1 ≤ a) (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x (H : ℤ))
    (e : Fin n → Fin s) (he : Function.Injective e)
    (hcount : 2^(a-1)+1 ≤ n)
    (Rows : Fin n → Set src.inner.Label)
    (hrow : ∀ i : Fin n,
      (2 : ℝ)^a*x ≤ src.inner.law.toFiniteLaw.prob (· ∈ Rows i))
    (O : Set (src.outer.Label × src.gamma.Label))
    (hO : (9/25 : ℝ) ≤ (ordinaryLaw src).toFiniteLaw.prob (· ∈ O)) :
    H+a ≤ Compression.restrictionD
      (fun (u : Fin n × src.inner.Label) c =>
        T src R₀ u.2 (src.outer.decode c.1 (e u.1)))
      (rowRectangle Finset.univ Rows) O := by
  have hwiseD := dwise_comp_injective D
    (ordinaryLaw src).toFiniteLaw
    ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
    (fun c (i : Fin s) => src.outer.decode c.1 i)
    (ordinary_dwise src) e he
  have hwise8 : IsDWise 8 (ordinaryLaw src).toFiniteLaw
      (fun c (i : Fin n) => src.outer.decode c.1 (e i))
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw := by
    intro C hC E
    exact hwiseD C (hC.trans hD) E
  have hcount' : 2^(a-1)+1 ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa using hcount
  have hrow' : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      (2 : ℝ)^a*x ≤ src.inner.law.toFiniteLaw.prob (· ∈ Rows i) := by
    intro i _
    exact hrow i
  exact V38Fin2Exact.exactboost src.inner.law
    ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law)
    (T src R₀) (ordinaryLaw src).toFiniteLaw
    (fun c (i : Fin n) => src.outer.decode c.1 (e i))
    hwise8 Finset.univ Rows O H a x ha hH hx hscale hprofile
    hcount' hrow' hO

theorem selected_ordinary_original_lower
    (R₀ : X → Y → Bool)
    (M : Rw → ((src.outer.Label × src.gamma.Label) ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → src.inner.Label)
    (hordinary : ∀ r c, M r (.inl c) =
      T src R₀ (selector r) (src.outer.decode c.1 (bin r)))
    (H a n : ℕ) (x : ℝ)
    (hD : 8 ≤ D) (ha : 1 ≤ a) (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : (2 : ℝ)^a * x ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x (H : ℤ))
    (e : Fin n → Fin s) (he : Function.Injective e)
    (hcount : 2^(a-1)+1 ≤ n)
    (R : Set Rw) (O : Set (src.outer.Label × src.gamma.Label))
    (hrow : ∀ i : Fin n, (2 : ℝ)^a*x ≤
      src.inner.law.toFiniteLaw.prob
        (fun z => ∃ r ∈ R, bin r = e i ∧ selector r = z))
    (hO : (9/25 : ℝ) ≤ (ordinaryLaw src).toFiniteLaw.prob (· ∈ O)) :
    H+a ≤ Compression.restrictionD M R (Sum.inl '' O) := by
  classical
  let Rows : Fin n → Set src.inner.Label :=
    fun i z => ∃ r ∈ R, bin r = e i ∧ selector r = z
  have hl := selected_ordinary_exact_lower src R₀ H a n x hD ha hH hx
    hscale hprofile e he hcount Rows (by intro i; exact hrow i) O hO
  let f : Fin n × src.inner.Label → Rw := fun u =>
    if h : ∃ r ∈ R, bin r = e u.1 ∧ selector r = u.2 then
      Classical.choose h else Classical.choice inferInstance
  have hf : ∀ u ∈ rowRectangle Finset.univ Rows,
      f u ∈ R ∧ bin (f u) = e u.1 ∧ selector (f u) = u.2 := by
    intro u hu
    have hex : ∃ r ∈ R, bin r = e u.1 ∧ selector r = u.2 := by
      simpa only [rowRectangle, Finset.mem_univ, true_and, Rows] using hu
    simpa [f, hex] using Classical.choose_spec hex
  have hmap : Compression.restrictionD
      (fun (u : Fin n × src.inner.Label) c =>
        T src R₀ u.2 (src.outer.decode c.1 (e u.1)))
      (rowRectangle Finset.univ Rows) O ≤
      Compression.restrictionD M R (Sum.inl '' O) := by
    have heq : Compression.restrictionD
        (fun (u : Fin n × src.inner.Label) c =>
          T src R₀ u.2 (src.outer.decode c.1 (e u.1)))
        (rowRectangle Finset.univ Rows) O =
        Compression.restrictionD (fun u c => M (f u) (.inl c))
          (rowRectangle Finset.univ Rows) O := by
      unfold Compression.restrictionD
      congr 1
      funext u c
      have hs := hf u.val u.property
      change T src R₀ u.val.2 (src.outer.decode c.val.1 (e u.val.1)) =
        M (f u.val) (.inl c.val)
      rw [hordinary (f u.val) c.val, hs.2.1, hs.2.2]
    have h := restrictionD_map_le M f Sum.inl R (Sum.inl '' O)
      (rowRectangle Finset.univ Rows) O
      (fun u hu => (hf u hu).1)
      (by intro c hc; exact ⟨c, hc, rfl⟩)
    rw [heq]
    exact h
  exact hl.trans hmap

theorem paired_original_parent_lower
    (R₀ : X → Y → Bool)
    (M : Rw → ((src.outer.Label × src.gamma.Label) ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → src.inner.Label)
    (ψ : F → J src) (star : Fin s)
    (ι : E → Rw) (ζ : E → src.inner.Label × src.inner.Label)
    (hordinary : ∀ r c, M r (.inl c) =
      T src R₀ (selector r) (src.outer.decode c.1 (bin r)))
    (P : Set E) (R : Set Rw)
    (O : Set (src.outer.Label × src.gamma.Label)) (G : Set F)
    (hstar : ∀ a ∈ P, bin (ι a) = star ∧ selector (ι a) = (ζ a).1)
    (hforeign : ∀ a ∈ P, ∀ f,
      M (ι a) (.inr f) = T src R₀ (ζ a).2 (ψ f))
    (hι : ∀ a ∈ P, ι a ∈ R)
    (H ell : ℕ) (hH : 2 ≤ H) (hq : q₂ = 2^ell)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (ε δ : ℝ)
    (hK : (49/64 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
        (· ∈ ζ '' P))
    (hO : 1-ε ≤
      (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (· ∈ (fun c => src.outer.decode c.1 star) '' O))
    (hF : δ ≤
      (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (· ∈ ψ '' G))
    (hδpos : 0 < δ) (hδ : δ ≤ 1)
    (hsmall : 2*q₂*x ≤ 1/8)
    (hε : 0 ≤ ε) (hslack : 2*q₂*x+ε < δ) :
    H+ell+1 ≤ Compression.restrictionD M R
      ((Sum.inl '' O) ∪ (Sum.inr '' G)) := by
  have hl := V39PairedObstruction.paired_restriction_lower src R₀ H ell hH hq x hx hD
    hprofile (ζ '' P)
    ((fun c => src.outer.decode c.1 star) '' O) (ψ '' G)
    ε δ hK hO hF hδpos hδ hsmall hε hslack
  exact hl.trans (paired_original_D_le src R₀ M bin selector ψ star ι ζ
    hordinary P R O G hstar hforeign hι)

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
    (hO : (3/4 : ℝ) < (ordinaryLaw src).toFiniteLaw.prob (· ∈ O))
    (H a r : ℕ) (hr : r ≤ a) (hH : 2 ≤ H) (x : ℝ) (hx : 0 < x)
    (hD : 8 ≤ D) (hs : s = 2^a)
    (hsmall : SourceSupportSchedule.floor s x 0 ≤ 1/8)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (T src R₀)
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
    exists_dense_child (ordinaryLaw src).toFiniteLaw O
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

theorem generated_run_live_stops
    (R₀ : X → Y → Bool) (H a : ℕ) (hH : 1 ≤ H)
    (hs : s = 2^a) (x : ℝ) (hx : 0 ≤ x) (hD : 1 ≤ D)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x (H : ℤ))
    (O : Set (src.outer.Label × src.gamma.Label))
    (hO : (3/5 : ℝ) ≤ (ordinaryLaw src).toFiniteLaw.prob (· ∈ O))
    (σ : Fin s → Raw → src.inner.Label)
    (input : Fin s → Raw → C)
    (col : (src.outer.Label × src.gamma.Label) → B)
    (initial : State B C (Fin s) Raw)
    (hP : ∀ i ∈ initial.coordinates, ∀ w ∈ initial.support i,
      ∀ c ∈ O, initial.protocol.eval (col c) (input i w) =
        T src R₀ (σ i w) (src.outer.decode c.1 i))
    (hcost : initial.protocol.cost ≤ H+a)
    (hmass : ∀ i ∈ initial.coordinates,
      SourceSupportSchedule.floor s x 0 ≤
        ProjectedSupportStep.mass src.inner.law.toFiniteLaw (σ i)
          (initial.support i))
    (hreaches : ∀ i ∈ initial.coordinates, ∀ w ∈ initial.support i,
      input i w ∈ initial.columns) :
    let K := runScheduled src.inner.law.toFiniteLaw σ input
      (SourceSupportSchedule.floor s x) 0 (a+1) initial
    ∀ v : K.Leaves, (K.state v).coordinates.Nonempty →
      H ≤ (K.state v).protocol.cost ∧ (K.route v).length ≤ a ∧
      ∃ query left right,
        (K.state v).protocol = Protocol.aNode query left right := by
  classical
  let floor := SourceSupportSchedule.floor s x
  let K := runScheduled src.inner.law.toFiniteLaw σ input floor 0 (a+1) initial
  change ∀ v : K.Leaves, (K.state v).coordinates.Nonempty →
    H ≤ (K.state v).protocol.cost ∧ (K.route v).length ≤ a ∧
    ∃ query left right,
      (K.state v).protocol = Protocol.aNode query left right
  intro v hv
  obtain ⟨i, hi⟩ := hv
  have hp := runScheduled_bobPath src.inner.law.toFiniteLaw σ input floor 0 (a+1) initial v
  have hstop := runScheduled_stopping src.inner.law.toFiniteLaw σ input floor 0 (a+1) initial v
  change (K.route v).length ≤ a+1 ∧
    ((K.route v).length = a+1 ∨ SourceSupportFrontier.NonBob (K.state v).protocol) at hstop
  have hm := runScheduled_floor src.inner.law.toFiniteLaw σ input floor
    (fun r => (SourceSupportSchedule.twice_next s x r).symm)
    0 (a+1) initial hmass v
  have hr := runScheduled_support_reaches src.inner.law.toFiniteLaw σ input floor 0 (a+1)
    initial hreaches v
  have hsets := runScheduled_sets_subset src.inner.law.toFiniteLaw σ input floor 0 (a+1)
    initial v
  have hfloor : x ≤ floor (K.route v).length := by
    have hf := SourceSupportSchedule.threshold_le_floor hx hstop.1
    simpa only [floor, hs] using hf
  have hrow : x ≤ ProjectedSupportStep.mass src.inner.law.toFiniteLaw
      (σ i) ((K.state v).support i) := by
    exact hfloor.trans (by simpa only [zero_add] using hm i hi)
  have hlower : H ≤ (K.state v).protocol.cost := by
    apply V39TwoStreamScalarCost.one_bin_cost src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      (ordinaryLaw src).toFiniteLaw (T src R₀) H x hprofile (σ i)
      (fun c => src.outer.decode c.1 i)
      (ordinary_coordinate_pushes src hD i)
      ((K.state v).support i) O hrow hO (input i) col
      (K.state v).protocol
    intro w hw c hc
    have hreach := hr i hi w hw
    exact (hp.eval_eq (col c) (input i w) hreach).trans
      (hP i (hsets.1 hi) w (hsets.2.2 i hw) c hc)
  have hdepth : (K.route v).length ≤ a := by
    have hbudget := hp.cost_add_length
    change (K.state v).protocol.cost + (K.route v).length ≤ initial.protocol.cost at hbudget
    omega
  have hnb : SourceSupportFrontier.NonBob (K.state v).protocol :=
    hstop.2.resolve_left (by omega)
  refine ⟨hlower, hdepth, ?_⟩
  cases he : (K.state v).protocol with
  | leaf value =>
      simp only [he, Protocol.cost] at hlower
      omega
  | aNode query left right => exact ⟨query, left, right, rfl⟩
  | bNode query left right =>
      simp only [he, SourceSupportFrontier.NonBob] at hnb

end CurrentAdditive.V39TwoStreamTerminals

#print axioms CurrentAdditive.V39TwoStreamScalarCost.one_bin_cost
#print axioms CurrentAdditive.V39TwoStreamTerminals.ordinary_density
#print axioms CurrentAdditive.V39TwoStreamTerminals.exists_dense_child
#print axioms CurrentAdditive.V39TwoStreamTerminals.selected_ordinary_exact_lower
#print axioms CurrentAdditive.V39TwoStreamTerminals.selected_ordinary_original_lower
#print axioms CurrentAdditive.V39TwoStreamTerminals.paired_original_parent_lower
#print axioms CurrentAdditive.V39TwoStreamTerminals.ordinary_node_forces_one
#print axioms CurrentAdditive.V39TwoStreamTerminals.generated_run_live_stops
