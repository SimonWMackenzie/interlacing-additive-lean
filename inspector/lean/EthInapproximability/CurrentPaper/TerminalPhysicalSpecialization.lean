import EthInapproximability.CurrentPaper.TerminalOuterBound
import EthInapproximability.CurrentPaper.TerminalPhysicalPairs

/-!
# The outer two-stream bound on actual protected inputs

Source: frozen v8 `A-stage4-details.tex`, `lem:paper-terminal-two-stream`,
the fixed joint representatives and the paragraph "The outer interlace".

The marker supports below are actual columns in the original rectangle.
Reference rows are chosen once from their common tuple image, additional
rows once from their selected-coordinate image, and joint columns once from
actual surviving pairs followed by their common completion. No local
communication lower bound is a field of this construction.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.TerminalPhysicalSpecialization

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Workspace.Types.Protocol
open Construction JointTransfer TerminalOuterBound ProtocolSeparation

/-- Choose from the actual original rows on the image. The fallback is
irrelevant to every evaluation on the retained reference/additional domain. -/
def imageSection {A B : Type*} [DecidableEq B]
    (rows : Finset A) (f : A → B) (fallback : A) (b : B) : A :=
  if hb : b ∈ rows.image f then selectedRowSection rows f ⟨b, hb⟩ else fallback

theorem imageSection_mem {A B : Type*} [DecidableEq B]
    (rows : Finset A) (f : A → B) (fallback : A) (b : B)
    (hb : b ∈ rows.image f) : imageSection rows f fallback b ∈ rows := by
  rw [imageSection, dif_pos hb]
  exact selectedRowSection_mem rows f ⟨b, hb⟩

theorem imageSection_apply {A B : Type*} [DecidableEq B]
    (rows : Finset A) (f : A → B) (fallback : A) (b : B)
    (hb : b ∈ rows.image f) : f (imageSection rows f fallback b) = b := by
  rw [imageSection, dif_pos hb]
  exact selectedRowSection_apply rows f ⟨b, hb⟩

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- Every ordinary support uses an actual original column whose selected
physical coordinate lies in the specified template bin. -/
def ordinarySupport (s L nv nb Q : ℕ) (i : Fin Q)
    (S : Finset (Fin Q → ProtectedRows s L nv nb X)) (p : Fin s) :
    Finset (Fin Q → ProtectedRows s L nv nb X) := by
  classical
  exact S.filter (fun y => y i ∈ templateBin s L nv nb p)

omit [Nonempty X] in
theorem ordinarySupport_subset (s L nv nb Q : ℕ) (i : Fin Q)
    (S : Finset (Fin Q → ProtectedRows s L nv nb X)) (p : Fin s) :
    ordinarySupport s L nv nb Q i S p ⊆ S := by
  classical
  exact Finset.filter_subset _ _

omit [Nonempty X] in
theorem ordinarySupport_bin (s L nv nb Q : ℕ) (i : Fin Q)
    (S : Finset (Fin Q → ProtectedRows s L nv nb X)) (p : Fin s)
    (y : Fin Q → ProtectedRows s L nv nb X)
    (hy : y ∈ ordinarySupport s L nv nb Q i S p) :
    y i ∈ templateBin s L nv nb p := by
  classical
  exact (Finset.mem_filter.mp hy).2

/-- The physical pair-density and routing margin in the manuscript imply
the precise quotient surplus consumed below. The template quotient is
regular; its use here incurs no balanced-sampler loss. -/
theorem physical_pair_surplus (s L nv nb r : ℕ)
    (hs : 0 < s) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (po pf : Fin s)
    (pairs : Finset (ProtectedRows s L nv nb X × ProtectedRows s L nv nb X))
    (hpairs : pairs ⊆ templateBin s L nv nb po ×ˢ templateBin s L nv nb pf)
    {alpha xT epsilon : ℝ}
    (hdensity : alpha ≤ (pairs.card : ℝ) /
      (L * Fintype.card (TemplateLabels s L nv nb X) : ℕ) ^ 2)
    (hepsilon : 0 ≤ epsilon)
    (hmargin : (49 / 64 : ℝ) ≤
      (alpha - (2 : ℝ) ^ (r + 1) * xT) / (1 + epsilon) ^ 2) :
    (49 / 64 : ℝ) * (L : ℝ) ^ 2 + L * threshold L xT r ≤
      ((pairs.image (fun z => (templateQuotient hL z.1, templateQuotient hL z.2))).card : ℝ) := by
  classical
  have h := regular_pair_initial_surplus hL
    (templateBin s L nv nb po) (templateBin s L nv nb pf)
    (templateQuotient hL) (templateQuotient hL)
    (template_regular s L nv nb hL po) (template_regular s L nv nb hL pf)
    (template_labels_pos s L nv nb hs hL hv hb)
    (template_bin_card s L nv nb po) (template_bin_card s L nv nb pf)
    pairs hpairs hdensity hepsilon hmargin
  convert h using 1
  unfold threshold
  ring

section Bound

variable (base : X → Y → Bool) (a s q L nv nb Q H m ell D2 r : ℕ)
    (ha : 0 < qOne a) (hs : 0 < s) (hL : 0 < L)
    (family : SecondFamily a q L X)
    (order : ItemOrder nv nb) (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    {x ε eps delta xT : ℝ}
    (inputs : PairInputs (Function.swap (firstMatrix base a s)) family H m ell x ε eps delta)
    (hsr : s = 2 ^ r) (hD2 : D2 + 1 = H + m + ell)
    (hD2pos : 2 ≤ D2) (hxT : 0 < xT) (heps : eps ≤ 1 / 5)
    (hscale : (2 : ℝ) ^ (r + 1) * xT ≤ 1)
    (hsecond : D2 ≤ Dfamily
      (interlaceFun (Function.swap (secondMatrix base a s q L family)) 1)
      (bracketGE (Fin L) (SecondRows a s q Y) 1 xT (3 / 5)))
    (hsecondHalf : D2 - 1 ≤ Dfamily
      (interlaceFun (Function.swap (secondMatrix base a s q L family)) 1)
      (bracketGE (Fin L) (SecondRows a s q Y) 1 xT (3 / 10)))
    (i j : Fin Q) (po pf : Fin s)
    (A : Finset (Fin Q × ProtectedColumns a s q Y))
    (S : Finset (Fin Q → ProtectedRows s L nv nb X))
    (Ao Af : Finset (ProtectedColumns a s q Y))
    (hAo : ∀ z ∈ Ao, (i, z) ∈ A) (hAf : ∀ z ∈ Af, (j, z) ∈ A)
    (hAoRef : Ao ⊆ referenceRows a s q) (hAfDiag : Af ⊆ diagonalRows a s q)
    (hAoDensity : 1 - eps ≤ (Ao.card : ℝ) / (referenceRows (Y := Y) a s q).card)
    (hAfDensity : delta ≤ (Af.card : ℝ) / (diagonalRows (Y := Y) a s q).card)
    (P' : Finset (ProtectedRows s L nv nb X × ProtectedRows s L nv nb X))
    (hP' : P' ⊆ templateBin s L nv nb po ×ˢ templateBin s L nv nb pf)
    (sigma : ProtectedRows s L nv nb X × ProtectedRows s L nv nb X →
      Fin Q → ProtectedRows s L nv nb X)
    (hsigma : ∀ z ∈ P', sigma z ∈ S ∧ sigma z i = z.1 ∧ sigma z j = z.2)
    (hpair : (49 / 64 : ℝ) * (L : ℝ) ^ 2 + L * threshold L xT r ≤
      ((P'.image (fun z => (templateQuotient hL z.1, templateQuotient hL z.2))).card : ℝ))
    (hordinary : ∀ p : Fin s, p ≠ po → threshold L xT r ≤
      (((ordinarySupport s L nv nb Q i S p).image
        (fun z => templateQuotient hL (z i))).card : ℝ))

include ha hs inputs hsr hD2 hD2pos hxT heps hscale hsecond hsecondHalf
  hAo hAf hAoRef hAfDiag hAoDensity hAfDensity hP' hsigma hpair hordinary

/-- The full selector contribution for an actual parent protocol. All
support premises concern actual original rows, columns and joint pairs.
The additional `log s` bits are derived, not supplied as a local bound. -/
theorem physical_outer_protocol_lower
    (P : Protocol (Fin Q × ProtectedColumns a s q Y)
      (Fin Q → ProtectedRows s L nv nb X) Bool)
    (hcompute : ∀ z ∈ A, ∀ y ∈ S, P.eval z y =
      interlaceFun (protectedMatrix base a s q L nv nb hs family order vectors cap) Q z y) :
    D2 + r + 1 ≤ P.cost := by
  classical
  letI : Nonempty (Fin (qOne a)) := Fin.pos_iff_nonempty.mp ha
  letI : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp inputs.qpos
  have hAoNe : Ao.Nonempty := by
    by_contra hn
    have he : Ao = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.card_empty, Nat.cast_zero, zero_div] at hAoDensity
    linarith
  let fallback := hAoNe.choose
  let C := Ao.image (selectorTuple (a := a) (s := s) (q := q))
  let F := Af.image (fun z => selectorTuple (a := a) (s := s) (q := q) z pf)
  let refMap : ThirdColumns a s q Y → (Fin Q × ProtectedColumns a s q Y) := fun c =>
    (i, imageSection Ao selectorTuple fallback c)
  let extraMap : SecondRows a s q Y → (Fin Q × ProtectedColumns a s q Y) := fun f =>
    (j, imageSection Af (fun z => selectorTuple z pf) fallback f)
  let quotient := templateQuotient (X := X) (s := s) (nv := nv) (nb := nb) hL
  let K := TerminalPhysicalPairs.quotientPairs P' quotient
  let Zpair := TerminalPhysicalPairs.support P' quotient sigma
  let supports : Fin s → Finset (Fin Q → ProtectedRows s L nv nb X) := fun p =>
    if p = po then Zpair else ordinarySupport s L nv nb Q i S p
  let π : Fin s → (Fin Q → ProtectedRows s L nv nb X) → Fin L :=
    fun _ z => quotient (z i)
  let ψ : (Fin Q → ProtectedRows s L nv nb X) → Fin L := fun z => quotient (z j)
  have hC : (1 - eps) * Fintype.card (ThirdColumns a s q Y) ≤ (C.card : ℝ) := by
    have hn : (0 : ℝ) < Fintype.card (ThirdColumns a s q Y) := by
      exact_mod_cast (Fintype.card_pos (α := ThirdColumns a s q Y))
    apply (le_div_iff₀ hn).mp
    exact hAoDensity.trans (reference_common_density a s q inputs.qpos Ao hAoRef)
  have hF : delta * Fintype.card (SecondRows a s q Y) ≤ (F.card : ℝ) := by
    have hn : (0 : ℝ) < Fintype.card (SecondRows a s q Y) := by
      exact_mod_cast (Fintype.card_pos (α := SecondRows a s q Y))
    apply (le_div_iff₀ hn).mp
    exact hAfDensity.trans (diagonal_selected_density a s q inputs.qpos pf Af hAfDiag)
  have hsigma' : ∀ z ∈ P', sigma z i = z.1 ∧ sigma z j = z.2 :=
    fun z hz => (hsigma z hz).2
  have hZsub : Zpair ⊆ S :=
    TerminalPhysicalPairs.support_subset P' quotient sigma S (fun z hz => (hsigma z hz).1)
  have hZbins : ∀ z ∈ Zpair,
      z i ∈ templateBin s L nv nb po ∧ z j ∈ templateBin s L nv nb pf :=
    fun z hz => TerminalPhysicalPairs.support_coordinates_mem P' quotient sigma i j hsigma'
      (templateBin s L nv nb po) (templateBin s L nv nb pf) hP' hz
  have hZcard : Zpair.card = K.card :=
    TerminalPhysicalPairs.support_card P' quotient sigma i j hsigma'
  have hpairMass : (49 / 64 : ℝ) * (L : ℝ) ^ 2 + L * threshold L xT r ≤
      (Zpair.card : ℝ) := by
    rw [hZcard]
    exact hpair
  have hwidth : ∀ p, threshold L xT r ≤ ((supports p).image (π p)).card := by
    intro p
    by_cases hp : p = po
    · subst p
      have hf := TerminalPhysicalPairs.quotientPairs_card_le_first_image
        P' quotient sigma i j hsigma'
      have hfR : (K.card : ℝ) ≤ (L : ℝ) *
          ((Zpair.image (fun z => quotient (z i))).card : ℝ) := by exact_mod_cast hf
      have hLR : (0 : ℝ) < L := by exact_mod_cast hL
      have hnonneg : 0 ≤ (49 / 64 : ℝ) * (L : ℝ) ^ 2 := by positivity
      simp only [supports, if_pos rfl, π]
      have hKmass : (49 / 64 : ℝ) * (L : ℝ) ^ 2 + L * threshold L xT r ≤
          (K.card : ℝ) := hpair
      nlinarith
    · simpa only [supports, π, if_neg hp] using hordinary p hp
  have hsupport : ∀ p, ∀ z ∈ supports p,
      z ∈ S ∧ z i ∈ templateBin s L nv nb p := by
    intro p z hz
    by_cases hp : p = po
    · subst p
      have hz' : z ∈ Zpair := by simpa only [supports, if_pos rfl] using hz
      exact ⟨hZsub hz', (hZbins z hz').1⟩
    · have hz' : z ∈ ordinarySupport s L nv nb Q i S p := by
        simpa only [supports, if_neg hp] using hz
      exact ⟨ordinarySupport_subset s L nv nb Q i S p hz',
        ordinarySupport_bin s L nv nb Q i S p z hz'⟩
  have ho : ∀ p, ∀ z ∈ supports p, ∀ c ∈ C,
      (Protocol.swap P).eval z (refMap c) =
        secondMatrix base a s q L family (c p) (π p z) := by
    intro p z hz c hc
    have hrowmem := imageSection_mem Ao selectorTuple fallback c hc
    have hrowval := imageSection_apply Ao selectorTuple fallback c hc
    rw [Protocol.eval_swap]
    rw [hcompute _ (hAo _ hrowmem) z (hsupport p z hz).1]
    change protectedMatrix base a s q L nv nb hs family order vectors cap
      (imageSection Ao selectorTuple fallback c) (z i) = _
    rw [protected_template_entry base a s q L nv nb hs hL family order vectors cap
      p (z i) (hsupport p z hz).2, hrowval]
  have hf : ∀ z ∈ supports po, ∀ f ∈ F,
      (Protocol.swap P).eval z (extraMap f) = secondMatrix base a s q L family f (ψ z) := by
    intro z hz f hf
    have hz' : z ∈ Zpair := by simpa only [supports, if_pos rfl] using hz
    have hrowmem := imageSection_mem Af (fun z => selectorTuple z pf) fallback f hf
    have hrowval := imageSection_apply Af (fun z => selectorTuple z pf) fallback f hf
    change selectorTuple (imageSection Af (fun z => selectorTuple z pf) fallback f) pf = f
      at hrowval
    rw [Protocol.eval_swap]
    rw [hcompute _ (hAf _ hrowmem) z (hZsub hz')]
    change protectedMatrix base a s q L nv nb hs family order vectors cap
      (imageSection Af (fun z => selectorTuple z pf) fallback f) (z j) = _
    rw [protected_template_entry base a s q L nv nb hs hL family order vectors cap
      pf (z j) (hZbins z hz').2, hrowval]
  have hinj : Set.InjOn (fun z => (π po z, ψ z)) ↑(supports po) := by
    simpa only [supports, if_pos rfl, π, ψ] using
      TerminalPhysicalPairs.quotient_injOn_support P' quotient sigma i j hsigma'
  have hmass : (49 / 64 : ℝ) * (L : ℝ) ^ 2 + L * threshold L xT r ≤
      ((supports po).card : ℝ) := by simpa only [supports, if_pos rfl] using hpairMass
  have hout := outer_protocol_lower (Function.swap (firstMatrix base a s)) family inputs
    hD2 hD2pos hxT hsecond hsecondHalf heps hsr hscale C F hC hF refMap extraMap π ψ
    (Protocol.swap P) supports po hwidth ho hf hinj hmass
  simpa only [Protocol.cost_swap] using hout

/-- The same physical construction lower-bounds the deterministic complexity
of the actual restricted interlaced matrix. A minimum-cost restricted
protocol is extended without changing its tree or its communication cost. -/
theorem physical_outer_subgame_lower :
    D2 + r + 1 ≤ D (subgame
      (interlaceFun (protectedMatrix base a s q L nv nb hs family order vectors cap) Q)
      A S) := by
  classical
  have hAoNe : Ao.Nonempty := by
    by_contra hn
    have he : Ao = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.card_empty, Nat.cast_zero, zero_div] at hAoDensity
    linarith
  obtain ⟨z, hz⟩ := hAoNe
  have hAne : A.Nonempty := ⟨(i, z), hAo z hz⟩
  have hPne : P'.Nonempty := by
    by_contra hn
    have he : P' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.image_empty, Finset.card_empty, Nat.cast_zero] at hpair
    have hthreshold : 0 < threshold L xT r := by unfold threshold; positivity
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    nlinarith [sq_pos_of_pos hLR]
  obtain ⟨pair, hpairmem⟩ := hPne
  have hSne : S.Nonempty := ⟨sigma pair, (hsigma pair hpairmem).1⟩
  let M := interlaceFun (protectedMatrix base a s q L nv nb hs family order vectors cap) Q
  have hm : D (subgame M A S) ∈ AchievableCosts (subgame M A S) :=
    Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty _)
  obtain ⟨P, hcost, hcomp⟩ := hm
  have hcomp' : ∀ z ∈ A, ∀ y ∈ S,
      (Protocol.extendSub A S hAne hSne P).eval z y = M z y := by
    intro z hz y hy
    rw [Protocol.eval_extendSub A S hAne hSne P ⟨z, hz⟩ ⟨y, hy⟩]
    exact hcomp ⟨z, hz⟩ ⟨y, hy⟩
  have hout := physical_outer_protocol_lower base a s q L nv nb Q H m ell D2 r
    ha hs hL family order vectors cap inputs hsr hD2 hD2pos hxT heps hscale
    hsecond hsecondHalf i j po pf A S Ao Af hAo hAf hAoRef hAfDiag hAoDensity hAfDensity
    P' hP' sigma hsigma hpair hordinary (Protocol.extendSub A S hAne hSne P) hcomp'
  simpa only [Protocol.cost_extendSub, hcost] using hout

end Bound

end EthInapproximability.CurrentPaper.TerminalPhysicalSpecialization
