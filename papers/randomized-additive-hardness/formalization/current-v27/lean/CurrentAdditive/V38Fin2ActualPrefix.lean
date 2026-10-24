import CurrentAdditive.V38Fin2Exact
import CurrentAdditive.V38Matrix
import Paper2.SourceProjection

/-!
Private v38 common-prefix component. The protocol below runs on the actual
two-family tagged column carrier. The complete raw-column source is used only
as a probability space for proving that a retained ordinary projection has
sufficient original-law mass; it does not replace the protocol's alphabet.
-/

namespace CurrentAdditive.V38Fin2ActualPrefix

open Paper2 Workspace.Types.Protocol

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  {q₁ q₂ t : ℕ} [NeZero q₂] [NeZero (2^t)]

private theorem positive_mass_nonempty {A : Type*} [Fintype A]
    (law : FiniteLaw A) (U : Set A)
    (h : 0 < law.prob (· ∈ U)) : U.Nonempty := by
  by_contra hn
  have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  subst U
  simp at h

/-- Full-product ordinary columns have the exact eight-wise tuple law on
the complete outer labels. The unused tail remains in the source carrier. -/
theorem raw_bin_eight_wise (ν : PositiveRationalLaw Y) :
    IsDWise 8 (SourceLaws.rawLaw ν q₁ q₂ (2^t)).toFiniteLaw
      (fun Z (p : Fin (2^t)) => Z.2 p)
      (SourceLaws.outerLaw ν q₁ q₂ (2^t)).toFiniteLaw := by
  intro S _ E
  rw [SourceLaws.rawLaw, PositiveRationalLaw.toFiniteLaw_prod]
  change (((ν.iid (2^t + 1)).toFiniteLaw.prod
      ((SourceLaws.outerLaw ν q₁ q₂ (2^t)).iid (2^t)).toFiniteLaw).prob
        (fun Z => E (fun p : S => Z.2 p.val))) = _
  rw [FiniteLaw.prod_prob_snd (ν.iid (2^t + 1)).toFiniteLaw
    ((SourceLaws.outerLaw ν q₁ q₂ (2^t)).iid (2^t)).toFiniteLaw
    (fun js => E (fun p : S => js p.val))]
  rw [PositiveRationalLaw.toFiniteLaw_iid]
  exact FiniteLaw.pi_prob_restrict
    (fun _ : Fin (2^t) => (SourceLaws.outerLaw ν q₁ q₂ (2^t)).toFiniteLaw)
    (fun p : S => p.val) Subtype.val_injective E

/-- A retained event of mass above 99/100 in the actual two-tag law gives
the ordinary family enough *unconditioned* source mass for separation. -/
theorem ordinary_retained_mass
    (ν : PositiveRationalLaw Y)
    (V : Set (V38Matrix.TaggedColumn q₁ q₂ (2^t) Y))
    (hV : (99/100 : ℝ) <
      (V38Matrix.taggedLaw (q₁ := q₁) (q₂ := q₂) (s := 2^t) ν).toFiniteLaw.prob
        (· ∈ V)) :
    (18/25 : ℝ) ≤
      (SourceLaws.rawLaw ν q₁ q₂ (2^t)).toFiniteLaw.prob
        (fun Z => (Sum.inl Z : V38Matrix.TaggedColumn q₁ q₂ (2^t) Y) ∈ V) := by
  have htag := V38Matrix.tagged_prob (q₁ := q₁) (q₂ := q₂)
    (s := 2^t) ν (fun Z => Z ∈ V)
  have hdiag :
      (SourceLaws.outerLaw ν q₁ q₂ (2^t)).toFiniteLaw.prob
        (fun j => (Sum.inr j : V38Matrix.TaggedColumn q₁ q₂ (2^t) Y) ∈ V) ≤ 1 :=
    FiniteLaw.prob_le_one _ _
  linarith

/-- The selected v38 full-product proof projects all bins together and
forgets only the tail. Its mass is measured under the original iid outer
law. Every tuple in this image has a surviving ordinary completion, chosen
independently of any template row. -/
theorem whole_bin_image_and_representatives
    (ν : PositiveRationalLaw Y)
    (K : Set (SourceMatrix.RawColumn q₁ q₂ (2^t) Y))
    (hK : (99/100 : ℝ) <
      (SourceLaws.rawLaw ν q₁ q₂ (2^t)).toFiniteLaw.prob (· ∈ K)) :
    (99/100 : ℝ) <
      ((SourceLaws.outerLaw ν q₁ q₂ (2^t)).iid (2^t)).toFiniteLaw.prob
        (· ∈ SourceProjection.rawBinProjection id '' K) ∧
      ∀ js : SourceProjection.rawBinProjection id '' K,
        ∃ Z ∈ K, SourceProjection.rawBinProjection id Z = js.val := by
  have himage := SourceProjection.raw_projection_mass ν
    (e := id) (he := Function.injective_id) K
  constructor
  · exact lt_of_lt_of_le hK himage
  · intro js
    exact js.property

/-- The first `t` nodes of the actual retained protocol are Alice nodes.
The exact block bound is the separate v38 `det:exact` obligation under its
two-threshold profile. The mass requirement on ordinary columns follows from
the actual retained two-tag law, and correctness is required only for the
given protocol on its own retained subtypes. -/
theorem actual_retained_forced_prefix
    (μ : PositiveRationalLaw (SourceMatrix.Template q₁ q₂ X))
    (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin (2^t)))
    (ξ₀ : SourceMatrix.Tail (2^t) Y)
    (U : Set (SourceMatrix.RawRow q₁ q₂ (2^t) X I))
    (V : Set (V38Matrix.TaggedColumn q₁ q₂ (2^t) Y))
    (P : Protocol U V Bool)
    (d : ℕ) (ρ z : ℝ)
    (_ht : 1 ≤ t) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hscale : (2 : ℝ)^t * ρ ≤ 1)
    (hblock : V38Fin2Prefix.ExactBlockBound μ (SourceMatrix.T R)
      (SourceLaws.rawLaw ν q₁ q₂ (2^t)).toFiniteLaw
      (fun Z p => Z.2 p) d ρ)
    (hrow : ∀ p : Fin (2^t), z ≤ μ.toFiniteLaw.prob
      (fun x => (Sum.inl (p,x) : SourceMatrix.RawRow q₁ q₂ (2^t) X I) ∈ U))
    (hgap : 2 * (2 : ℝ)^t * ρ < z)
    (hV : (99/100 : ℝ) <
      (V38Matrix.taggedLaw (q₁ := q₁) (q₂ := q₂) (s := 2^t) ν).toFiniteLaw.prob
        (· ∈ V))
    (hcost : P.cost ≤ d+t)
    (hcompute : P.Computes (fun a c =>
      SourceMatrix.raw R activity a.1
        (V38Matrix.forgetTag ξ₀ c.1))) :
    SourceProtocolPrefixTree.CompleteAlicePrefix t P := by
  classical
  let K : Set (SourceMatrix.RawColumn q₁ q₂ (2^t) Y) :=
    {Z | (Sum.inl Z : V38Matrix.TaggedColumn q₁ q₂ (2^t) Y) ∈ V}
  have hK : (18/25 : ℝ) ≤
      (SourceLaws.rawLaw ν q₁ q₂ (2^t)).toFiniteLaw.prob (· ∈ K) :=
    ordinary_retained_mass ν V hV
  have hKne : K.Nonempty := positive_mass_nonempty _ K
    (lt_of_lt_of_le (by norm_num) hK)
  have hz : 0 < z := by
    have hp : 0 < (2 : ℝ) * (2 : ℝ)^t * ρ := by positivity
    linarith
  let p₀ : Fin (2^t) := ⟨0, Nat.two_pow_pos t⟩
  have hUne : U.Nonempty := by
    have hp : 0 < μ.toFiniteLaw.prob
        (fun x => (Sum.inl (p₀,x) : SourceMatrix.RawRow q₁ q₂ (2^t) X I) ∈ U) :=
      lt_of_lt_of_le hz (hrow p₀)
    obtain ⟨x,hx⟩ := positive_mass_nonempty μ.toFiniteLaw _ hp
    exact ⟨.inl (p₀,x),hx⟩
  let u₀ : U := ⟨hUne.choose,hUne.choose_spec⟩
  let v₀ : V := ⟨.inl hKne.choose,hKne.choose_spec⟩
  let φ : (Fin (2^t) × SourceMatrix.Template q₁ q₂ X) → U :=
    fun a => if h : (Sum.inl a : SourceMatrix.RawRow q₁ q₂ (2^t) X I) ∈ U
      then ⟨.inl a,h⟩ else u₀
  let ψ : SourceMatrix.RawColumn q₁ q₂ (2^t) Y → V :=
    fun Z => if h : (Sum.inl Z : V38Matrix.TaggedColumn q₁ q₂ (2^t) Y) ∈ V
      then ⟨.inl Z,h⟩ else v₀
  let Pfull : Protocol
      (Fin (2^t) × SourceMatrix.Template q₁ q₂ X)
      (SourceMatrix.RawColumn q₁ q₂ (2^t) Y) Bool :=
    NPCC.Protocol.pullback φ ψ P
  let Rows : Fin (2^t) → Set (SourceMatrix.Template q₁ q₂ X) :=
    fun p => {x | (Sum.inl (p,x) : SourceMatrix.RawRow q₁ q₂ (2^t) X I) ∈ U}
  have hcost' : Pfull.cost ≤ d+t := by simpa [Pfull] using hcost
  have heval : ∀ p : Fin (2^t), ∀ x ∈ Rows p, ∀ Z ∈ K,
      Pfull.eval (p,x) Z = SourceMatrix.T R x (Z.2 p) := by
    intro p x hx Z hZ
    have hmemU : (Sum.inl (p,x) : SourceMatrix.RawRow q₁ q₂ (2^t) X I) ∈ U := hx
    have hmemV : (Sum.inl Z : V38Matrix.TaggedColumn q₁ q₂ (2^t) Y) ∈ V := hZ
    have hφ : φ (p,x) = ⟨.inl (p,x),hx⟩ := by simp [φ,hmemU]
    have hψ : ψ Z = ⟨.inl Z,hZ⟩ := by simp [ψ,hmemV]
    simp only [Pfull, NPCC.Protocol.pullback_eval, hφ, hψ]
    rw [hcompute ⟨.inl (p,x),hx⟩ ⟨.inl Z,hZ⟩]
    rfl
  have hp := V38Fin2Prefix.complete_alice_prefix
    μ (SourceMatrix.T R)
    (SourceLaws.rawLaw ν q₁ q₂ (2^t)).toFiniteLaw
    (fun Z p => Z.2 p)
    (Finset.univ : Finset (Fin (2^t))) Rows K d t ρ z hd hρ
    hscale hblock (by simp) (by simpa [Rows] using hrow)
    hgap hK Pfull hcost' (by intro i _ x hx Z hZ; exact heval i x hx Z hZ)
  exact (SourceProtocolPrefixTree.complete_pullback_iff φ ψ t P).mp hp

#print axioms raw_bin_eight_wise
#print axioms ordinary_retained_mass
#print axioms whole_bin_image_and_representatives
#print axioms actual_retained_forced_prefix

/-- Current two-threshold form on the actual retained two-family source.
The template width `q₁` is arbitrary, so the manuscript's `q₁=2^t-2`
specialises directly.  `hprofile` is the literal base restriction profile;
the exact-block theorem is proved internally from that profile. -/
theorem actual_two_threshold_forced_prefix
    (μ : PositiveRationalLaw (SourceMatrix.Template q₁ q₂ X))
    (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin (2^t)))
    (ξ₀ : SourceMatrix.Tail (2^t) Y)
    (U : Set (SourceMatrix.RawRow q₁ q₂ (2^t) X I))
    (V : Set (V38Matrix.TaggedColumn q₁ q₂ (2^t) Y))
    (P : Protocol U V Bool)
    (d : ℕ) (ρ z : ℝ)
    (ht : 1 ≤ t) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hscale : (2 : ℝ)^t*ρ ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (SourceMatrix.T R)
      μ.toFiniteLaw (SourceLaws.outerLaw ν q₁ q₂ (2^t)).toFiniteLaw ρ (d : ℤ))
    (hrow : ∀ p : Fin (2^t), z ≤ μ.toFiniteLaw.prob
      (fun x => (Sum.inl (p,x) : SourceMatrix.RawRow q₁ q₂ (2^t) X I) ∈ U))
    (hgap : 2*(2 : ℝ)^t*ρ < z)
    (hV : (99/100 : ℝ) <
      (V38Matrix.taggedLaw (q₁ := q₁) (q₂ := q₂) (s := 2^t) ν).toFiniteLaw.prob (· ∈ V))
    (hcost : P.cost ≤ d+t)
    (hcompute : P.Computes (fun a c => SourceMatrix.raw R activity a.1
      (V38Matrix.forgetTag ξ₀ c.1))) :
    SourceProtocolPrefixTree.CompleteAlicePrefix t P := by
  exact actual_retained_forced_prefix μ ν R activity ξ₀ U V P d ρ z ht hd hρ
    hscale (V38Fin2Exact.exactBlockBound_of_twoThreshold μ
      (SourceLaws.outerLaw ν q₁ q₂ (2^t)) (SourceMatrix.T R)
      (SourceLaws.rawLaw ν q₁ q₂ (2^t)).toFiniteLaw (fun Z p => Z.2 p)
      (raw_bin_eight_wise ν) d ρ hd hρ hprofile)
    hrow hgap hV hcost hcompute

#print axioms actual_two_threshold_forced_prefix

end CurrentAdditive.V38Fin2ActualPrefix
