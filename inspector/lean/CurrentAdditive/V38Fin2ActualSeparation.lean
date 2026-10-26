import CurrentAdditive.V38Fin2ActualPrefix
import CurrentAdditive.V38Fin2Separation

/-! Exact `cl:separation` on retained inputs of the actual two-family source.
The base template width is arbitrary and may be `s-2` as in v39. -/

namespace CurrentAdditive.V38Fin2ActualPrefix

open Paper2 Workspace.Types.Protocol

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  {q₁ q₂ t : ℕ} [NeZero q₂] [NeZero (2^t)]

/-- The actual template rows of block `p` that reach prefix part `w`.
The membership proof merely turns an actual retained row into its subtype;
no representative input is added to the protocol alphabet. -/
def retainedPrefixFibre
    {U : Set (SourceMatrix.RawRow q₁ q₂ (2^t) X I)}
    {V : Set (V38Matrix.TaggedColumn q₁ q₂ (2^t) Y)}
    (P : Protocol U V Bool) (p w : Fin (2^t)) : Set (SourceMatrix.Template q₁ q₂ X) :=
  {x | ∃ h : (Sum.inl (p,x) : SourceMatrix.RawRow q₁ q₂ (2^t) X I) ∈ U,
    NPCC.Protocol.prefixCodeRaw t P ⟨Sum.inl (p,x),h⟩ = w}

theorem actual_two_threshold_separation
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
    SourceProtocolPrefixTree.CompleteAlicePrefix t P ∧
    ∃ dom : Fin (2^t) ≃ Fin (2^t),
      (∀ w, z/(2 : ℝ)^t ≤ μ.toFiniteLaw.prob (· ∈ retainedPrefixFibre P (dom w) w)) ∧
      (∀ w j, j ≠ dom w → μ.toFiniteLaw.prob (· ∈ retainedPrefixFibre P j w) < 2*ρ) ∧
      (∀ w, z-2*((2^t : ℕ)-1 : ℕ)*ρ <
        μ.toFiniteLaw.prob (· ∈ retainedPrefixFibre P (dom w) w)) := by
  classical
  let K : Set (SourceMatrix.RawColumn q₁ q₂ (2^t) Y) :=
    {Z | (Sum.inl Z : V38Matrix.TaggedColumn q₁ q₂ (2^t) Y) ∈ V}
  have hK : (18/25 : ℝ) ≤
      (SourceLaws.rawLaw ν q₁ q₂ (2^t)).toFiniteLaw.prob (· ∈ K) :=
    ordinary_retained_mass ν V hV
  have hKne : K.Nonempty := by
    by_contra hn
    have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [he] at hK
    norm_num at hK
  have hz : 0 < z := by
    have hp : 0 < (2 : ℝ)*(2 : ℝ)^t*ρ := by positivity
    linarith
  let p₀ : Fin (2^t) := ⟨0,Nat.two_pow_pos t⟩
  have hUne : U.Nonempty := by
    have hp := hrow p₀
    by_contra hn
    have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [he] at hp
    linarith
  let u₀ : U := ⟨hUne.choose,hUne.choose_spec⟩
  let v₀ : V := ⟨.inl hKne.choose,hKne.choose_spec⟩
  let φ : (Fin (2^t) × SourceMatrix.Template q₁ q₂ X) → U :=
    fun a => if h : (Sum.inl a : SourceMatrix.RawRow q₁ q₂ (2^t) X I) ∈ U
      then ⟨.inl a,h⟩ else u₀
  let ψ : SourceMatrix.RawColumn q₁ q₂ (2^t) Y → V :=
    fun Z => if h : (Sum.inl Z : V38Matrix.TaggedColumn q₁ q₂ (2^t) Y) ∈ V
      then ⟨.inl Z,h⟩ else v₀
  let Pfull : Protocol (Fin (2^t) × SourceMatrix.Template q₁ q₂ X)
      (SourceMatrix.RawColumn q₁ q₂ (2^t) Y) Bool := NPCC.Protocol.pullback φ ψ P
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
    simp only [Pfull,NPCC.Protocol.pullback_eval,hφ,hψ]
    rw [hcompute ⟨.inl (p,x),hx⟩ ⟨.inl Z,hZ⟩]
    rfl
  have hblock := V38Fin2Exact.exactBlockBound_of_twoThreshold μ
    (SourceLaws.outerLaw ν q₁ q₂ (2^t)) (SourceMatrix.T R)
    (SourceLaws.rawLaw ν q₁ q₂ (2^t)).toFiniteLaw (fun Z p => Z.2 p)
    (raw_bin_eight_wise ν) d ρ hd hρ hprofile
  obtain ⟨hpref,dom,hmass,hsmall,hlarge⟩ := V38Fin2Prefix.dominant_prefix_parts
    μ (SourceMatrix.T R) (SourceLaws.rawLaw ν q₁ q₂ (2^t)).toFiniteLaw
    (fun Z p => Z.2 p) Rows K d ρ z ht hd hρ hscale hblock
    (by simpa [Rows] using hrow) hgap hK Pfull hcost' heval
  have hcode (p : Fin (2^t)) (x : SourceMatrix.Template q₁ q₂ X)
      (hx : (Sum.inl (p,x) : SourceMatrix.RawRow q₁ q₂ (2^t) X I) ∈ U) :
      NPCC.Protocol.prefixCodeRaw t Pfull (p,x) =
      NPCC.Protocol.prefixCodeRaw t P ⟨Sum.inl (p,x),hx⟩ := by
    simp only [Pfull,PrefixPullback.prefixCodeRaw_pullback]
    simp [φ,hx]
  have hfibre (p w : Fin (2^t)) :
      (fun x => x ∈ Rows p ∧ NPCC.Protocol.prefixCodeRaw t Pfull (p,x) = w) =
      (fun x => x ∈ retainedPrefixFibre P p w) := by
    funext x
    apply propext
    constructor
    · rintro ⟨hx,hw⟩
      exact ⟨hx,by rw [← hcode p x hx]; exact hw⟩
    · rintro ⟨hx,hw⟩
      exact ⟨hx,by rw [hcode p x hx]; exact hw⟩
  refine ⟨(SourceProtocolPrefixTree.complete_pullback_iff φ ψ t P).mp hpref,
    dom,?_,?_,?_⟩
  · intro w
    simpa only [hfibre] using hmass w
  · intro w j hj
    simpa only [hfibre] using hsmall w j hj
  · intro w
    simpa only [hfibre] using hlarge w

#print axioms actual_two_threshold_separation

end CurrentAdditive.V38Fin2ActualPrefix
