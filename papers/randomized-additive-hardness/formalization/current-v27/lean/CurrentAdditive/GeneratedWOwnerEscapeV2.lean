import CurrentAdditive.GeneratedWCopyEscape

/-! An actual short W node cannot retain a near-full indexed N copy. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.ReferenceCertificateTree
  Workspace.Types.CommComplexity

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux] [Fintype X] [Fintype Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux]
  [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s w : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂)
    (s := s) μX μY)

/-- Source near-full applied to the original-index projection of one
complete-stream W node, then converted to physical protected escape. -/
theorem indexed_owner_escape_of_good_singleton_image
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    (streams : InternalStreams src μI w)
    (R : X → Y → Bool)
    (activity : G × (V ⊕ Aux) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (C : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hnear : ∀ (U : Set (Column src))
      (V : Set (Row (I := G × (V ⊕ Aux)) src)),
      1-η ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U) →
      1-η ≤ (rowLaw src μI).toFiniteLaw.prob (· ∈ V) →
      C ≤ Paper2.Compression.restrictionD (N src R activity ξ₀) U V)
    {B J Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (input : J → Ω → Fin w × Column src)
    (floor : ℕ → ℝ) (depth fuel : ℕ)
    (state : State (Fin w × Column src) B J Ω)
    (v : (run μ input floor depth fuel state).Leaves)
    (i : Fin w)
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (hImage : 1-η/2 ≤ (rowLaw src μI).toFiniteLaw.prob
      (· ∈ (fun t => InternalStreams.decode src streams t i) '' Yevent))
    (hcost : Paper2.Compression.restrictionD
      (W src streams R activity ξ₀) Yevent
      ((run μ input floor depth fuel state).state v).rows < C) :
    η < (127/128 : ℝ) *
      (1 - (ordinaryLaw src).toFiniteLaw.prob
        (fun z => (i,Column.ordinary z) ∈
          ((run μ input floor depth fuel state).state v).rows)) +
      protectedDeleted src state.rows i +
      protectedOutgoing src μ input floor depth fuel state v i := by
  classical
  let U : Set (Column src) :=
    {Z | (i,Z) ∈ ((run μ input floor depth fuel state).state v).rows}
  let Vrows : Set (Row (I := G × (V ⊕ Aux)) src) :=
    (fun t => InternalStreams.decode src streams t i) '' Yevent
  have hVmass : 1-η ≤ (rowLaw src μI).toFiniteLaw.prob (· ∈ Vrows) := by
    dsimp [Vrows]
    linarith
  have hUbad : (columnLaw src).toFiniteLaw.prob (· ∈ U) < 1-η := by
    by_contra hn
    push Not at hn
    have hlow := hnear U Vrows hn hVmass
    have hmap := indexed_copy_restriction_le_W src μI streams R activity ξ₀
      Yevent ((run μ input floor depth fuel state).state v).rows i
    dsimp [U, Vrows] at hlow hmap
    omega
  have hid := protected_missing_identity src μ input floor depth fuel state v i
  dsimp [U] at hUbad
  linarith

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_owner_escape_of_good_singleton_image
