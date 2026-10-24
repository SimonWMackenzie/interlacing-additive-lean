import CurrentAdditive.DeterministicIndexedMatrix

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourceMatrix Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]

/-- Finite proof-only realization of all three exact source calls.
`chooseCodeSource` uses the rational cylinder theorem; no runtime follows. -/
noncomputable def chosenSources (μX : PositiveRationalLaw X)
    (μY : PositiveRationalLaw Y) :
    Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY := by
  let γ := chooseCodeSource D (q₁ + s + 1) μY
  let σ := chooseCodeSource D q₂
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX)
  let τ := chooseCodeSource D s
    ((PositiveRationalLaw.uniform (Fin q₂)).prod γ.law)
  exact ⟨γ, σ, τ⟩

namespace Sources

variable {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- The actual protocol on decoded index labels, obtained by reading the
visible data locally and running the previously checked YES protocol. -/
noncomputable def yesProtocol (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (P : Workspace.Types.Protocol.Protocol X Y Bool) :
    Workspace.Types.Protocol.Protocol (Row (I := I) src) (Column src) Bool :=
  Workspace.UpperBound.Protocol.comap (decodeRow src) (decodeColumn src ξ₀)
    (Paper2.SourceMatrix.yesProtocol (q₁ := q₁) assign activity P)

theorem yesProtocol_computes (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s))
    (hc : CollisionFree assign activity) (ξ₀ : Tail s Y)
    (R : X → Y → Bool) (P : Workspace.Types.Protocol.Protocol X Y Bool)
    (hP : P.Computes R) :
    (yesProtocol src assign activity ξ₀ P).Computes (B src R activity ξ₀) := by
  intro k Z
  rw [yesProtocol, Workspace.UpperBound.Protocol.comap_eval]
  exact Paper2.SourceMatrix.yesProtocol_computes assign activity hc R P hP
    (decodeRow src k) (decodeColumn src ξ₀ Z)

theorem yesProtocol_cost (assign : I → Fin s)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (P : Workspace.Types.Protocol.Protocol X Y Bool) :
    (yesProtocol src assign activity ξ₀ P).cost ≤
      Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + 2) + P.cost := by
  rw [yesProtocol, Workspace.UpperBound.Protocol.comap_cost]
  exact Paper2.SourceMatrix.yesProtocol_cost assign activity P

/-- The same indexed matrix has a universal upper protocol without a graph
colouring; this gives the one-bit NO-side ceiling. -/
noncomputable def universalProtocol (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (P : Workspace.Types.Protocol.Protocol X Y Bool) :
    Workspace.Types.Protocol.Protocol (Row (I := I) src) (Column src) Bool :=
  Workspace.UpperBound.Protocol.comap (decodeRow src) (decodeColumn src ξ₀)
    (Paper2.SourceMatrix.universalProtocol (q₁ := q₁) (fun _ : I => (0 : Fin s)) activity P)

theorem universalProtocol_computes (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (R : X → Y → Bool)
    (P : Workspace.Types.Protocol.Protocol X Y Bool) (hP : P.Computes R) :
    (universalProtocol src activity ξ₀ P).Computes (B src R activity ξ₀) := by
  intro k Z
  rw [universalProtocol, Workspace.UpperBound.Protocol.comap_eval]
  exact Paper2.SourceMatrix.universalProtocol_computes
    (fun _ : I => (0 : Fin s)) activity R P hP
      (decodeRow src k) (decodeColumn src ξ₀ Z)

theorem universalProtocol_cost (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (P : Workspace.Types.Protocol.Protocol X Y Bool) :
    (universalProtocol src activity ξ₀ P).cost ≤
      Nat.clog 2 s + Nat.clog 2 q₂ + Nat.clog 2 (q₁ + s + 1) + P.cost := by
  rw [universalProtocol, Workspace.UpperBound.Protocol.comap_cost]
  exact Paper2.SourceMatrix.universalProtocol_cost
    (fun _ : I => (0 : Fin s)) activity P

end Sources

end CurrentAdditive.DeterministicIndexedMatrix
