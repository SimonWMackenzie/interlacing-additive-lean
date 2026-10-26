import Paper2.ProtectedIncomingSource
import Paper2.ProtectedIncomingSelection
import Paper2.ProtectedIncomingDensity

/-!
# Actual incoming-mass failure to a selected original-node contradiction

This scratch composition retains the same physical protected row set,
original Items tuple event, and node protocol. The remaining physical-run
adapter must supply the node correctness/cost and failed incoming-mass
inequality from the actual reference run.
-/

namespace Paper2.ProtectedIncomingFromFailure

open ProtectedIncomingDensity ProtectedIncomingSelection ProtectedIncomingSource
open SourceMatrix SourceLaws SourceProfileParameters
open Workspace.Types.CommComplexity Workspace.Types.Protocol

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩

set_option maxRecDepth 4096 in
/-- A final original destination cannot receive the displayed large
protected incoming mass while its actual protocol has at most `C-1`
remaining bits. No high-density group, selected coordinates or column
selector-image law is assumed: all are derived from this failed bound. -/
theorem final_mass_failure_impossible
    {X Y Vtx : Type*} [Fintype X] [Fintype Y]
    [Fintype Vtx] [Nonempty Vtx]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hD : D base = d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) Vtx →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y)
    (w r Q C t : ℕ) (hw : w = 2 ^ r) (hQ : 0 < Q) (hC : 1 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (O : Set (Fin w → RawRow (width L - 2) (outerWidth L) (width L) X
      (SourceConstruction.Items (width L) Vtx)))
    (I : Finset (Fin w))
    (hY : RestorationCoverParameters.theta Q ≤
      (((SourceLawBinding.matrixColumnLaw (V := Vtx) μ
        (width L - 2) (outerWidth L) (width L)
        (SourceProfiles.width_ge_four L)).toFiniteLaw).iid w).prob (· ∈ O))
    (hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1)
    (hfailed : 1024 * (1 / 256 : ℝ) *
      RestorationCoverParameters.B2 Q * (r + 2) * width L * (2 ^ t : ℕ) ≤
      ∑ i ∈ I, ForeignOwnerMass.protectedMass ν L w i R)
    (P : Protocol R O Bool)
    (hP : P.Computes (fun row col =>
      fullInterlace (N base activity ξ₀) w row.val col.val))
    (hcost : P.cost ≤ C - 1) : False := by
  classical
  let B := RestorationCoverParameters.B2 Q
  let κ := 2 ^ t
  have hB : 0 < B := by
    dsimp [B, RestorationCoverParameters.B2]
    omega
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨b, hlarge, hDone, j, n, hVI, _, hδpos, hδone, hδlow,
    hrows, _, hsize, _, hroom, huw⟩ :=
    actual_density_group ν L w r B κ R I hw hB hκ hfailed
  let den := density ν L w R I b
  let D₀ : ℝ := ∑ i, den i
  let δ : ℝ := (1 / 2 : ℝ) ^ j.val
  let G := ProtectedDensityGroups.dyadicGroup den D₀ j
  let u := 2 ^ n
  have hwpos : 0 < w := by rw [hw]; positivity
  obtain ⟨e, he, heG, p, hcol⟩ :=
    final_dyadic_selection μ (SourceProfiles.width_ge_four L)
      Q n κ hQ hκ δ hδone hsize O G hroom hY
  have hk : 0 < 2 ^ (n - 1) := by positivity
  have hu : u = 2 * 2 ^ (n - 1) :=
    (dyadic_group_even n (width L) κ δ
      (by unfold width; positivity) hκ hδone hsize).2
  exact source_group_node_impossible μ ν base L d hd hD hp
    hinner houter hwide href activity ξ₀ w hwpos R O I G b hVI
    hk e heG p u t C hu huw hC hCeq δ D₀ hDone hδpos
    hδlow hsize hxsmall (fun i hi => (hrows i hi).1) hcol P hP (Or.inr hcost)

set_option maxRecDepth 4096 in
/-- At the actual first Bob query, the same failed protected mass selects
a charged original child whose remaining budget contradicts the source
row-ladder capacity. The child protocol is a restriction of the given
original node protocol, not an independently supplied certificate. -/
theorem bob_mass_failure_impossible
    {X Y Vtx : Type*} [Fintype X] [Fintype Y]
    [Fintype Vtx] [Nonempty Vtx]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hD : D base = d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) Vtx →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y)
    (w r Q C t : ℕ) (hw : w = 2 ^ r) (hQ : 0 < Q) (hC : 1 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (O : Set (Fin w → RawRow (width L - 2) (outerWidth L) (width L) X
      (SourceConstruction.Items (width L) Vtx)))
    (I : Finset (Fin w))
    (hY : RestorationCoverParameters.theta Q ≤
      (((SourceLawBinding.matrixColumnLaw (V := Vtx) μ
        (width L - 2) (outerWidth L) (width L)
        (SourceProfiles.width_ge_four L)).toFiniteLaw).iid w).prob (· ∈ O))
    (hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1)
    (hfailed : 1024 * (1 / 256 : ℝ) *
      RestorationCoverParameters.B2 Q * (r + 2) * width L * (2 ^ t : ℕ) ≤
      ∑ i ∈ I, ForeignOwnerMass.protectedMass ν L w i R)
    (query : (Fin w → RawRow (width L - 2) (outerWidth L) (width L) X
      (SourceConstruction.Items (width L) Vtx)) → Bool)
    (left right : Protocol R O Bool)
    (hP : (Protocol.bNode (fun y : O => query y.val) left right).Computes
      (fun row col => fullInterlace (N base activity ξ₀) w row.val col.val))
    (hcost : (Protocol.bNode (fun y : O => query y.val) left right).cost ≤
      C + t - 1) : False := by
  classical
  let B := RestorationCoverParameters.B2 Q
  let κ := 2 ^ t
  have hB : 0 < B := by dsimp [B, RestorationCoverParameters.B2]; omega
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨b, hlarge, hDone, j, n, hVI, _, hδpos, hδone, hδlow,
    hrows, _, hsize, _, hroom, huw⟩ :=
    actual_density_group ν L w r B κ R I hw hB hκ hfailed
  let den := density ν L w R I b
  let D₀ : ℝ := ∑ i, den i
  let δ : ℝ := (1 / 2 : ℝ) ^ j.val
  let G := ProtectedDensityGroups.dyadicGroup den D₀ j
  let u := 2 ^ n
  have hwpos : 0 < w := by rw [hw]; positivity
  obtain ⟨bchild, e, he, heG, p, hcol⟩ :=
    bob_child_dyadic_selection μ (SourceProfiles.width_ge_four L)
      Q n κ hQ hκ δ hδone hsize O G hroom hY query
  let Ochild := ReferenceColumnStep.columnChild O query bchild
  let child := if bchild then right else left
  let Qchild : Protocol R Ochild Bool :=
    Workspace.UpperBound.Protocol.comap (fun row : R => row)
      (fun col : Ochild => (⟨col.val, col.property.1⟩ : O)) child
  have hQ : Qchild.Computes (fun row col =>
      fullInterlace (N base activity ξ₀) w row.val col.val) := by
    intro row col
    rw [Workspace.UpperBound.Protocol.comap_eval]
    have heval := hP row ⟨col.val, col.property.1⟩
    have hb : query col.val = bchild := col.property.2
    cases bchild <;> simpa [Protocol.eval, hb, child] using heval
  have hchild : child.cost + 1 ≤
      (Protocol.bNode (fun y : O => query y.val) left right).cost := by
    dsimp only [child]
    cases bchild <;> simp only [Bool.false_eq_true, ↓reduceIte, Protocol.cost]
    · simpa only [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_max_left left.cost right.cost) 1
    · simpa only [Nat.add_comm] using
        Nat.add_le_add_right (Nat.le_max_right left.cost right.cost) 1
  have hQcost : Qchild.cost ≤ C + t - 2 := by
    rw [Workspace.UpperBound.Protocol.comap_cost]
    omega
  have hk : 0 < 2 ^ (n - 1) := by positivity
  have hu : u = 2 * 2 ^ (n - 1) :=
    (dyadic_group_even n (width L) κ δ
      (by unfold width; positivity) hκ hδone hsize).2
  exact source_group_node_impossible μ ν base L d hd hD hp
    hinner houter hwide href activity ξ₀ w hwpos R Ochild I G b hVI
    hk e heG p u t C hu huw hC hCeq δ D₀ hDone hδpos
    hδlow hsize hxsmall (fun i hi => (hrows i hi).1) hcol
    Qchild hQ (Or.inl hQcost)

end Paper2.ProtectedIncomingFromFailure

#print axioms Paper2.ProtectedIncomingFromFailure.final_mass_failure_impossible
#print axioms Paper2.ProtectedIncomingFromFailure.bob_mass_failure_impossible
