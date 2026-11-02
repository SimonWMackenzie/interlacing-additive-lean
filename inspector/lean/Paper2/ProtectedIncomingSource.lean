import Paper2.ProtectedIncomingBlocks
import Paper2.SourceProfiles
import Paper2.ProtectedIncomingTemplateLaw
import Paper2.ProtectedIncomingDensity

/-!
# Source-parameter and actual-node adapter for incoming labelled blocks

Scratch continuation of frozen `ProtectedIncomingBlocks.lean`. The generic
block/embedding file is not edited while it undergoes independent review.
-/

namespace Paper2.ProtectedIncomingSource

open Paper2.ProtectedIncomingBlocks
open SourceMatrix SourceLaws SourceProfileParameters
open Workspace.Types.CommComplexity Workspace.Types.Protocol

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩

/-- The block count is the exact dyadic power used in the row ladder. -/
theorem source_K_power (L t : ℕ) :
    2 ^ (1 + exponent L + t + outerExponent L) =
      2 * width L * (2 ^ t) * outerWidth L := by
  simp only [width, outerWidth, pow_add, pow_one]

/-- The charged lower bound is the manuscript's `C+log κ`, with natural
subtraction discharged by the displayed positive source budget. -/
theorem source_capacity_budget (L d C t : ℕ) (hC : 1 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L) :
    d + exponent L + (1 + exponent L + t + outerExponent L) = C + t := by
  omega

/-- The original base profile supplies the transposed-`M₁` row-ladder
profile; it is not an assumed incoming-node certificate. -/
theorem source_inner_profile
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hD : D base = d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y) :
    RestrictionProfile
      (fun (γ : Word (width L - 2) (width L) Y) a => M₁ base a γ)
      (ν.iid ((width L - 2) + width L + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin (width L - 2))).prod μ).toFiniteLaw
      (x L) ((d + exponent L : ℕ) : ℤ) :=
  (SourceProfiles.source_profiles μ ν base L d hd hD hp hinner
    houter hwide href activity ξ₀).2.1

/-- The density front end's Boolean names the diagonal tag when true;
the block module names the fixed-tail tag when true. This complement
converts the *same* actual original-coordinate group into the per-coordinate
mass hypothesis, with no relabelled or conditioned rows. -/
theorem group_mass_for_blocks
    {Y : Type*} [Fintype Y]
    (ν : PositiveRationalLaw Y) (L w k : ℕ)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (I V : Finset (Fin w)) (b : Bool) (e : Fin k → Fin w)
    (δ : ℝ) (hVI : V ⊆ I) (he : ∀ t, e t ∈ V)
    (hrows : ∀ i ∈ V, δ / 2 <
      ProtectedIncomingDensity.density ν L w R I b i) :
    ∀ t : Fin k, δ / 2 <
      if (!b) then
        (fixedTailLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
          (· ∈ ProtectedIncomingRows.fixedEvent R (e t))
      else
        (outerLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
          (· ∈ ProtectedIncomingRows.diagonalEvent R (e t)) := by
  intro t
  have hi := hVI (he t)
  have hr := hrows (e t) (he t)
  cases b <;> simpa [ProtectedIncomingDensity.density, hi] using hr

/-- The source-facing local incoming bound, on the physical original Items
matrix and the same actual retained rectangle. `hmass` comes from the
selected dense original group; `hcol` is the explicit whole-event selector
image that the checked template-law bridge supplies. -/
theorem source_incoming_cost_lower
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hD : D base = d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y)
    (w : ℕ) (hw : 0 < w)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (O : Set (Fin w → RawRow (width L - 2) (outerWidth L) (width L) X
      (SourceConstruction.Items (width L) V)))
    {k : ℕ} (hk : 0 < k)
    (e : Fin k → Fin w) (p : Fin k → Fin (width L)) (tag : Fin k → Bool)
    (u t C : ℕ) (hu : u = 2 * k) (huw : u ≤ w) (hC : 1 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (δ D₀ : ℝ) (hD₀ : 1 ≤ D₀) (hδ : 0 < δ)
    (hδlow : D₀ / (2 * (w : ℝ)) ≤ δ)
    (hsize : 16 * (width L : ℝ) * ((2 ^ t : ℕ) : ℝ) ≤ (u : ℝ) * δ)
    (hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1)
    (hmass : ∀ j : Fin k, δ / 2 <
      if tag j then
        (fixedTailLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
          (· ∈ ProtectedIncomingRows.fixedEvent R (e j))
      else
        (outerLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
          (· ∈ ProtectedIncomingRows.diagonalEvent R (e j)))
    (hcol : (12 / 25 : ℝ) <
      ((templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw.iid k).prob
        (· ∈ ProtectedIncomingColumns.selectorImage O e p))
    (P : Protocol R O Bool)
    (hP : P.Computes (fun row col =>
      fullInterlace (N base activity ξ₀) w row.val col.val)) :
    C + t ≤ P.cost := by
  classical
  let ell := 1 + exponent L + t + outerExponent L
  have hell : 2 ≤ ell := by
    have he := exponent_ge L
    dsimp [ell]
    omega
  have hH : 2 ≤ d + exponent L := by omega
  have hK : 2 ^ ell = 2 * width L * 2 ^ t * outerWidth L :=
    source_K_power L t
  have hwden : (0 : ℝ) < (w : ℝ) ^ 2 * outerWidth L := by
    have ho : 0 < outerWidth L := NeZero.pos _
    exact mul_pos (sq_pos_of_pos (by exact_mod_cast hw)) (by exact_mod_cast ho)
  have hxsmall' : x L ≤ 1 / ((w : ℝ) ^ 2 * outerWidth L) := by
    apply (le_div_iff₀ hwden).2
    simpa only [mul_comm] using hxsmall
  have hprofile := source_inner_profile μ ν base L d hd hD hp
    hinner houter hwide href activity ξ₀
  have hlower := incoming_capacity_from_guards μ ν base activity ξ₀
    R O e p tag u (width L) (2 ^ t) (d + exponent L) ell δ D₀ (x L)
    hw hk hu huw hD₀ hδ hδlow hsize (x_pos L) hxsmall' hH hell
    hK hprofile hmass hcol
  have hupper : Compression.restrictionD
      (fullInterlace (N base activity ξ₀) w) R O ≤ P.cost := by
    change Workspace.Types.CommComplexity.D (fun (row : R) (col : O) =>
      fullInterlace (N base activity ξ₀) w row.val col.val) ≤ P.cost
    exact Nat.sInf_le ⟨P, rfl, hP⟩
  have hbudget := source_capacity_budget L d C t hC hCeq
  omega

/-- Either of the two actual node budgets in frozen v12 is inconsistent
with the source-specialized row ladder: a charged first-Bob child has at
most `C+t-2` bits, and a final node has at most `C-1` bits. -/
theorem source_incoming_node_impossible
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hD : D base = d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y)
    (w : ℕ) (hw : 0 < w)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (O : Set (Fin w → RawRow (width L - 2) (outerWidth L) (width L) X
      (SourceConstruction.Items (width L) V)))
    {k : ℕ} (hk : 0 < k)
    (e : Fin k → Fin w) (p : Fin k → Fin (width L)) (tag : Fin k → Bool)
    (u t C : ℕ) (hu : u = 2 * k) (huw : u ≤ w) (hC : 1 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (δ D₀ : ℝ) (hD₀ : 1 ≤ D₀) (hδ : 0 < δ)
    (hδlow : D₀ / (2 * (w : ℝ)) ≤ δ)
    (hsize : 16 * (width L : ℝ) * ((2 ^ t : ℕ) : ℝ) ≤ (u : ℝ) * δ)
    (hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1)
    (hmass : ∀ j : Fin k, δ / 2 <
      if tag j then
        (fixedTailLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
          (· ∈ ProtectedIncomingRows.fixedEvent R (e j))
      else
        (outerLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
          (· ∈ ProtectedIncomingRows.diagonalEvent R (e j)))
    (hcol : (12 / 25 : ℝ) <
      ((templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw.iid k).prob
        (· ∈ ProtectedIncomingColumns.selectorImage O e p))
    (P : Protocol R O Bool)
    (hP : P.Computes (fun row col =>
      fullInterlace (N base activity ξ₀) w row.val col.val))
    (hnode : P.cost ≤ C + t - 2 ∨ P.cost ≤ C - 1) : False := by
  have hlower := source_incoming_cost_lower μ ν base L d hd hD hp
    hinner houter hwide href activity ξ₀ w hw R O hk e p tag
    u t C hu huw hC hCeq δ D₀ hD₀ hδ hδlow hsize hxsmall
    hmass hcol P hP
  rcases hnode with hb | hf <;> omega

/-- Source-facing contradiction with the actual density-group output in
place of per-coordinate protected-mass premises. The selected labels
remain original coordinates in `V`, and `!b` is the checked tag conversion. -/
theorem source_group_node_impossible
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
    (w : ℕ) (hw : 0 < w)
    (R : Set (Fin w × TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (O : Set (Fin w → RawRow (width L - 2) (outerWidth L) (width L) X
      (SourceConstruction.Items (width L) Vtx)))
    (I V : Finset (Fin w)) (b : Bool) (hVI : V ⊆ I)
    {k : ℕ} (hk : 0 < k)
    (e : Fin k → Fin w) (he : ∀ j, e j ∈ V)
    (p : Fin k → Fin (width L))
    (u t C : ℕ) (hu : u = 2 * k) (huw : u ≤ w) (hC : 1 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (δ D₀ : ℝ) (hD₀ : 1 ≤ D₀) (hδ : 0 < δ)
    (hδlow : D₀ / (2 * (w : ℝ)) ≤ δ)
    (hsize : 16 * (width L : ℝ) * ((2 ^ t : ℕ) : ℝ) ≤ (u : ℝ) * δ)
    (hxsmall : ((w : ℝ) ^ 2 * (outerWidth L : ℝ)) * x L ≤ 1)
    (hrows : ∀ i ∈ V, δ / 2 <
      ProtectedIncomingDensity.density ν L w R I b i)
    (hcol : (12 / 25 : ℝ) <
      ((templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw.iid k).prob
        (· ∈ ProtectedIncomingColumns.selectorImage O e p))
    (P : Protocol R O Bool)
    (hP : P.Computes (fun row col =>
      fullInterlace (N base activity ξ₀) w row.val col.val))
    (hnode : P.cost ≤ C + t - 2 ∨ P.cost ≤ C - 1) : False := by
  have hmass := group_mass_for_blocks ν L w k R I V b e δ hVI he hrows
  exact source_incoming_node_impossible μ ν base L d hd hD hp
    hinner houter hwide href activity ξ₀ w hw R O hk e p (fun _ => !b)
    u t C hu huw hC hCeq δ D₀ hD₀ hδ hδlow hsize hxsmall
    hmass hcol P hP hnode

end Paper2.ProtectedIncomingSource

#print axioms Paper2.ProtectedIncomingSource.source_K_power
#print axioms Paper2.ProtectedIncomingSource.source_capacity_budget
#print axioms Paper2.ProtectedIncomingSource.source_inner_profile
#print axioms Paper2.ProtectedIncomingSource.group_mass_for_blocks
#print axioms Paper2.ProtectedIncomingSource.source_incoming_cost_lower
#print axioms Paper2.ProtectedIncomingSource.source_incoming_node_impossible
#print axioms Paper2.ProtectedIncomingSource.source_group_node_impossible
