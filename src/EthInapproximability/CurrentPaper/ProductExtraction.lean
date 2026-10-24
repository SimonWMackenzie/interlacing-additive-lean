import EthInapproximability.ParameterizedNP.WrapperProtectedEarly
import EthInapproximability.ParameterizedNP.EarlyClosureBlockSelection
import EthInapproximability.ParameterizedNP.TerminalStateRealization

/-!
# Product-set projections for the current paper

Source: the mathematical v8 source, `A-stage4-details.tex`,
`lem:paper-product-extraction`, parts (1) and (2), and the following paragraph
on sections of actual joint projections.  All sets below are actual finite
sets of tuples; no rectangular-completion or independence premise is used.

The two counting proofs are reused only at their generic finite-alphabet
interfaces in `WrapperProjectionCovers` and `WrapperProtectedEarly`.
Their old matrix constructors, schedules, and communication conclusions are
not consumed.  The product-balanced-family assertion, part (3), is separate.
-/

namespace EthInapproximability.CurrentPaper.ProductExtraction

open Finset

variable {C : Type*} [Fintype C] [DecidableEq C] {q u : ℕ}

/-- Restrict actual retained tuples to the specified coordinates. -/
def projection (J : Finset (Fin q)) (S : Finset (Fin q → C)) : Finset (↥J → C) :=
  S.image (fun f i => f i.1)

/-- First retain actual tuples whose selected entries are all in the template,
then project.  This is not the Cartesian product of separate images. -/
def templateProjection (J : Finset (Fin u)) (P : Finset (Fin u → C))
    (T : Finset C) : Finset (↥J → C) :=
  projection J (P.filter (fun f => ∀ i ∈ J, f i ∈ T))

/-- A poor set has strictly smaller than the specified projection density. -/
def Poor (ρ : ℝ) (J : Finset (Fin q)) (S : Finset (Fin q → C)) : Prop :=
  ((projection J S).card : ℝ) < ρ * (Fintype.card C : ℝ) ^ J.card

omit [Fintype C] in
theorem mem_projection_iff {J : Finset (Fin q)} {S : Finset (Fin q → C)}
    {g : ↥J → C} :
    g ∈ projection J S ↔ ∃ f ∈ S, (fun i : ↥J => f i.1) = g := by
  simp only [projection, Finset.mem_image]

omit [Fintype C] in
theorem templateProjection_mem {J : Finset (Fin u)} {P : Finset (Fin u → C)}
    {T : Finset C} {g : ↥J → C} (hg : g ∈ templateProjection J P T) (i : ↥J) :
    g i ∈ T := by
  rcases mem_projection_iff.mp hg with ⟨f, hf, rfl⟩
  exact (Finset.mem_filter.mp hf).2 i.1 i.2

/-- A section chooses a retained tuple, not an arbitrary coordinate completion. -/
noncomputable def projectionSection (J : Finset (Fin q))
    (S : Finset (Fin q → C)) : ↥(projection J S) → ↥S := fun g =>
  ⟨Classical.choose (mem_projection_iff.mp g.2),
    (Classical.choose_spec (mem_projection_iff.mp g.2)).1⟩

omit [Fintype C] in
theorem projectionSection_apply (J : Finset (Fin q)) (S : Finset (Fin q → C))
    (g : ↥(projection J S)) (i : ↥J) :
    (projectionSection J S g).1 i.1 = g.1 i := by
  exact congrFun (Classical.choose_spec (mem_projection_iff.mp g.2)).2 i

/-- Part (1): at most `k(B-1)` coordinates hit every poor `k`-set.
The endpoint `ρ = 1` is included, as in the current statement; its strict
power gate is incompatible with the density of a subset of a full cube. -/
theorem poor_coordinate_cover (S : Finset (Fin q → C)) {k B : ℕ} {ρ θ : ℝ}
    (hC : 0 < Fintype.card C) (hk : 1 ≤ k) (hB : 1 ≤ B)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hgate : ρ ^ B < θ)
    (hS : θ * (Fintype.card C : ℝ) ^ q ≤ (S.card : ℝ)) :
    ∃ E : Finset (Fin q), E.card ≤ k * (B - 1) ∧
      ∀ J : Finset (Fin q), J.card = k → Poor ρ J S → (E ∩ J).Nonempty := by
  have hρlt : ρ < 1 := by
    rcases hρ1.lt_or_eq with h | h
    · exact h
    · subst ρ
      simp only [one_pow] at hgate
      have hcard : (S.card : ℝ) ≤ (Fintype.card C : ℝ) ^ q := by
        have h := Finset.card_le_univ S
        simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
          (Nat.cast_le (α := ℝ)).mpr h
      have hpos : (0 : ℝ) < (Fintype.card C : ℝ) ^ q :=
        pow_pos (Nat.cast_pos.mpr hC) q
      nlinarith
  exact ParameterizedNP.WrapperProjectionCovers.productProjectionCover S
    hC hk hB hρ0 hρlt hgate hS

/-- Part (2), with density bounds written multiplicatively to preserve the
exact integer populations and avoid silently dividing by zero. -/
theorem template_half_coordinate_extraction (P : Finset (Fin u → C)) (T : Finset C)
    {ρ lam : ℝ} (hu : 4 ∣ u) (hu0 : 0 < u) (hC : 0 < Fintype.card C)
    (hρ : 0 < ρ) (hP : ρ * (Fintype.card C : ℝ) ^ u ≤ (P.card : ℝ))
    (hT : lam * (Fintype.card C : ℝ) ≤ (T.card : ℝ))
    (hgap : 1 - lam ≤ ρ / 8) :
    ∃ J : Finset (Fin u), J.card = u / 2 ∧
      ρ * (T.card : ℝ) ^ (u / 2) ≤
        2 ^ (u + 1) * ((templateProjection J P T).card : ℝ) := by
  exact ParameterizedNP.WrapperProtectedEarly.templateCoordinateExtraction
    P T hu hu0 hC hρ hP hT hgap

/-- The same statement as a relative density inside the template cube. -/
theorem template_half_coordinate_extraction_density
    (P : Finset (Fin u → C)) (T : Finset C) {ρ lam : ℝ}
    (hu : 4 ∣ u) (hu0 : 0 < u) (hC : 0 < Fintype.card C)
    (hρ : 0 < ρ) (hlam : 0 < lam)
    (hP : ρ * (Fintype.card C : ℝ) ^ u ≤ (P.card : ℝ))
    (hT : lam * (Fintype.card C : ℝ) ≤ (T.card : ℝ))
    (hgap : 1 - lam ≤ ρ / 8) :
    ∃ J : Finset (Fin u), J.card = u / 2 ∧
      ρ / 2 ^ (u + 1) ≤
        ((templateProjection J P T).card : ℝ) / (T.card : ℝ) ^ (u / 2) := by
  obtain ⟨J, hJ, hbound⟩ := template_half_coordinate_extraction P T
    hu hu0 hC hρ hP hT hgap
  refine ⟨J, hJ, ?_⟩
  have ht : (0 : ℝ) < T.card := lt_of_lt_of_le
    (mul_pos hlam (Nat.cast_pos.mpr hC)) hT
  apply (le_div_iff₀ (pow_pos ht _)).2
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (u + 1))).2
    (by simpa only [mul_comm] using hbound)

section Bins

variable {I : Type*} [Fintype I] {s : ℕ}

/-- The retained part in a single specified vector of bins. -/
noncomputable def binPiece (A : Finset (I → C)) (bin : C → Fin s)
    (p : I → Fin s) : Finset (I → C) := by
  classical
  exact A.filter (fun f => (fun i => bin (f i)) = p)

omit [Fintype C] [DecidableEq C] in
/-- Fixing one equal bin per coordinate preserves relative density.  Both the
ambient template and every selected-bin membership are stated explicitly. -/
theorem equal_bin_average (A : Finset (I → C)) (T : Finset C)
    (bin : C → Fin s) {m : ℕ} {h : ℝ} (hs : 0 < s)
    (hbin : ∀ p : Fin s, (T.filter (fun c => bin c = p)).card = m)
    (hAtemplate : ∀ f ∈ A, ∀ i, f i ∈ T)
    (hA : h * (T.card : ℝ) ^ Fintype.card I ≤ (A.card : ℝ)) :
    ∃ p : I → Fin s,
      h * (m : ℝ) ^ Fintype.card I ≤ ((binPiece A bin p).card : ℝ) ∧
      ∀ f ∈ binPiece A bin p, ∀ i, f i ∈ T ∧ bin (f i) = p i := by
  classical
  have hT := ParameterizedNP.EarlyClosureBlockSelection.templateCard_eq_bins bin T hbin
  rw [hT] at hA
  obtain ⟨p, hp⟩ := ParameterizedNP.EarlyClosureBlockSelection.stageThreeBin_density
    hs bin A hA
  refine ⟨p, hp, ?_⟩
  intro f hf i
  have hf' := Finset.mem_filter.mp hf
  exact ⟨hAtemplate f hf'.1 i, congrFun hf'.2 i⟩

end Bins

/-- The first two operations in the uniform protected-packet proof:
extract half the coordinates and fix one template bin in each of them. -/
theorem template_half_bin_extraction (P : Finset (Fin u → C)) (T : Finset C)
    {ρ lam : ℝ} {s m : ℕ} (bin : C → Fin s) (hs : 0 < s)
    (hbin : ∀ p : Fin s, (T.filter (fun c => bin c = p)).card = m)
    (hu : 4 ∣ u) (hu0 : 0 < u) (hC : 0 < Fintype.card C)
    (hρ : 0 < ρ) (hP : ρ * (Fintype.card C : ℝ) ^ u ≤ (P.card : ℝ))
    (hT : lam * (Fintype.card C : ℝ) ≤ (T.card : ℝ))
    (hgap : 1 - lam ≤ ρ / 8) :
    ∃ (J : Finset (Fin u)) (p : ↥J → Fin s), J.card = u / 2 ∧
      (ρ / 2 ^ (u + 1)) * (m : ℝ) ^ (u / 2) ≤
        ((binPiece (templateProjection J P T) bin p).card : ℝ) ∧
      ∀ f ∈ binPiece (templateProjection J P T) bin p,
        ∀ i, f i ∈ T ∧ bin (f i) = p i := by
  obtain ⟨J, hJ, hbound⟩ := template_half_coordinate_extraction P T
    hu hu0 hC hρ hP hT hgap
  have hA : (ρ / 2 ^ (u + 1)) * (T.card : ℝ) ^ Fintype.card ↥J ≤
      ((templateProjection J P T).card : ℝ) := by
    rw [Fintype.card_coe, hJ, div_mul_eq_mul_div]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (u + 1))).2
      (by simpa only [mul_comm] using hbound)
  obtain ⟨p, hp, hmem⟩ := equal_bin_average (templateProjection J P T) T bin hs hbin
    (fun _ hf i => templateProjection_mem hf i) hA
  exact ⟨J, p, hJ, by simpa only [Fintype.card_coe, hJ] using hp, hmem⟩

section Quotients

open ParameterizedNP.TerminalStateRealization

variable {I A B : Type*} [Fintype I] [DecidableEq I] [DecidableEq B]

/-- Independent regular quotient maps remain regular on the entire product
box.  The assertion concerns the whole joint tuple, not just its marginals. -/
theorem regular_product (R : I → Finset A) (f : I → A → B) (d : I → ℕ)
    (hreg : ∀ i, RegularOn (R i) (f i) (d i)) :
    RegularOn (Fintype.piFinset R) (fun a i => f i (a i)) (∏ i, d i) := by
  classical
  intro b
  have heq : (Fintype.piFinset R).filter (fun a => (fun i => f i (a i)) = b) =
      Fintype.piFinset (fun i => (R i).filter (fun a => f i a = b i)) := by
    ext a
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨ha, hb⟩ i
      exact ⟨ha i, congrFun hb i⟩
    · intro ha
      exact ⟨fun i => (ha i).1, funext (fun i => (ha i).2)⟩
  rw [heq, Fintype.card_piFinset]
  exact Finset.prod_congr rfl (fun i _ => hreg i (b i))

/-- Forgetting regular duplication labels does not decrease the density of
an actual joint retained set.  No product assumption is imposed on `P`. -/
theorem regular_product_density [Fintype B]
    (R : I → Finset A) (f : I → A → B) (d : I → ℕ)
    (hreg : ∀ i, RegularOn (R i) (f i) (d i)) (hd : ∀ i, 0 < d i)
    (P : Finset (I → A)) (hP : P ⊆ Fintype.piFinset R) :
    (P.card : ℝ) / ((Fintype.piFinset R).card : ℝ) ≤
      ((P.image (fun a i => f i (a i))).card : ℝ) /
        (Fintype.card B : ℝ) ^ Fintype.card I := by
  classical
  have hdprod : 0 < ∏ i, d i := Finset.prod_pos (fun i _ => hd i)
  have h := regularOn_density_transfer (regular_product R f d hreg) hdprod hP
  simpa only [Fintype.card_fun, Nat.cast_pow] using h

/-- A division-free density bound through the same joint quotient. -/
theorem regular_product_density_bound [Fintype B]
    (R : I → Finset A) (f : I → A → B) (d : I → ℕ)
    (hreg : ∀ i, RegularOn (R i) (f i) (d i)) (hd : ∀ i, 0 < d i)
    (P : Finset (I → A)) (hP : P ⊆ Fintype.piFinset R) {h : ℝ}
    (hbound : h * ((Fintype.piFinset R).card : ℝ) ≤ (P.card : ℝ)) :
    h * (Fintype.card B : ℝ) ^ Fintype.card I ≤
      ((P.image (fun a i => f i (a i))).card : ℝ) := by
  classical
  have hregular := regular_product R f d hreg
  have hdprod : (0 : ℝ) < (∏ i, d i : ℕ) :=
    Nat.cast_pos.mpr (Finset.prod_pos (fun i _ => hd i))
  have hcard := hregular.card_eq
  have himage := hregular.card_le_mul_image hP
  have himageR : (P.card : ℝ) ≤ (∏ i, d i : ℕ) *
      ((P.image (fun a i => f i (a i))).card : ℝ) := by exact_mod_cast himage
  have hcardR : ((Fintype.piFinset R).card : ℝ) =
      (∏ i, d i : ℕ) * (Fintype.card B : ℝ) ^ Fintype.card I := by
    simpa only [Nat.cast_mul, Fintype.card_fun, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ℝ)) hcard
  rw [hcardR] at hbound
  apply le_of_mul_le_mul_left (a := ((∏ i, d i : ℕ) : ℝ)) _ hdprod
  nlinarith [hbound, himageR]

end Quotients

end EthInapproximability.CurrentPaper.ProductExtraction
