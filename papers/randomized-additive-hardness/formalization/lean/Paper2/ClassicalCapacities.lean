import Paper2.ClassicalRows
import Paper2.ClassicalSeparation

/-!
# Small-capacity estimates on arbitrary selected blocks

Frozen source: v12 Appendix A, `cl:profile-equivalence`, `cl:projection`,
and `cl:small-capacities`. This module composes the proved row estimates
with the actual uniform-law profile and with arbitrary selected blocks.

`NPCC.coord_projection` supplies retained rows and projected columns with
explicit provenance. The protocol adapter below chooses one actual original
column for each projected column; it never replaces the surviving tuple set
by a product of coordinate sets. Its argument follows the private helper
`D_projected_subgame_le` in the frozen `NPCC.Control` source, using the
existing concrete protocol precomposition theorem.

The present statements concern uniform finite carriers. Rational-law
transport and the amplifier that consumes these estimates are separate.
-/

namespace Paper2.ClassicalCapacities

open Workspace.Types.CommComplexity Workspace.Types.Interlace
open ClassicalRows

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- The actual uniform three-level restriction profile yields the identical
three-rung lower bound. H is a lower bound, not an exact communication cost. -/
theorem profile_lambda (F : X → Y → Bool) (H : ℕ) (x : ℝ) (hx : x ≤ 1)
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      x (H : ℤ)) : H ≤ lambda F 1 x (3 / 5) := by
  obtain ⟨h0, h1, h2⟩ := (restrictionProfile_three_levels F (FiniteLaw.uniform X)
    (FiniteLaw.uniform Y) x (H : ℤ)).mp hprofile
  have a := ClassicalSeparation.oneCopy_family_lowerBound F x (3 / 5) (H : ℤ)
    hx (by norm_num) h0
  have b := ClassicalSeparation.oneCopy_family_lowerBound F x (3 / 10) ((H : ℤ) - 1)
    hx (by norm_num) h1
  have c := ClassicalSeparation.oneCopy_family_lowerBound F x (3 / 20) ((H : ℤ) - 2)
    hx (by norm_num) h2
  apply (le_lambda_iff F 1 H x (3 / 5)).mpr
  have hhalf : ((3 : ℝ) / 5) / 2 = 3 / 10 := by norm_num
  have hquarter : ((3 : ℝ) / 5) / 4 = 3 / 20 := by norm_num
  rw [hhalf, hquarter]
  have ha : H ≤ restrictionCost F 1 x (3 / 5) := by exact_mod_cast a
  by_cases hsmall : H ≤ 1
  · exact ⟨ha, by omega, by omega⟩
  · have hH2 : 2 ≤ H := by omega
    have hb' : ((H - 1 : ℕ) : ℤ) ≤
        (restrictionCost F 1 x (3 / 10) : ℤ) := by
      simpa [Nat.cast_sub (by omega : 1 ≤ H)] using b
    have hc' : ((H - 2 : ℕ) : ℤ) ≤
        (restrictionCost F 1 x (3 / 20) : ℤ) := by
      simpa [Nat.cast_sub (by omega : 2 ≤ H)] using c
    have hb : H - 1 ≤ restrictionCost F 1 x (3 / 10) := by
      exact_mod_cast hb'
    have hc : H - 2 ≤ restrictionCost F 1 x (3 / 20) := by
      exact_mod_cast hc'
    exact ⟨ha, by omega, by omega⟩

/-- A protocol on the original retained inputs gives a protocol on any
coordinate projection whose rows and columns retain actual representatives.
No independent-coordinate or fibre-completeness assumption is made. -/
theorem projected_D_le (F : X → Y → Bool) {q r : ℕ}
    {R : Finset (Fin q × X)} {C : Finset (Fin q → Y)}
    {R' : Finset (Fin r × X)} {C' : Finset (Fin r → Y)}
    (emb : Fin r → Fin q)
    (hRows : ∀ a ∈ R', (emb a.1, a.2) ∈ R)
    (hCols : ∀ c' ∈ C', ∃ c ∈ C, ∀ j : Fin r, c' j = c (emb j)) :
    D (NPCC.subgame (interlaceFun F r) R' C') ≤
      D (NPCC.subgame (interlaceFun F q) R C) := by
  classical
  let rows : {a // a ∈ R'} → {a // a ∈ R} :=
    fun a => ⟨(emb a.val.1, a.val.2), hRows a.val a.property⟩
  let cols : {c // c ∈ C'} → {c // c ∈ C} :=
    fun c => ⟨Classical.choose (hCols c.val c.property),
      (Classical.choose_spec (hCols c.val c.property)).1⟩
  have hcols (c : {c // c ∈ C'}) (j : Fin r) : c.val j = (cols c).val (emb j) :=
    (Classical.choose_spec (hCols c.val c.property)).2 j
  have heq : NPCC.subgame (interlaceFun F r) R' C' =
      fun a c => NPCC.subgame (interlaceFun F q) R C (rows a) (cols c) := by
    funext a c
    exact congrArg (F a.val.2) (hcols c a.val.1)
  rw [heq]
  exact NPCC.D_mapNodes_le (NPCC.subgame (interlaceFun F q) R C) rows cols

/-- Select arbitrary named blocks, relabel them by `Fin r`, and project
the retained columns. The uniform density is preserved including ceilings,
and the resulting matrix is no harder than the original retained matrix. -/
theorem selected_blocks (F : X → Y → Bool) {p r : ℕ} (hr : 0 < r)
    (Q : Finset (Fin p)) (e : Fin r ≃ {i // i ∈ Q})
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y)) (x z : ℝ)
    (hrow : NPCC.IsEquipartitionedGE R Q ⌈(Fintype.card X : ℝ) * x⌉₊)
    (hcol : ⌈((Fintype.card Y : ℝ) ^ p) * z⌉₊ ≤ C.card) :
    ∃ RC' : Finset (Fin r × X) × Finset (Fin r → Y),
      RC' ∈ restrictions (X := X) (Y := Y) r x z ∧
      D (NPCC.subgame (interlaceFun F r) RC'.1 RC'.2) ≤
        D (NPCC.subgame (interlaceFun F p) R C) := by
  obtain ⟨RC', hmem, hRows, hCols⟩ := NPCC.coord_projection hr e hrow hcol le_rfl
  exact ⟨RC', hmem, projected_D_le F (fun j => (e j).val) hRows hCols⟩

/-- The large-power case of `cl:small-capacities` for any selected block
set. The retained matrix may also contain rows from additional blocks. -/
theorem small_capacity_power (F : X → Y → Bool) (H l p : ℕ) {x : ℝ}
    (hH : 2 ≤ H) (hx0 : 0 < x) (hl : 2 ≤ l)
    (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      x (H : ℤ))
    (Q : Finset (Fin p)) (hQ : 2 ^ (l - 1) + 1 ≤ Q.card)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hrow : NPCC.IsEquipartitionedGE R Q
      ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ l * x)⌉₊)
    (hcol : ⌈((Fintype.card Y : ℝ) ^ p) * (9 / 25)⌉₊ ≤ C.card) :
    H + l ≤ D (NPCC.subgame (interlaceFun F p) R C) := by
  classical
  have hx : x ≤ 1 := (le_mul_of_one_le_left hx0.le
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans hscale
  have hbase := profile_lambda F H x hx hprofile
  let e : Fin Q.card ≃ {i // i ∈ Q} := (Fintype.equivFinOfCardEq (by simp)).symm
  have hQpos : 0 < Q.card := by
    exact lt_of_lt_of_le (by positivity : 0 < 2 ^ (l - 1) + 1) hQ
  obtain ⟨RC', hmem, hD⟩ := selected_blocks F hQpos Q e R C
    ((2 : ℝ) ^ l * x) (9 / 25) hrow hcol
  exact (ClassicalRows.small_capacity_power F H l Q.card hH hx0 hl hscale hbase hQ
    RC'.1 RC'.2 hmem).trans hD

/-- The `K = 1` and `K = 2` cases both require two retained blocks and the
doubled row threshold. There is no assertion for one retained block. -/
theorem small_capacity_two (F : X → Y → Bool) (H p : ℕ) {x : ℝ}
    (hH : 2 ≤ H) (hx0 : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      x (H : ℤ))
    (Q : Finset (Fin p)) (hQ : 2 ≤ Q.card)
    (R : Finset (Fin p × X)) (C : Finset (Fin p → Y))
    (hrow : NPCC.IsEquipartitionedGE R Q ⌈(Fintype.card X : ℝ) * (2 * x)⌉₊)
    (hcol : ⌈((Fintype.card Y : ℝ) ^ p) * (9 / 25)⌉₊ ≤ C.card) :
    H + 1 ≤ D (NPCC.subgame (interlaceFun F p) R C) := by
  classical
  obtain ⟨Q', hsub, hcard⟩ := Finset.exists_subset_card_eq hQ
  let e : Fin 2 ≃ {i // i ∈ Q'} :=
    (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  obtain ⟨RC', hmem, hD⟩ := selected_blocks F (by decide : 0 < 2) Q' e R C
    (2 * x) (9 / 25) (fun i hi => hrow i (hsub hi)) hcol
  exact (ClassicalRows.small_capacity_two F H hH hx0 hscale
    (profile_lambda F H x (by linarith) hprofile) RC'.1 RC'.2 hmem).trans hD

end Paper2.ClassicalCapacities
