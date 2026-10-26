import Paper2.RestrictionProfiles
import Paper2.DominantBlocks
import NPCC.Control

/-!
# Classical near-exact separation at the paper's three profile thresholds

Frozen source: v12 Appendix A, `cl:separation` (lines 206--251).
This adapter uses the concrete inherited `NPCC.classical_separation` proof,
not a postulated separation contract. The uniform profile is translated
to the exact one-copy brackets of the inherited robust-matrix predicate.
The early-speaker conclusion is on live rectangles, not dead subtrees.
-/

namespace Paper2

open scoped BigOperators
open Workspace.Types.CommComplexity Workspace.Types.Protocol
open Workspace.Types.Interlace

namespace FiniteLaw

/-- The uniform probability law on any nonempty finite labelled carrier. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] : FiniteLaw α where
  weight _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_pos.ne')

theorem uniform_prob_finset {α : Type*} [Fintype α] [Nonempty α] (S : Finset α) :
    (uniform α).prob (fun x => x ∈ S) = (S.card : ℝ) / Fintype.card α := by
  classical
  simp only [prob, uniform]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

/-- Cardinality ceilings are exactly the uniform probability thresholds. -/
theorem le_uniform_prob_iff {α : Type*} [Fintype α] [Nonempty α]
    (S : Finset α) (x : ℝ) :
    x ≤ (uniform α).prob (· ∈ S) ↔ ⌈(Fintype.card α : ℝ) * x⌉₊ ≤ S.card := by
  rw [uniform_prob_finset, le_div_iff₀ (by exact_mod_cast Fintype.card_pos)]
  rw [Nat.ceil_le]
  simp [mul_comm]

end FiniteLaw

namespace ClassicalSeparation

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

/-- A lower bound on all uniform restrictions gives the identical lower
bound on every member of the inherited one-copy bracket. The one-copy
row/column carriers are explicitly projected to their original inputs. -/
theorem oneCopy_lowerBound (F : X → Y → Bool) (x y : ℝ) (c : ℤ)
    (h : RestrictionLowerBound F (FiniteLaw.uniform X) (FiniteLaw.uniform Y) x y c)
    (RC : Finset (Fin 1 × X) × Finset (Fin 1 → Y))
    (hRC : RC ∈ NPCC.bracketGE X Y 1 x y) :
    c ≤ (D (NPCC.subgame (interlaceFun F 1) RC.1 RC.2) : ℤ) := by
  classical
  let R := RC.1.image Prod.snd
  let C := RC.2.image (fun z => z 0)
  have hRcard : R.card = RC.1.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    exact Prod.ext (Subsingleton.elim _ _) hab
  have hCcard : C.card = RC.2.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    funext i
    simpa only [show i = 0 from Subsingleton.elim _ _] using hab
  have hR : ⌈(Fintype.card X : ℝ) * x⌉₊ ≤ R.card := by
    have he := hRC.1 0 (Finset.mem_univ _)
    simpa [hRcard, show ∀ a : Fin 1 × X, a.1 = 0 from fun _ => Subsingleton.elim _ _] using he
  have hC : ⌈(Fintype.card Y : ℝ) * y⌉₊ ≤ C.card := by
    simpa [hCcard] using hRC.2
  have hl := h (R : Set X) (C : Set Y)
    ((FiniteLaw.le_uniform_prob_iff R x).mpr hR)
    ((FiniteLaw.le_uniform_prob_iff C y).mpr hC)
  have heq := restrictionD_pullback_image F Prod.snd (fun z : Fin 1 → Y => z 0)
    (RC.1 : Set (Fin 1 × X)) (RC.2 : Set (Fin 1 → Y))
  have hF : (fun a : Fin 1 × X => fun z : Fin 1 → Y => F a.2 (z 0)) =
      interlaceFun F 1 := by
    funext a z
    simp only [interlaceFun, show a.1 = 0 from Subsingleton.elim _ _]
  rw [hF] at heq
  have hRset : (R : Set X) = Prod.snd '' (RC.1 : Set (Fin 1 × X)) := Finset.coe_image
  have hCset : (C : Set Y) = (fun z : Fin 1 → Y => z 0) '' (RC.2 : Set (Fin 1 → Y)) :=
    Finset.coe_image
  rw [← hRset, ← hCset] at heq
  have heq' : D (NPCC.subgame (interlaceFun F 1) RC.1 RC.2) =
      Compression.restrictionD F (R : Set X) (C : Set Y) := by
    exact heq
  rw [heq']
  exact hl

/-- The minimum over the nonempty one-copy bracket obeys the same integer
lower bound. Nonemptiness is proved from admissible density thresholds. -/
theorem oneCopy_family_lowerBound (F : X → Y → Bool) (x y : ℝ) (c : ℤ)
    (hx : x ≤ 1) (hy : y ≤ 1)
    (h : RestrictionLowerBound F (FiniteLaw.uniform X) (FiniteLaw.uniform Y) x y c) :
    c ≤ (NPCC.Dfamily (interlaceFun F 1) (NPCC.bracketGE X Y 1 x y) : ℤ) := by
  classical
  have hne : {d : ℕ | ∃ RC ∈ NPCC.bracketGE X Y 1 x y,
      d = D (NPCC.subgame (interlaceFun F 1) RC.1 RC.2)}.Nonempty := by
    obtain ⟨RC, hRC⟩ := NPCC.bracketGE.nonempty (X := X) (Y := Y)
      1 x y hx hy Fintype.card_pos
    exact ⟨_, RC, hRC, rfl⟩
  obtain ⟨RC, hRC, heq⟩ := Nat.sInf_mem hne
  change c ≤ (sInf {d : ℕ | ∃ RC ∈ NPCC.bracketGE X Y 1 x y,
      d = D (NPCC.subgame (interlaceFun F 1) RC.1 RC.2)} : ℕ)
  rw [heq]
  exact oneCopy_lowerBound F x y c h RC hRC

/-- The exact profile of the current paper implies the inherited robust
predicate at `delta = 1/10`. This derives all three bracket lower bounds;
no robustness or separation conclusion is supplied as an extra premise. -/
theorem profile_isRobust (F : X → Y → Bool) (b : ℝ) (hb : 1 ≤ b)
    (hD : 2 ≤ D F)
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      ((2 : ℝ) ^ (-b)) (D F : ℤ)) :
    NPCC.IsRobust F (1 / 10) b := by
  have hx : (2 : ℝ) ^ (-b) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hlevels := (restrictionProfile_three_levels F (FiniteLaw.uniform X)
    (FiniteLaw.uniform Y) ((2 : ℝ) ^ (-b)) (D F : ℤ)).mp hprofile
  have h0 := oneCopy_family_lowerBound F ((2 : ℝ) ^ (-b)) (3 / 5) (D F : ℤ)
    hx (by norm_num) hlevels.1
  have h1 := oneCopy_family_lowerBound F ((2 : ℝ) ^ (-b)) (3 / 10) ((D F : ℤ) - 1)
    hx (by norm_num) hlevels.2.1
  have h2 := oneCopy_family_lowerBound F ((2 : ℝ) ^ (-b)) (3 / 20) ((D F : ℤ) - 2)
    hx (by norm_num) hlevels.2.2
  refine ⟨by omega, ?_, ?_, ?_⟩
  · norm_num only [show (1 / 2 + (1 / 10) : ℝ) = 3 / 5 by norm_num]
    exact_mod_cast h0
  · norm_num only [show (1 / 8 + (1 / 10) / 4 : ℝ) = 3 / 20 by norm_num]
    exact h2
  · norm_num only [show (1 / 4 + (1 / 10) / 2 : ℝ) = 3 / 10 by norm_num]
    exact h1

/-- The numerical endpoint required by the inherited protocol-order theorem. -/
theorem delta_tenth_admissible : (1 / 10 : ℝ) ≤ 1 / Real.sqrt 2 - 1 / 2 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hbound : Real.sqrt 2 ≤ 5 / 3 := by nlinarith
  have hi : (3 / 5 : ℝ) ≤ 1 / Real.sqrt 2 :=
    (le_div_iff₀ hs).mpr (by nlinarith)
  linarith

/-- Frozen v12 `cl:separation`, with `u = 2^Q` and the current paper's
uniform three-level profile. `FirstKRowBitsOn` forbids early Bob nodes and
leaves on live rectangles only. The no-waste counts use the actual row
prefix of the given protocol and exact natural ceilings. -/
theorem classical_separation (F : X → Y → Bool) (b : ℕ) (hb : 1 ≤ b)
    (hD : 2 ≤ D F)
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      ((2 : ℝ) ^ (-(b : ℝ))) (D F : ℤ))
    (Q : ℕ) (hQ : 1 ≤ Q) (x z : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hz : (18 / 25 : ℝ) ≤ z) (hz1 : z ≤ 1)
    (hqx : (2 ^ Q : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) ≤ x)
    (hgap : 2 ^ Q * ⌈(2 : ℝ) ^ (1 - (b : ℝ)) * (Fintype.card X : ℝ)⌉₊
      < ⌈(Fintype.card X : ℝ) * x⌉₊)
    (RC : Finset (Fin (2 ^ Q) × X) × Finset (Fin (2 ^ Q) → Y))
    (hRC : RC ∈ NPCC.bracketGE X Y (2 ^ Q) x z)
    (P : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool)
    (hPc : P.Computes (NPCC.subgame (fullInterlace F (2 ^ Q)) RC.1 RC.2))
    (hcost : P.cost ≤ D F + Q) :
    NPCC.Protocol.FirstKRowBitsOn
      (Finset.univ : Finset {a // a ∈ RC.1})
      (Finset.univ : Finset {c // c ∈ RC.2}) Q P ∧
    NPCC.NoWasteConclusion (Finset.univ : Finset (Fin (2 ^ Q))) RC.1
      (NPCC.Protocol.prefixLabelFinQ RC.1 P)
      ⌈(Fintype.card X : ℝ) * x⌉₊
      ⌈(2 : ℝ) ^ (1 - (b : ℝ)) * (Fintype.card X : ℝ)⌉₊ := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hr := profile_isRobust F b hb' hD hprofile
  exact NPCC.classical_separation hr hb' (by norm_num) delta_tenth_admissible
    hD Q hQ hx0 hx1 (by norm_num; exact hz) hz1 hqx hgap RC hRC P hPc hcost

/-- The dominant-block bijection in the paragraph following `cl:separation`.
Unlike a conditional no-waste interface, this theorem starts with the
paper's profile and protocol hypotheses and derives the no-waste input by
the checked separation theorem above. All `2^Q` prefix fibres are nonempty. -/
theorem classical_separation_with_bijection
    (F : X → Y → Bool) (b : ℕ) (hb : 1 ≤ b) (hD : 2 ≤ D F)
    (hprofile : RestrictionProfile F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      ((2 : ℝ) ^ (-(b : ℝ))) (D F : ℤ))
    (Q : ℕ) (hQ : 1 ≤ Q) (x z : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hz : (18 / 25 : ℝ) ≤ z) (hz1 : z ≤ 1)
    (hqx : (2 ^ Q : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) ≤ x)
    (hgap : 2 ^ Q * ⌈(2 : ℝ) ^ (1 - (b : ℝ)) * (Fintype.card X : ℝ)⌉₊
      < ⌈(Fintype.card X : ℝ) * x⌉₊)
    (RC : Finset (Fin (2 ^ Q) × X) × Finset (Fin (2 ^ Q) → Y))
    (hRC : RC ∈ NPCC.bracketGE X Y (2 ^ Q) x z)
    (P : Protocol {a // a ∈ RC.1} {c // c ∈ RC.2} Bool)
    (hPc : P.Computes (NPCC.subgame (fullInterlace F (2 ^ Q)) RC.1 RC.2))
    (hcost : P.cost ≤ D F + Q) :
    NPCC.Protocol.FirstKRowBitsOn
      (Finset.univ : Finset {a // a ∈ RC.1})
      (Finset.univ : Finset {c // c ∈ RC.2}) Q P ∧
    ∃ dom : Fin (2 ^ Q) ≃ Fin (2 ^ Q), ∀ j : Fin (2 ^ Q),
      ⌈(Fintype.card X : ℝ) * x⌉₊ - (2 ^ Q - 1) *
          ⌈(2 : ℝ) ^ (1 - (b : ℝ)) * (Fintype.card X : ℝ)⌉₊ ≤
        (RC.1.filter (fun a => NPCC.Protocol.prefixLabelFinQ RC.1 P a = j ∧
          a.1 = dom j)).card ∧
      (∀ i : Fin (2 ^ Q), i ≠ dom j →
        (RC.1.filter (fun a => NPCC.Protocol.prefixLabelFinQ RC.1 P a = j ∧
          a.1 = i)).card <
          ⌈(2 : ℝ) ^ (1 - (b : ℝ)) * (Fintype.card X : ℝ)⌉₊) ∧
      (RC.1.filter (fun a => NPCC.Protocol.prefixLabelFinQ RC.1 P a = j ∧
        a.1 = dom j)).Nonempty ∧
      (RC.1.filter (fun a => NPCC.Protocol.prefixLabelFinQ RC.1 P a = j)).Nonempty := by
  have hs := classical_separation F b hb hD hprofile Q hQ x z hx0 hx1 hz hz1
    hqx hgap RC hRC P hPc hcost
  exact ⟨hs.1, DominantBlocks.exists_dominantBlockEquiv RC.1
    (NPCC.Protocol.prefixLabelFinQ RC.1 P) hRC.1 hgap hs.2⟩

omit [Nonempty X] in
/-- The column side of every separation prefix is nonempty as well: it
is the unchanged retained column set, whose lower density is positive. -/
theorem separation_columns_nonempty (Q : ℕ) (x z : ℝ) (hz : (18 / 25 : ℝ) ≤ z)
    (RC : Finset (Fin (2 ^ Q) × X) × Finset (Fin (2 ^ Q) → Y))
    (hRC : RC ∈ NPCC.bracketGE X Y (2 ^ Q) x z) : RC.2.Nonempty := by
  have hn : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  have hprod : 0 < (Fintype.card Y : ℝ) ^ (2 ^ Q) * z :=
    mul_pos (pow_pos hn _) (by linarith)
  have hceil : 0 < ⌈(Fintype.card Y : ℝ) ^ (2 ^ Q) * z⌉₊ := Nat.ceil_pos.mpr hprod
  exact Finset.card_pos.mp (hceil.trans_le hRC.2)

omit [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] in
/-- On a retained input the inherited row-prefix code really is its actual
transcript code, and at least `Q` charged bits are sent. Thus the preceding
nonempty label fibres are genuine depth-`Q` protocol rectangles, not labels
assigned to junk rows or early-terminating executions. -/
theorem prefix_labels_are_actual (Q : ℕ)
    (R : Finset (Fin (2 ^ Q) × X)) (C : Finset (Fin (2 ^ Q) → Y))
    (P : Protocol {a // a ∈ R} {c // c ∈ C} Bool)
    (hrow : NPCC.Protocol.FirstKRowBitsOn
      (Finset.univ : Finset {a // a ∈ R})
      (Finset.univ : Finset {c // c ∈ C}) Q P)
    (a : {a // a ∈ R}) (c : {c // c ∈ C}) :
    NPCC.Protocol.actualPrefixCodeRaw Q P a c = NPCC.Protocol.prefixLabelFinQ R P a.val ∧
      Q ≤ NPCC.Protocol.evalDepth P a c := by
  constructor
  · have hh := NPCC.Protocol.actualPrefixCodeRaw_eq_prefixCodeRaw_of_firstKRowBitsOn
      Finset.univ Finset.univ Q P hrow (Finset.mem_univ a) (Finset.mem_univ c)
    simpa only [NPCC.Protocol.prefixLabelFinQ, dif_pos a.property] using hh
  · have hh := NPCC.Protocol.evalDepth_eq_add_actualSubtreeAtRaw_of_firstKRowBitsOn
      Finset.univ Finset.univ Q P (NPCC.Protocol.actualPrefixCodeRaw Q P a c)
      hrow (Finset.mem_univ a) (Finset.mem_univ c) rfl
    omega

end ClassicalSeparation
end Paper2

#print axioms Paper2.ClassicalSeparation.profile_isRobust
#print axioms Paper2.ClassicalSeparation.classical_separation
#print axioms Paper2.ClassicalSeparation.classical_separation_with_bijection
#print axioms Paper2.ClassicalSeparation.prefix_labels_are_actual
