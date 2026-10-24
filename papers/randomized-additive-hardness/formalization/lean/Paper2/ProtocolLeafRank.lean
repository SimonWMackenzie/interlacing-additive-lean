import NPCC.SeedRank
import Paper2.IndexedMatrices

/-!
# The two-output protocol rank bound

Frozen Paper 2 v12, Appendix A, `cl:seed`: a protocol has enough one-output
leaves for the rank of its Boolean matrix and enough zero-output leaves for
the rank of its complement. This is the sharper, paired version of the
ordinary log-rank bound.

The finite-index theorem is reused from the frozen dependency
`vendor/npc-cc/NPCC/SeedRank.lean`, `NPCC.protocol_rank_pair_bound`.
Source SHA256: 7021D235FC29440F5B95B58EE47F1DFAAEF9DEEB93457483F8A3F9DCDAF5F592.
Its proof is a structural induction on actual Workspace protocols and uses
rank subadditivity, not the NP-hardness theorem or a source assumption.
The declarations below transport that checked theorem to arbitrary finite
indexed carriers, including repeated rows and empty carriers. Their axiom
surfaces are audited at the bottom of this module.
-/

namespace Paper2

open Workspace.Types.CommComplexity Workspace.Types.Protocol
open RankLeaves

variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype X] in
/-- The two Boolean output classes share one protocol tree, so the two real
ranks together are bounded by the number of available leaves. -/
theorem protocol_rank_pair_bound [Finite X] (P : Protocol X Y Bool) :
    (realMatrix P.eval).rank + (realMatrix fun x y => !(P.eval x y)).rank ≤
      2 ^ P.cost := by
  letI := Fintype.ofFinite X
  let eX := (Fintype.equivFin X).symm
  let eY := (Fintype.equivFin Y).symm
  let Q := Workspace.UpperBound.Protocol.comap eX eY P
  have h := NPCC.protocol_rank_pair_bound Q
  have hleft : Workspace.LogRankBound.matRf Q.eval =
      realMatrix (fun i j => P.eval (eX i) (eY j)) := by
    ext i j
    simp [Q, Workspace.UpperBound.Protocol.comap_eval,
      Workspace.LogRankBound.matRf, realMatrix]
  have hright : Workspace.LogRankBound.matRf (NPCC.notFun Q.eval) =
      realMatrix (fun i j => !(P.eval (eX i) (eY j))) := by
    ext i j
    simp [Q, Workspace.UpperBound.Protocol.comap_eval,
      Workspace.LogRankBound.matRf, NPCC.notFun, realMatrix]
  rw [hleft, hright] at h
  rw [pullback_rank_eq_of_surjective P.eval eX eY eX.surjective eY.surjective,
    pullback_rank_eq_of_surjective (fun x y => !(P.eval x y))
      eX eY eX.surjective eY.surjective] at h
  simpa [Q, Workspace.UpperBound.Protocol.comap_cost] using h

/-- Paired rank bound for actual deterministic communication complexity. -/
theorem rank_pair_le_two_pow_D (F : X → Y → Bool) :
    (realMatrix F).rank + (realMatrix fun x y => !(F x y)).rank ≤ 2 ^ D F := by
  have hne := Workspace.UpperBound.AchievableCosts_nonempty F
  obtain ⟨P, hcost, hcomp⟩ := Nat.sInf_mem hne
  have heval : P.eval = F := funext fun x => funext fun y => hcomp x y
  have h := protocol_rank_pair_bound P
  rwa [heval, hcost] at h

omit [Fintype X] in
/-- Complementation can reduce real rank by at most one. -/
theorem rank_le_complement_rank_add_one [Finite X] (F : X → Y → Bool) :
    (realMatrix F).rank ≤ (realMatrix fun x y => !(F x y)).rank + 1 := by
  letI := Fintype.ofFinite X
  let eX := (Fintype.equivFin X).symm
  let eY := (Fintype.equivFin Y).symm
  let A := Workspace.LogRankBound.matRf (fun i j => F (eX i) (eY j))
  let B := Workspace.LogRankBound.matRf (fun i j => !(F (eX i) (eY j)))
  let J := Workspace.LogRankBound.matRf (fun (_ : Fin (Fintype.card X))
      (_ : Fin (Fintype.card Y)) => true)
  have hdecomp : A = -B + J := by
    ext i j
    cases h : F (eX i) (eY j) <;>
      simp [A, B, J, Workspace.LogRankBound.matRf, h]
  have hbound : A.rank ≤ B.rank + 1 := by
    rw [hdecomp]
    calc
      (-B + J).rank ≤ (-B).rank + J.rank := Workspace.LogRankBound.rank_add_le _ _
      _ ≤ B.rank + 1 := by
        have hneg : (-B).rank ≤ B.rank := by
          simpa only [Matrix.neg_mul, Matrix.one_mul] using
            Matrix.rank_mul_le_right (-1 : Matrix (Fin (Fintype.card X))
              (Fin (Fintype.card X)) ℝ) B
        exact Nat.add_le_add hneg (Workspace.LogRankBound.rank_const_le_one true)
  change (realMatrix (fun i j => F (eX i) (eY j))).rank ≤
    (realMatrix (fun i j => !(F (eX i) (eY j)))).rank + 1 at hbound
  rw [pullback_rank_eq_of_surjective F eX eY eX.surjective eY.surjective,
    pullback_rank_eq_of_surjective (fun x y => !(F x y))
      eX eY eX.surjective eY.surjective] at hbound
  exact hbound

/-- The rank-only corollary used for restrictions of the lookup seed. -/
theorem two_mul_rank_le_two_pow_D_add_one (F : X → Y → Bool) :
    2 * (realMatrix F).rank ≤ 2 ^ D F + 1 := by
  have hp := rank_pair_le_two_pow_D F
  have hc := rank_le_complement_rank_add_one F
  omega

/-- An integral strict rank threshold forces the next bit of cost. -/
theorem cost_gt_of_two_mul_rank_gt (F : X → Y → Bool) (t : ℕ)
    (h : 2 ^ t + 1 < 2 * (realMatrix F).rank) : t < D F := by
  by_contra hnot
  have hD : D F ≤ t := Nat.le_of_not_gt hnot
  have hp := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hD
  have hb := two_mul_rank_le_two_pow_D_add_one F
  omega

#print axioms NPCC.protocol_rank_pair_bound
#print axioms protocol_rank_pair_bound
#print axioms rank_pair_le_two_pow_D
#print axioms rank_le_complement_rank_add_one
#print axioms two_mul_rank_le_two_pow_D_add_one
#print axioms cost_gt_of_two_mul_rank_gt

end Paper2
