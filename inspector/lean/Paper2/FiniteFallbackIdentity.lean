import Paper2.LookupSeed

/-!
# Frozen Appendix D identity fallback: exact fixed-leaf-output cost

Only the literal square identity matrix and the one-row exceptional output
are treated here. No graph decision procedure or cutoff/runtime claim is made.
-/

namespace Paper2.FiniteFallbackIdentity

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open RankLeaves

/-- The literal square Boolean identity matrix, with its indicated carriers. -/
def identityMatrix (n : ℕ) : Fin n → Fin n → Bool :=
  fun i j => decide (i = j)

/-- Every diagonal one has its own independent row in the real matrix. -/
theorem rank_identity (n : ℕ) : (realMatrix (identityMatrix n)).rank = n := by
  apply le_antisymm
  · simpa using (realMatrix (identityMatrix n)).rank_le_card_width
  · have h := card_le_rank_of_zero_witness (realMatrix (identityMatrix n))
      id id (by intro i; simp [realMatrix, identityMatrix])
      (by intro i j hij; simp [realMatrix, identityMatrix, hij])
    simpa using h

/-- For at least two indices, the zero-output matrix has positive rank.
The stronger full complement-rank statement is not needed for exact cost:
the paired leaf bound already exceeds the previous power of two. -/
theorem complement_rank_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < (realMatrix (fun i j : Fin n => !(identityMatrix n i j))).rank := by
  have h := rank_le_complement_rank_add_one (identityMatrix n)
  rw [rank_identity] at h
  omega

/-- The upper bound announces Alice's `k-1`-bit index and then Bob returns
the one answer bit. -/
theorem identity_D_le (k : ℕ) (hk : 1 ≤ k) :
    D (identityMatrix (2 ^ (k - 1))) ≤ k := by
  let n := 2 ^ (k - 1)
  let P : Fin n → Protocol (Fin n) (Fin n) Bool := fun i =>
    .bNode (fun j => decide (i = j)) (.leaf false) (.leaf true)
  have h := Workspace.UpperBound.D_le_announce
    (identityMatrix n) (Fin n) id P (k - 1) 1
    (by simp [n])
    (by
      intro i x y hix
      subst i
      simp [P, identityMatrix, Protocol.eval])
    (by intro i; rfl)
  change D (identityMatrix (2 ^ (k - 1))) ≤ k
  simpa only [n] using (h.trans (by omega : k - 1 + 1 ≤ k))

/-- Exact unrestricted deterministic complexity in the fixed-output-leaf
protocol model, for the literal `2^(k-1)`-square identity matrix. -/
theorem identity_D (k : ℕ) (hk : 2 ≤ k) :
    D (identityMatrix (2 ^ (k - 1))) = k := by
  apply le_antisymm (identity_D_le k (by omega))
  let n := 2 ^ (k - 1)
  have hn : 2 ≤ n := by
    dsimp [n]
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2)
      (by omega : 1 ≤ k - 1)
  have hrank := rank_identity n
  have hzero := complement_rank_pos n hn
  have hpair := rank_pair_le_two_pow_D (identityMatrix n)
  rw [hrank] at hpair
  have hlt : n < 2 ^ D (identityMatrix n) := by omega
  have hprev : k - 1 < D (identityMatrix n) := by
    by_contra hnot
    have hle : D (identityMatrix n) ≤ k - 1 := Nat.le_of_not_gt hnot
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hle
    dsimp [n] at hlt
    omega
  change k ≤ D (identityMatrix n)
  omega

/-- Frozen Appendix D's exceptional one-row output for `k=1`. -/
def oneRow : Fin 1 → Fin 2 → Bool := fun _ j => decide (j = 1)

theorem oneRow_D : D oneRow = 1 := by
  have hupper : D oneRow ≤ 1 := by
    let P : Protocol (Fin 1) (Fin 2) Bool :=
      .bNode (fun j => decide (j = 1)) (.leaf false) (.leaf true)
    apply Nat.sInf_le
    exact ⟨P, rfl, by intro i j; simp [P, oneRow, Protocol.eval]⟩
  have hnonzero : 0 < D oneRow := by
    by_contra hnot
    have hD : D oneRow = 0 := by omega
    have hne := Workspace.UpperBound.AchievableCosts_nonempty oneRow
    obtain ⟨P, hcost, hcomp⟩ := Nat.sInf_mem hne
    change P.cost = D oneRow at hcost
    rw [hD] at hcost
    cases P with
    | leaf z =>
        have h0 := hcomp 0 0
        have h1 := hcomp 0 1
        simp [oneRow, Protocol.eval] at h0 h1
        cases z <;> simp_all
    | aNode a l r => simp [Protocol.cost] at hcost
    | bNode b l r => simp [Protocol.cost] at hcost
  omega

#print axioms rank_identity
#print axioms complement_rank_pos
#print axioms identity_D
#print axioms oneRow_D

end Paper2.FiniteFallbackIdentity
