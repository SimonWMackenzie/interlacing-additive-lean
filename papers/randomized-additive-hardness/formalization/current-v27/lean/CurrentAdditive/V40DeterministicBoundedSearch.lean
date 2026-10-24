import CurrentAdditive.V39PublicFloor
import CurrentAdditive.BoundedDyadicSearch

set_option autoImplicit false

namespace CurrentAdditive.V40DeterministicBoundedSearch

open V39GeneratedConstruction V38Schedule GeneratedCutoff PublicScheduleBoundedSearch

def test (p : SourceConstants) (n m L : Nat) : Bool :=
  generatedPass p.deletion L m (sourceDeltaV p.gamma p.degree n m) (sourceZeta p.gamma)

def start (floor n : Nat) : Nat := Nat.clog 2 (max floor n)

/-- The bounded executable scan. Its predicate uses the actual graph n,m;
the original formula size enters only through the lower search floor. -/
def search (p : SourceConstants) (floor n m : Nat) : Nat :=
  selectedLog (test p n m) (start floor n) (publicUpperLog p floor n)

theorem upper_passes (p : SourceConstants) (floor n m : Nat)
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ p.degree * n) :
    test p n m (publicUpperLog p floor n) = true := by
  apply (generatedPass_iff ..).2
  have hN : n ≤ generatedN (publicUpperLog p floor n) := by
    calc
      n ≤ max floor n := le_max_right _ _
      _ ≤ 2 ^ (Nat.clog 2 (max floor n)) := Nat.le_pow_clog (by decide) _
      _ ≤ generatedN (publicUpperLog p floor n) :=
        Nat.pow_le_pow_right (by decide) (le_max_left _ _)
  exact all_large_sources p.gamma p.deletion p.degree p.gamma_pos p.degree_pos
    p.deletion_pos p.deletion_le _ n m (le_max_right _ _) hn hN hlow hdegree

theorem search_spec (p : SourceConstants) (floor n m : Nat)
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ p.degree * n) :
    start floor n ≤ search p floor n m ∧
    search p floor n m ≤ publicUpperLog p floor n ∧
    test p n m (search p floor n m) = true ∧
    ∀ L, start floor n ≤ L → L < search p floor n m → test p n m L = false := by
  exact selectedLog_spec (test p n m) (start floor n) (publicUpperLog p floor n)
    (le_max_left _ _) (upper_passes p floor n m hn hlow hdegree)

/-- The bounded scan returns exactly the public first passing exponent.
The sufficient cutoff is used only as fuel, never as the returned parameter. -/
theorem search_eq_publicLogFrom (p : SourceConstants) (floor n m : Nat)
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ p.degree * n) :
    search p floor n m = publicLogFrom p floor n m hn hlow hdegree := by
  have hs := search_spec p floor n m hn hlow hdegree
  have hp := publicLogFrom_spec p floor n m hn hlow hdegree
  apply Nat.le_antisymm
  · by_contra h
    have hlt : publicLogFrom p floor n m hn hlow hdegree < search p floor n m := by omega
    have hf := hs.2.2.2 _ hp.1 hlt
    have ht : test p n m (publicLogFrom p floor n m hn hlow hdegree) = true :=
      (generatedPass_iff ..).2 hp.2
    simp [ht] at hf
  · change Nat.find (exists_passing_from p floor n m hn hlow hdegree) ≤ _
    exact Nat.find_min' _ ⟨hs.1, (generatedPass_iff ..).1 hs.2.2.1⟩

theorem bounded_scan_success (p : SourceConstants) (floor n m : Nat)
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ p.degree * n) :
    firstPassingAtMost (test p n m) (start floor n) (publicUpperLog p floor n) =
      some (publicLogFrom p floor n m hn hlow hdegree) := by
  obtain ⟨L, hL⟩ := firstPassingAtMost_complete (test p n m) (start floor n)
    (publicUpperLog p floor n) (le_max_left _ _)
    (upper_passes p floor n m hn hlow hdegree)
  have he : search p floor n m = L := by simp [search, selectedLog, hL]
  rw [← he, search_eq_publicLogFrom p floor n m hn hlow hdegree] at hL
  exact hL

/-- All attempted candidates, including failed candidates, lie in the same
effective dyadic envelope used by the actual source/output arithmetic. -/
theorem every_candidate_size (p : SourceConstants) (floor n L : Nat)
    (hn : 0 < n) (hL : L ≤ publicUpperLog p floor n) :
    generatedN L ≤ 2 * max (max floor n) (generatedN (cutoffLog p.degree p.deletion)) := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hL
  exact hp.trans (chosen_dyadic_bound (max floor n) p.degree p.deletion
    (lt_of_lt_of_le hn (le_max_right _ _)))

end CurrentAdditive.V40DeterministicBoundedSearch
