import CurrentAdditive.V39PublicGeneratedSchedule

/-! The deterministic ETH schedule must start at max(original formula N,n),
where n is the actual copied graph vertex count. These are separate inputs.
The generated tests still use the ACTUAL graph n,m; increasing the search
floor does not change its graph, item law, or source density.
-/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 V38Schedule GeneratedCutoff

def publicUpperLog (p : SourceConstants) (floor n : ℕ) : ℕ :=
  max (Nat.clog 2 (max floor n)) (cutoffLog p.degree p.deletion)

theorem exists_passing_from (p : SourceConstants) (floor n m : ℕ)
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n) :
    ∃ L, Nat.clog 2 (max floor n) ≤ L ∧
      GeneratedTests p.deletion L m (sourceDeltaV p.gamma p.degree n m)
        (sourceZeta p.gamma) := by
  let L := publicUpperLog p floor n
  refine ⟨L, le_max_left _ _, ?_⟩
  have hnN : n ≤ generatedN L := by
    calc
      n ≤ max floor n := le_max_right _ _
      _ ≤ 2^(Nat.clog 2 (max floor n)) := Nat.le_pow_clog (by decide) _
      _ ≤ generatedN L := Nat.pow_le_pow_right (by decide) (le_max_left _ _)
  exact all_large_sources p.gamma p.deletion p.degree p.gamma_pos p.degree_pos
    p.deletion_pos p.deletion_le L n m (le_max_right _ _) hn hnN hlow hdegree

/-- Actual least passing exponent above the explicitly supplied floor.
There is no assumption that this least passing value exceeds the sufficient
all-large cutoff. -/
def publicLogFrom (p : SourceConstants) (floor n m : ℕ)
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n) : ℕ :=
  firstGeneratedExponent p.deletion (max floor n) m
    (sourceDeltaV p.gamma p.degree n m) (sourceZeta p.gamma)
      (exists_passing_from p floor n m hn hlow hdegree)

theorem publicLogFrom_spec (p : SourceConstants) (floor n m : ℕ)
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n) :
    Nat.clog 2 (max floor n) ≤ publicLogFrom p floor n m hn hlow hdegree ∧
      GeneratedTests p.deletion (publicLogFrom p floor n m hn hlow hdegree) m
        (sourceDeltaV p.gamma p.degree n m) (sourceZeta p.gamma) :=
  Nat.find_spec (exists_passing_from p floor n m hn hlow hdegree)

theorem publicLogFrom_size (p : SourceConstants) (floor n m : ℕ)
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n) :
    max floor n ≤ generatedN (publicLogFrom p floor n m hn hlow hdegree) :=
  (Nat.le_pow_clog (by decide) _).trans
    (Nat.pow_le_pow_right (by decide) (publicLogFrom_spec p floor n m hn hlow hdegree).1)

theorem publicLogFrom_le_upper (p : SourceConstants) (floor n m : ℕ)
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n) :
    publicLogFrom p floor n m hn hlow hdegree ≤ publicUpperLog p floor n := by
  apply Nat.find_min'
  refine ⟨le_max_left _ _, ?_⟩
  have hnN : n ≤ generatedN (publicUpperLog p floor n) := by
    calc
      n ≤ max floor n := le_max_right _ _
      _ ≤ 2^(Nat.clog 2 (max floor n)) := Nat.le_pow_clog (by decide) _
      _ ≤ generatedN (publicUpperLog p floor n) :=
        Nat.pow_le_pow_right (by decide) (le_max_left _ _)
  exact all_large_sources p.gamma p.deletion p.degree p.gamma_pos p.degree_pos
    p.deletion_pos p.deletion_le _ n m (le_max_right _ _) hn hnN hlow hdegree

theorem publicLogFrom_dyadic_bound (p : SourceConstants) (floor n m : ℕ)
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n) :
    generatedN (publicLogFrom p floor n m hn hlow hdegree) ≤
      2*max (max floor n) (generatedN (cutoffLog p.degree p.deletion)) := by
  have h := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
    (publicLogFrom_le_upper p floor n m hn hlow hdegree)
  exact h.trans (chosen_dyadic_bound (max floor n) p.degree p.deletion (by omega))

def publicGraphRunFrom (p : SourceConstants) (floor : ℕ) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) : StoredMatrix := by
  let L := publicLogFrom p floor n m hn hlow hdegree
  have ht := (publicLogFrom_spec p floor n m hn hlow hdegree).2
  haveI : NeZero (generatedS L) := ⟨by unfold generatedS; positivity⟩
  haveI : NeZero (generatedQ₂ L) := ⟨by unfold generatedQ₂ generatedN; positivity⟩
  haveI : NeZero (generatedW L) := ⟨by unfold generatedW generatedN; positivity⟩
  haveI : NeZero (generatedQ L) := ⟨by unfold generatedQ generatedN; positivity⟩
  exact graphRun (w := generatedW L) (Q := generatedQ L)
    (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht) edge L k

def publicGraphThresholdFrom (p : SourceConstants) (floor n m : ℕ)
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n) (k : ℕ) : ℕ :=
  let L := publicLogFrom p floor n m hn hlow hdegree
  Paper2.LookupSeed.exponent L+1+k*(12*L+2*quarterCeil L)

theorem publicGraphRunFrom_yes (p : SourceConstants) (floor : ℕ) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) (colour : Fin n → Fin 3)
    (proper : ∀ j, colour (edge j false) ≠ colour (edge j true)) :
    Workspace.Types.CommComplexity.D (publicGraphRunFrom p floor hn hlow hdegree edge k).entry ≤
      publicGraphThresholdFrom p floor n m hn hlow hdegree k := by
  let L := publicLogFrom p floor n m hn hlow hdegree
  have ht := (publicLogFrom_spec p floor n m hn hlow hdegree).2
  haveI : NeZero (generatedS L) := ⟨by unfold generatedS; positivity⟩
  haveI : NeZero (generatedQ₂ L) := ⟨by unfold generatedQ₂ generatedN; positivity⟩
  haveI : NeZero (generatedW L) := ⟨by unfold generatedW generatedN; positivity⟩
  haveI : NeZero (generatedQ L) := ⟨by unfold generatedQ generatedN; positivity⟩
  have hy := graphRun_yes (w := generatedW L) (Q := generatedQ L)
    (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht)
    edge L k colour proper
  change Workspace.Types.CommComplexity.D
    (publicGraphRunFrom p floor hn hlow hdegree edge k).entry ≤
      Paper2.LookupSeed.exponent L+1+
      k*graphIncrement (generatedS L) (generatedQ₂ L) (generatedW L) (generatedQ L) at hy
  rw [generated_graph_increment] at hy
  exact hy

end CurrentAdditive.V39GeneratedConstruction

#print axioms CurrentAdditive.V39GeneratedConstruction.publicLogFrom_dyadic_bound
#print axioms CurrentAdditive.V39GeneratedConstruction.publicGraphRunFrom_yes
