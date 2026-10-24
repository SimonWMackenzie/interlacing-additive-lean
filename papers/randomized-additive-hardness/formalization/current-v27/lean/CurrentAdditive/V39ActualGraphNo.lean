import CurrentAdditive.V39ActualGeneratedIteration

/-! The exact NO recurrence for the literal stored graph constructor,
including the public first-passing parameter above the original input
floor. The same stored matrix has its computed laws and recurring profile. -/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity V38Schedule
open Paper2.LookupSeed
open CurrentAdditive.V39ActualGeneratedSource

private theorem exponent_pos (L : ℕ) : 0 < exponent L := by
  have h := width_admissible L
  by_contra hn
  have hz : exponent L=0 := by omega
  simp only [width,hz,pow_zero] at h
  omega

theorem generatedGraphRun_no_of_tests {L n m rep : ℕ}
    [NeZero (generatedS L)] [NeZero (generatedQ₂ L)]
    [NeZero (generatedW L)] [NeZero (generatedQ L)]
    (γ c : ℚ) (Δ : ℕ) (hc : 0 < c) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < n) (hm : 0 < m)
    (htests : GeneratedTests c L m (sourceDeltaV γ Δ n m) (sourceZeta γ))
    (hs : 4≤generatedS L)
    (hwidth : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false≠edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v≤Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ:ℝ)*m≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card:ℝ))
    (k : ℕ) :
    let out := graphRun (w:=generatedW L) (Q:=generatedQ L) hs hn hwidth edge L k
    D out.entry=exponent L+1+k*(12*L+2*quarterCeil L+1) ∧
    V38RestrictionProfiles.TwoThresholdProfile out.entry
      out.rowLaw.toFiniteLaw out.colLaw.toFiniteLaw ((generatedRho L:ℚ):ℝ)
      ((exponent L+1+k*(12*L+2*quarterCeil L+1):ℕ):ℤ) := by
  haveI : NeZero (generatedQ₁ L) := ⟨by dsimp [generatedQ₁]; omega⟩
  exact storedIterate_no_of_tests γ c Δ hc hγ hΔ hn hm htests hs hwidth
    edge loopless hdegree gap (storedLookupSeed L) (exponent L+1)
    (by have h:=exponent_pos L; omega) (storedLookupSeed_cost L) (storedLookupSeed_profile L) k

theorem publicGraphRunFrom_no (p : SourceConstants) (floor : ℕ) {n m : ℕ}
    (hn : 0 < n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false≠edge e true)
    (hlocal : ∀ v, SourceItems.degree edge v≤p.degree)
    (gap : ∀ colour : Fin n → Fin 3, (p.gamma:ℝ)*m≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card:ℝ))
    (k : ℕ) :
    D (publicGraphRunFrom p floor hn hlow hdegree edge k).entry=
      publicGraphThresholdFrom p floor n m hn hlow hdegree k+k ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (publicGraphRunFrom p floor hn hlow hdegree edge k).entry
      (publicGraphRunFrom p floor hn hlow hdegree edge k).rowLaw.toFiniteLaw
      (publicGraphRunFrom p floor hn hlow hdegree edge k).colLaw.toFiniteLaw
      ((generatedRho (publicLogFrom p floor n m hn hlow hdegree):ℚ):ℝ)
      ((publicGraphThresholdFrom p floor n m hn hlow hdegree k+k:ℕ):ℤ) := by
  let L := publicLogFrom p floor n m hn hlow hdegree
  have ht := (publicLogFrom_spec p floor n m hn hlow hdegree).2
  haveI : NeZero (generatedS L) := ⟨by unfold generatedS; positivity⟩
  haveI : NeZero (generatedQ₂ L) := ⟨by unfold generatedQ₂ generatedN; positivity⟩
  haveI : NeZero (generatedW L) := ⟨by unfold generatedW generatedN; positivity⟩
  haveI : NeZero (generatedQ L) := ⟨by unfold generatedQ generatedN; positivity⟩
  have h := generatedGraphRun_no_of_tests p.gamma p.deletion p.degree
    p.deletion_pos p.gamma_pos p.degree_pos hn (by omega) ht
    (passing_s_ge_four _ _ _ _ _ ht) (passing_repetition_eq _ _ _ _ _ ht)
    edge loopless hlocal gap k
  have hsum : exponent L+1+k*(12*L+2*quarterCeil L+1)=
      publicGraphThresholdFrom p floor n m hn hlow hdegree k+k := by
    dsimp [publicGraphThresholdFrom]
    rw [Nat.mul_add,Nat.mul_one]
    simp only [L,Nat.add_assoc]
  rw [hsum] at h
  exact h

theorem publicGraphRun_no (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false≠edge e true)
    (hlocal : ∀ v, SourceItems.degree edge v≤p.degree)
    (gap : ∀ colour : Fin n → Fin 3, (p.gamma:ℝ)*m≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card:ℝ))
    (k : ℕ) :
    D (publicGraphRun p hn hlow hdegree edge k).entry=
      publicGraphThreshold p n m hn hlow hdegree k+k ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (publicGraphRun p hn hlow hdegree edge k).entry
      (publicGraphRun p hn hlow hdegree edge k).rowLaw.toFiniteLaw
      (publicGraphRun p hn hlow hdegree edge k).colLaw.toFiniteLaw
      ((generatedRho (publicLog p n m hn hlow hdegree):ℚ):ℝ)
      ((publicGraphThreshold p n m hn hlow hdegree k+k:ℕ):ℤ) := by
  let L := publicLog p n m hn hlow hdegree
  have ht := (publicLog_spec p n m hn hlow hdegree).2
  haveI : NeZero (generatedS L) := ⟨by unfold generatedS; positivity⟩
  haveI : NeZero (generatedQ₂ L) := ⟨by unfold generatedQ₂ generatedN; positivity⟩
  haveI : NeZero (generatedW L) := ⟨by unfold generatedW generatedN; positivity⟩
  haveI : NeZero (generatedQ L) := ⟨by unfold generatedQ generatedN; positivity⟩
  have h := generatedGraphRun_no_of_tests p.gamma p.deletion p.degree
    p.deletion_pos p.gamma_pos p.degree_pos hn (by omega) ht
    (passing_s_ge_four _ _ _ _ _ ht) (passing_repetition_eq _ _ _ _ _ ht)
    edge loopless hlocal gap k
  have hsum : exponent L+1+k*(12*L+2*quarterCeil L+1)=
      publicGraphThreshold p n m hn hlow hdegree k+k := by
    dsimp [publicGraphThreshold]
    rw [Nat.mul_add,Nat.mul_one]
    simp only [L,Nat.add_assoc]
  rw [hsum] at h
  exact h

end CurrentAdditive.V39GeneratedConstruction

#print axioms CurrentAdditive.V39GeneratedConstruction.generatedGraphRun_no_of_tests
#print axioms CurrentAdditive.V39GeneratedConstruction.publicGraphRunFrom_no
#print axioms CurrentAdditive.V39GeneratedConstruction.publicGraphRun_no
