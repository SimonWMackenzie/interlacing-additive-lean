import CurrentAdditive.V42GeneratedNo

/-! Induction on the identical v42 stored/numbered seven-call constructor.
The next cost and recurring profile come from successor_no at each round. -/
namespace CurrentAdditive.V42GeneratedNo

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open V42Schedule V39GeneratedConstruction

local instance iterSNZ (k : ℕ) : NeZero (s k) := ⟨(s_pos k).ne'⟩
local instance iterQ₂NZ (k : ℕ) : NeZero (q₂ k (4*k)) := ⟨(q₂_pos k (4*k)).ne'⟩
local instance iterWNZ (k : ℕ) : NeZero (w k) := ⟨(w_pos k).ne'⟩
local instance iterQNZ (k : ℕ) : NeZero (Q k) := ⟨(Q_pos k).ne'⟩

variable {k n m rep : ℕ} [NeZero (q₁ k)]

theorem numberedIterate_no
    (γ : ℚ) (Δ : ℕ) (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m)
    (hk : commonCutoff (V38Schedule.sourceDeltaV γ Δ n m) (V38Schedule.sourceZeta γ) Δ ≤ k)
    (hk2 : 2 ≤ k) (hs : 4 ≤ s k)
    (hwidth : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false≠edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ:ℝ)*m≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card:ℝ))
    (R : NumberedMatrix) (d : ℕ) (hd : 2 ≤ d) (hD : D R.entry=d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R.entry R.rowLaw.toFiniteLaw R.colLaw.toFiniteLaw
      (rho (4*k):ℝ) (d:ℤ)) (rounds : ℕ) :
    let out := V42GeneratedConstruction.numberedIterate k (4*k) hk2
      (LiteralEdgeEncoder.indexedItemLaw (s k) n hs hn) (graphActivity (by omega) hwidth edge) rounds R
    D out.entry=d+rounds*(40*k+1) ∧ V38RestrictionProfiles.TwoThresholdProfile out.entry
      out.rowLaw.toFiniteLaw out.colLaw.toFiniteLaw (rho (4*k):ℝ) ((d+rounds*(40*k+1):ℕ):ℤ) := by
  induction rounds with
  | zero =>
    simpa only [V42GeneratedConstruction.numberedIterate,executableIterate,NumberedMatrix.iterate,
      Nat.zero_mul,Nat.add_zero] using And.intro hD hp
  | succ rounds ih =>
    have h := numberedStep_no γ Δ hγ hΔ hn hm hk hk2 hs hwidth edge loopless hdegree gap
      (V42GeneratedConstruction.numberedIterate k (4*k) hk2
        (LiteralEdgeEncoder.indexedItemLaw (s k) n hs hn) (graphActivity (by omega) hwidth edge) rounds R)
      (d+rounds*(40*k+1)) (by omega) ih.1 ih.2
    have he : d+rounds*(40*k+1)+40*k+1=d+(rounds+1)*(40*k+1) := by ring
    dsimp only at h
    rw [he] at h
    exact h

theorem storedIterate_no
    (γ : ℚ) (Δ : ℕ) (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m)
    (hk : commonCutoff (V38Schedule.sourceDeltaV γ Δ n m) (V38Schedule.sourceZeta γ) Δ ≤ k)
    (hk2 : 2 ≤ k) (hs : 4 ≤ s k)
    (hwidth : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false≠edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ:ℝ)*m≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card:ℝ))
    (R : StoredMatrix) (d : ℕ) (hd : 2 ≤ d) (hD : D R.entry=d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R.entry R.rowLaw.toFiniteLaw R.colLaw.toFiniteLaw
      (rho (4*k):ℝ) (d:ℤ)) (rounds : ℕ) :
    let out := V42GeneratedConstruction.storedIterate k (4*k) hk2
      (LiteralEdgeEncoder.indexedItemLaw (s k) n hs hn) (graphActivity (by omega) hwidth edge) rounds R
    D out.entry=d+rounds*(40*k+1) ∧ V38RestrictionProfiles.TwoThresholdProfile out.entry
      out.rowLaw.toFiniteLaw out.colLaw.toFiniteLaw (rho (4*k):ℝ) ((d+rounds*(40*k+1):ℕ):ℤ) := by
  have h := numberedIterate_no γ Δ hγ hΔ hn hm hk hk2 hs hwidth edge loopless hdegree gap
    R.numbered d hd hD hp rounds
  have he := V42GeneratedConstruction.storedIterate_numbered k (4*k) hk2
    (LiteralEdgeEncoder.indexedItemLaw (s k) n hs hn) (graphActivity (by omega) hwidth edge) rounds R
  have h' :
      let out := (V42GeneratedConstruction.storedIterate k (4*k) hk2
        (LiteralEdgeEncoder.indexedItemLaw (s k) n hs hn) (graphActivity (by omega) hwidth edge) rounds R).numbered
      D out.entry=d+rounds*(40*k+1) ∧ V38RestrictionProfiles.TwoThresholdProfile out.entry
        out.rowLaw.toFiniteLaw out.colLaw.toFiniteLaw (rho (4*k):ℝ) ((d+rounds*(40*k+1):ℕ):ℤ) := by
    rw [he]
    exact h
  exact h'

omit [NeZero (q₁ k)] in
theorem graphRun_no
    (γ : ℚ) (Δ : ℕ) (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m)
    (hk : commonCutoff (V38Schedule.sourceDeltaV γ Δ n m) (V38Schedule.sourceZeta γ) Δ ≤ k)
    (hk2 : 2 ≤ k)
    (hwidth : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false≠edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ:ℝ)*m≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card:ℝ))
    (rounds : ℕ) :
    let out := V42GeneratedConstruction.graphRun k (4*k) hk2 hn hwidth edge (4*k) rounds
    D out.entry=LookupSeed.exponent (4*k)+1+rounds*(40*k+1) ∧
    V38RestrictionProfiles.TwoThresholdProfile out.entry out.rowLaw.toFiniteLaw out.colLaw.toFiniteLaw
      (rho (4*k):ℝ) ((LookupSeed.exponent (4*k)+1+rounds*(40*k+1):ℕ):ℤ) := by
  have hs := V42GeneratedConstruction.s_ge_four k hk2
  letI : NeZero (q₁ k) := ⟨by have h:=hs; unfold q₁; omega⟩
  have hseed : V38RestrictionProfiles.TwoThresholdProfile (storedLookupSeed (4*k)).entry
      (storedLookupSeed (4*k)).rowLaw.toFiniteLaw (storedLookupSeed (4*k)).colLaw.toFiniteLaw
      (rho (4*k):ℝ) ((LookupSeed.exponent (4*k)+1:ℕ):ℤ) := by
    simpa only [rho,V38Schedule.generatedRho,V38Schedule.generatedN,Nat.cast_pow,Nat.cast_ofNat] using storedLookupSeed_profile (4*k)
  have h := storedIterate_no γ Δ hγ hΔ hn hm hk hk2 hs hwidth edge loopless hdegree gap
    (storedLookupSeed (4*k)) (LookupSeed.exponent (4*k)+1)
    (by
      have hp : 0 < LookupSeed.exponent (4*k) := by
        unfold LookupSeed.exponent
        apply Nat.clog_pos (by decide)
        omega
      omega) (storedLookupSeed_cost (4*k)) hseed rounds
  exact h

def generatedB (k rounds : ℕ) : ℕ := LookupSeed.exponent (4*k)+1+rounds*(40*k)
def generatedH (k rounds : ℕ) : ℕ := generatedB k rounds+rounds

theorem generatedH_eq (k rounds : ℕ) :
    LookupSeed.exponent (4*k)+1+rounds*(40*k+1)=generatedH k rounds := by
  unfold generatedH generatedB
  ring

omit [NeZero (q₁ k)] in
theorem graphRun_yes_threshold (hk2 : 2 ≤ k) (hn : 0 < n)
    (hwidth : q₂ k (4*k)=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (rounds : ℕ) (colour : Fin n → Fin 3)
    (proper : ∀ e, colour (edge e false)≠colour (edge e true)) :
    D (V42GeneratedConstruction.graphRun k (4*k) hk2 hn hwidth edge (4*k) rounds).entry ≤
      generatedB k rounds := by
  have h := V42GeneratedConstruction.graphRun_yes k (4*k) hk2 hn hwidth edge
    (4*k) rounds colour proper
  simpa only [V42GeneratedConstruction.generated_overhead,generatedB] using h

#print axioms numberedIterate_no
#print axioms storedIterate_no
#print axioms graphRun_no
#print axioms graphRun_yes_threshold

end CurrentAdditive.V42GeneratedNo



