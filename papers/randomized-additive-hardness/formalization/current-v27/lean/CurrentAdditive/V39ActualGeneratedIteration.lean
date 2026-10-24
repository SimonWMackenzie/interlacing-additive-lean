import CurrentAdditive.V39ActualSuccessorNo
import CurrentAdditive.V39NumberedProfile
import CurrentAdditive.V39StoredSeedProfile
import CurrentAdditive.V39PublicFloor

/-! Exact NO cost and the recurring current profile for the same numbered
and stored constructors. Every round invokes the genuine seven-source
theorem; no desired next-round profile is supplied to the induction. -/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity V38Schedule
open CurrentAdditive.V39ActualGeneratedSource

theorem stored_step_numbered {q₁ q₂ s w Q ni : ℕ}
    [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]
    (μI : PositiveRationalLaw (Fin ni))
    (act : Fin ni → Fin q₂ → Option (Fin s)) (R : StoredMatrix) :
    (StoredMatrix.step (q₁:=q₁) (s:=s) (w:=w) (Q:=Q) μI act R).numbered=
      executableStep (q₁:=q₁) (s:=s) (w:=w) (Q:=Q) μI act R.numbered :=
  StoredMatrix.ofNumbered_numbered _

variable {L n m rep : ℕ}
  [NeZero (generatedQ₁ L)] [NeZero (generatedQ₂ L)] [NeZero (generatedS L)]
  [NeZero (generatedW L)] [NeZero (generatedQ L)]

theorem numberedStep_no_of_tests
    (code : CodeD 8192)
    (γ c : ℚ) (Δ : ℕ) (hc : 0 < c) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < n) (hm : 0 < m)
    (htests : GeneratedTests c L m (sourceDeltaV γ Δ n m) (sourceZeta γ))
    (hs : 4≤generatedS L)
    (hwidth : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false≠edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v≤Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ:ℝ)*m≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card:ℝ))
    (R : NumberedMatrix) (d : ℕ) (hd : 2≤d) (hD : D R.entry=d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R.entry
      R.rowLaw.toFiniteLaw R.colLaw.toFiniteLaw ((generatedRho L:ℚ):ℝ) (d:ℤ)) :
    let out := NumberedMatrix.step (q₁:=generatedQ₁ L) (s:=generatedS L)
      (w:=generatedW L) (Q:=generatedQ L) code
      (LiteralEdgeEncoder.indexedItemLaw (generatedS L) n hs hn)
      (activity hs hwidth edge) R
    D out.entry=d+(12*L+2*quarterCeil L)+1 ∧
    V38RestrictionProfiles.TwoThresholdProfile out.entry
      out.rowLaw.toFiniteLaw out.colLaw.toFiniteLaw ((generatedRho L:ℚ):ℝ)
      ((d+(12*L+2*quarterCeil L)+1:ℕ):ℤ) := by
  let src := sourceData (q₁:=generatedQ₁ L) (q₂:=generatedQ₂ L)
    (s:=generatedS L) code R.rowLaw R.colLaw
  let st := SourceData.streams (w:=generatedW L) code src
    (μI:=LiteralEdgeEncoder.indexedItemLaw (generatedS L) n hs hn)
  let out := SourceData.final (w:=generatedW L) (Q:=generatedQ L) code src
  have h := src.successor_no_of_tests γ c Δ hc hγ hΔ hn hm htests hs hwidth
    edge loopless hdegree gap R.entry d hd hD hp st out
  exact ⟨(src.numbered_cost st out R.entry _).trans h.1,
    src.numbered_profile st out R.entry _ _ _ h.2⟩

theorem numberedIterate_no_of_tests
    (code : CodeD 8192)
    (γ c : ℚ) (Δ : ℕ) (hc : 0 < c) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < n) (hm : 0 < m)
    (htests : GeneratedTests c L m (sourceDeltaV γ Δ n m) (sourceZeta γ))
    (hs : 4≤generatedS L)
    (hwidth : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false≠edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v≤Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ:ℝ)*m≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card:ℝ))
    (R : NumberedMatrix) (d : ℕ) (hd : 2≤d) (hD : D R.entry=d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R.entry
      R.rowLaw.toFiniteLaw R.colLaw.toFiniteLaw ((generatedRho L:ℚ):ℝ) (d:ℤ))
    (k : ℕ) :
    let out := NumberedMatrix.iterate (q₁:=generatedQ₁ L) (s:=generatedS L)
      (w:=generatedW L) (Q:=generatedQ L) code
      (LiteralEdgeEncoder.indexedItemLaw (generatedS L) n hs hn)
      (activity hs hwidth edge) k R
    D out.entry=d+k*(12*L+2*quarterCeil L+1) ∧
    V38RestrictionProfiles.TwoThresholdProfile out.entry
      out.rowLaw.toFiniteLaw out.colLaw.toFiniteLaw ((generatedRho L:ℚ):ℝ)
      ((d+k*(12*L+2*quarterCeil L+1):ℕ):ℤ) := by
  induction k with
  | zero => simpa only [NumberedMatrix.iterate,Nat.zero_mul,Nat.add_zero] using And.intro hD hp
  | succ k ih =>
    have h := numberedStep_no_of_tests code γ c Δ hc hγ hΔ hn hm htests hs hwidth
      edge loopless hdegree gap
      (NumberedMatrix.iterate (q₁:=generatedQ₁ L) (s:=generatedS L)
        (w:=generatedW L) (Q:=generatedQ L) code
        (LiteralEdgeEncoder.indexedItemLaw (generatedS L) n hs hn)
        (activity hs hwidth edge) k R)
      (d+k*(12*L+2*quarterCeil L+1)) (by omega) ih.1 ih.2
    have hsum : d+k*(12*L+2*quarterCeil L+1)+(12*L+2*quarterCeil L)+1=
        d+(k+1)*(12*L+2*quarterCeil L+1) := by
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    rw [hsum] at h
    exact h

theorem storedStep_no_of_tests
    (γ c : ℚ) (Δ : ℕ) (hc : 0 < c) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < n) (hm : 0 < m)
    (htests : GeneratedTests c L m (sourceDeltaV γ Δ n m) (sourceZeta γ))
    (hs : 4≤generatedS L)
    (hwidth : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false≠edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v≤Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ:ℝ)*m≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card:ℝ))
    (R : StoredMatrix) (d : ℕ) (hd : 2≤d) (hD : D R.entry=d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R.entry
      R.rowLaw.toFiniteLaw R.colLaw.toFiniteLaw ((generatedRho L:ℚ):ℝ) (d:ℤ)) :
    let out := StoredMatrix.step (q₁:=generatedQ₁ L) (s:=generatedS L)
      (w:=generatedW L) (Q:=generatedQ L)
      (LiteralEdgeEncoder.indexedItemLaw (generatedS L) n hs hn)
      (activity hs hwidth edge) R
    D out.entry=d+(12*L+2*quarterCeil L)+1 ∧
    V38RestrictionProfiles.TwoThresholdProfile out.entry
      out.rowLaw.toFiniteLaw out.colLaw.toFiniteLaw ((generatedRho L:ℚ):ℝ)
      ((d+(12*L+2*quarterCeil L)+1:ℕ):ℤ) := by
  have h := numberedStep_no_of_tests (executableCodeD 8192) γ c Δ hc hγ hΔ hn hm
    htests hs hwidth edge loopless hdegree gap R.numbered d hd hD hp
  change D (StoredMatrix.step _ _ R).numbered.entry=_ ∧
    V38RestrictionProfiles.TwoThresholdProfile (StoredMatrix.step _ _ R).numbered.entry
      (StoredMatrix.step _ _ R).numbered.rowLaw.toFiniteLaw
      (StoredMatrix.step _ _ R).numbered.colLaw.toFiniteLaw _ _
  rw [stored_step_numbered]
  exact h

theorem storedIterate_no_of_tests
    (γ c : ℚ) (Δ : ℕ) (hc : 0 < c) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < n) (hm : 0 < m)
    (htests : GeneratedTests c L m (sourceDeltaV γ Δ n m) (sourceZeta γ))
    (hs : 4≤generatedS L)
    (hwidth : generatedQ₂ L=LiteralEdgeEncoder.Width (generatedS L) m rep)
    (edge : Fin m → Bool → Fin n) (loopless : ∀ e, edge e false≠edge e true)
    (hdegree : ∀ v, SourceItems.degree edge v≤Δ)
    (gap : ∀ colour : Fin n → Fin 3, (γ:ℝ)*m≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card:ℝ))
    (R : StoredMatrix) (d : ℕ) (hd : 2≤d) (hD : D R.entry=d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R.entry
      R.rowLaw.toFiniteLaw R.colLaw.toFiniteLaw ((generatedRho L:ℚ):ℝ) (d:ℤ))
    (k : ℕ) :
    let out := StoredMatrix.iterate (q₁:=generatedQ₁ L) (s:=generatedS L)
      (w:=generatedW L) (Q:=generatedQ L)
      (LiteralEdgeEncoder.indexedItemLaw (generatedS L) n hs hn)
      (activity hs hwidth edge) k R
    D out.entry=d+k*(12*L+2*quarterCeil L+1) ∧
    V38RestrictionProfiles.TwoThresholdProfile out.entry
      out.rowLaw.toFiniteLaw out.colLaw.toFiniteLaw ((generatedRho L:ℚ):ℝ)
      ((d+k*(12*L+2*quarterCeil L+1):ℕ):ℤ) := by
  have h := numberedIterate_no_of_tests (executableCodeD 8192) γ c Δ hc hγ hΔ hn hm
    htests hs hwidth edge loopless hdegree gap R.numbered d hd hD hp k
  let out := StoredMatrix.iterate (q₁:=generatedQ₁ L) (s:=generatedS L)
    (w:=generatedW L) (Q:=generatedQ L)
    (LiteralEdgeEncoder.indexedItemLaw (generatedS L) n hs hn)
    (activity hs hwidth edge) k R
  change D out.numbered.entry=_ ∧ V38RestrictionProfiles.TwoThresholdProfile out.numbered.entry
    out.numbered.rowLaw.toFiniteLaw out.numbered.colLaw.toFiniteLaw _ _
  dsimp [out]
  rw [StoredMatrix.iterate_numbered]
  exact h

end CurrentAdditive.V39GeneratedConstruction

#print axioms CurrentAdditive.V39GeneratedConstruction.numberedStep_no_of_tests
#print axioms CurrentAdditive.V39GeneratedConstruction.numberedIterate_no_of_tests
#print axioms CurrentAdditive.V39GeneratedConstruction.storedStep_no_of_tests
#print axioms CurrentAdditive.V39GeneratedConstruction.storedIterate_no_of_tests
