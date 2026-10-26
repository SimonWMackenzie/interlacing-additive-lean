import CurrentAdditive.V39PublicGeneratedSchedule

/-! Promise-independent upper protocols on the same functional constructor.
This supplies the universal half of the current amplifier contract; the YES
half is already publicGraphRun_yes. There is no source-profile premise.
-/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 V38Schedule Workspace.Types.CommComplexity
open CurrentAdditive.LiteralEdgeEncoder

variable {q₁ q₂ s w Q ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]

theorem numberedIterate_upper (c : CodeD 8192)
    (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : NumberedMatrix) (k : ℕ) :
    D (NumberedMatrix.iterate (q₁ := q₁) (s := s) (w := w) (Q := Q)
        c μI activity k R).entry ≤
      D R.entry+k*(Nat.clog 2 s+Nat.clog 2 q₂+Nat.clog 2 (q₁+s+1)+
        Nat.clog 2 w+Nat.clog 2 Q) := by
  induction k with
  | zero =>
    simp only [NumberedMatrix.iterate, Nat.zero_mul, Nat.add_zero]
    exact Nat.le_refl _
  | succ k ih =>
    have h := NumberedMatrix.step_upper (q₁ := q₁) (s := s) (w := w) (Q := Q)
      c μI activity (NumberedMatrix.iterate (q₁ := q₁) (s := s) (w := w) (Q := Q)
        c μI activity k R)
    simpa only [NumberedMatrix.iterate, Nat.succ_mul, Nat.add_assoc]
      using h.trans (Nat.add_le_add_right ih _)

theorem storedIterate_upper (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : StoredMatrix) (k : ℕ) :
    D (StoredMatrix.iterate (q₁ := q₁) (s := s) (w := w) (Q := Q)
        μI activity k R).entry ≤
      D R.entry+k*(Nat.clog 2 s+Nat.clog 2 q₂+Nat.clog 2 (q₁+s+1)+
        Nat.clog 2 w+Nat.clog 2 Q) := by
  have h := numberedIterate_upper (q₁ := q₁) (s := s) (w := w) (Q := Q)
    (executableCodeD 8192) μI activity R.numbered k
  change D (executableIterate (q₁ := q₁) (s := s) (w := w) (Q := Q)
    μI activity k R.numbered).entry ≤ _ at h
  rw [← StoredMatrix.iterate_numbered] at h
  exact h

theorem publicGraphRun_universal (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :
    D (publicGraphRun p hn hlow hdegree edge k).entry ≤
      publicGraphThreshold p n m hn hlow hdegree k+k := by
  let L := publicLog p n m hn hlow hdegree
  have ht := (publicLog_spec p n m hn hlow hdegree).2
  have hs : 4 ≤ generatedS L := passing_s_ge_four _ _ _ _ _ ht
  haveI : NeZero (generatedS L) := ⟨by unfold generatedS; positivity⟩
  haveI : NeZero (generatedS L-2) := ⟨by omega⟩
  haveI : NeZero (generatedQ₂ L) := ⟨by unfold generatedQ₂ generatedN; positivity⟩
  haveI : NeZero (generatedW L) := ⟨by unfold generatedW generatedN; positivity⟩
  haveI : NeZero (generatedQ L) := ⟨by unfold generatedQ generatedN; positivity⟩
  have h := storedIterate_upper (q₁ := generatedS L-2) (s := generatedS L)
    (w := generatedW L) (Q := generatedQ L) (indexedItemLaw _ n hs hn)
    (graphActivity (by omega) (passing_repetition_eq _ _ _ _ _ ht) edge)
    (storedLookupSeed L) k
  rw [storedLookupSeed_cost] at h
  have htail : Nat.clog 2 (generatedS L-2+generatedS L+1) ≤
      quarterCeil L+1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]
    change generatedS L-2+generatedS L+1 ≤ generatedS L*2
    omega
  have hslog : Nat.clog 2 (generatedS L) = quarterCeil L := by
    simp only [generatedS, Nat.clog_pow, one_lt_two]
  have hh := generated_graph_increment L
  have hinc : Nat.clog 2 (generatedS L)+Nat.clog 2 (generatedQ₂ L)+
      Nat.clog 2 (generatedS L-2+generatedS L+1)+Nat.clog 2 (generatedW L)+
      Nat.clog 2 (generatedQ L) ≤ 12*L+2*quarterCeil L+1 := by
    unfold graphIncrement at hh
    rw [hslog] at hh ⊢
    omega
  change D (publicGraphRun p hn hlow hdegree edge k).entry ≤
    Paper2.LookupSeed.exponent L+1+k*(12*L+2*quarterCeil L)+k
  change D (publicGraphRun p hn hlow hdegree edge k).entry ≤
    Paper2.LookupSeed.exponent L+1+k*(Nat.clog 2 (generatedS L)+
      Nat.clog 2 (generatedQ₂ L)+Nat.clog 2 (generatedS L-2+generatedS L+1)+
      Nat.clog 2 (generatedW L)+Nat.clog 2 (generatedQ L)) at h
  have hmul := Nat.mul_le_mul_left k hinc
  calc
    _ ≤ Paper2.LookupSeed.exponent L+1+k*(Nat.clog 2 (generatedS L)+
      Nat.clog 2 (generatedQ₂ L)+Nat.clog 2 (generatedS L-2+generatedS L+1)+
      Nat.clog 2 (generatedW L)+Nat.clog 2 (generatedQ L)) := h
    _ ≤ Paper2.LookupSeed.exponent L+1+k*(12*L+2*quarterCeil L+1) :=
      Nat.add_le_add_left hmul _
    _ = Paper2.LookupSeed.exponent L+1+k*(12*L+2*quarterCeil L)+k := by ring

end CurrentAdditive.V39GeneratedConstruction

#print axioms CurrentAdditive.V39GeneratedConstruction.publicGraphRun_universal
