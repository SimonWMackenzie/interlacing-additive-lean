import CurrentAdditive.V39RLoopPublicCaps
import CurrentAdditive.V39RequestStepClock
import Paper2.SCBody

set_option maxHeartbeats 3000000
set_option maxRecDepth 2000
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39RLoop
noncomputable section
open Paper2
open EthInapproximability.CurrentPaper
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveLabelCodecScratch RecursiveEntries

/-- A closed arithmetic constant with its defining equality; it contains no
execution or correctness proposition. -/
private noncomputable opaque coefficientDatum :
    {C : ℕ // C = 200 * (NX + N1 + V39RLoopGrowth.pushBound + 1)^2} :=
  ⟨200 * (NX + N1 + V39RLoopGrowth.pushBound + 1)^2,rfl⟩

def bodyCoefficient : ℕ := coefficientDatum.val
attribute [local irreducible] V39RLoopGrowth.pushBound bodyCoefficient

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- Every current input pair has the same explicit public per-level majorant. -/
theorem bodyClock_public (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 4 ≤ s) (r : ℕ) (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K k : ℕ) (hk : k ≤ K)
    (x0 : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q (k + 1))
    (y0 : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q (k + 1)) :
    bodyClock g hg hs r hq ξ k x0 y0 ≤
      bodyCoefficient * (publicScale g p s q₁ q₂ w Q r K)^10 := by
  let X := publicScale g p s q₁ q₂ w Q r K
  obtain ⟨hX,hS,hc,hl,hG,hmn⟩ := publicScale_caps g p s q₁ q₂ w Q r K k hk
  have hstep := V39StepClock.stepClock_X g hg hs r hq ξ k x0 y0 hX hS hc hl hG hmn
  have hX1 : 1 ≤ X := by omega
  have hXB : X ≤ X^10 := by simpa using (Nat.pow_le_pow_right hX1 (show 1 ≤ 10 by omega))
  have h9B : X^9 ≤ X^10 := Nat.pow_le_pow_right hX1 (by omega)
  have hB1 : 1 ≤ X^10 := Nat.one_le_pow 10 X hX1
  have hJ := SuccessClock2.joinBound_le g.vertices p s q₁ q₂ w Q k
    (NeZero.one_le : 1 ≤ Q) (NeZero.one_le : 1 ≤ w) (NeZero.one_le : 1 ≤ s) (NeZero.one_le : 1 ≤ q₂)
  have hJX : NavJoin.joinBound g.vertices p s q₁ q₂ w Q k ≤ X^10 := by
    have hm : 11000 * X ≤ X^2 := by rw [pow_two]; exact Nat.mul_le_mul_right X (by omega)
    have hp : X^2 ≤ X^10 := Nat.pow_le_pow_right hX1 (by omega)
    exact hJ.trans ((show 1000 * (_ + _ + 10) ≤ 11000*X by omega).trans (hm.trans hp))
  have hm := master_public_bound (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r K
  have hmk : (∑ z : SrcX.JX, (master (p:=p) (s:=s) (q₁:=q₁) (q₂:=q₂) (w:=w) (Q:=Q) g r z).length)+k ≤ X := by
    dsimp [X,publicScale,scalarSum] at *; omega
  have hb := entryBank_public_bound g r K k hk x0 y0
  have hc0 := syntaxCap_le g.vertices p s q₁ q₂ w Q K k (by omega)
  obtain ⟨hlr,hlc⟩ := labelCap_le g.vertices p s q₁ q₂ w Q K k (by omega)
  have hc0X : codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).1 +
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2 ≤ X := by
    dsimp [X,publicScale]; omega
  have hlrX : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).1.maxLen ≤ X := by
    dsimp [X,publicScale]; omega
  have hlcX : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.maxLen ≤ X := by
    dsimp [X,publicScale]; omega
  obtain ⟨e1,-,e3,e4,e5,e6,e7⟩ := SuccessClock.derived_le (n:=g.vertices) (s:=s)
    (q₁:=q₁) (q₂:=q₂) (NeZero.one_le : 1 ≤ w) (NeZero.one_le : 1 ≤ Q) (copies p .bit) (.ticket p) k
  change codeSize (Code.append (.ticket w) (taggedCode q₁ q₂ s (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2)) ≤
    codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 at e1
  change codeSize (outerCode q₁ q₂ s (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2) ≤
    codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 at e3
  change codeSize (copies (s + 1) (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2) ≤
    codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 at e4
  change codeSize (graphRowsCode (V:=Fin g.vertices) q₁ q₂ s (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).1) ≤
    codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).2 at e6
  have hap : codeSize (Code.append (.ticket q₁) (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).1) =
    3+(3+(q₁+1))+codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).1 := rfl
  have hnav : (∑ i : Fin 9, (NavJoin.outVec g.vertices p s q₁ q₂ w Q k i).length) ≤ 12*X := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, NavJoin.outVec, Matrix.cons_val_zero,
      Matrix.cons_val_succ, encodeCode_length]
    omega
  unfold bodyClock
  extract_lets x y C c c' activity req Tst Lp Lc L2 L6 L7
  have hTst : Tst ≤ X^10 := hstep.trans h9B
  have hLp : Lp ≤ 2*(X^10) := by change _+k ≤ _; omega
  have hLc : Lc ≤ X^10 + V39RLoopGrowth.pushBound*Tst :=
    Nat.add_le_add_right (hb.trans hXB) _
  have hr := C.1.length_le req.1
  have hy := C.2.length_le req.2
  have hL2 : L2 ≤ X^10 := by dsimp [L2,c']; simp only [encodeCode_length]; omega
  have hcr : C.1.maxLen ≤ X := hlrX
  have hcc : C.2.maxLen ≤ X := hlcX
  have hL6 : L6 ≤ 3*(X^10) := by dsimp only [L6,c]; simp only [encodeCode_length]; omega
  have hL7 : L7 ≤ 14*(X^10) := by dsimp only [L7]; omega
  clear_value C c c' activity req Tst Lp Lc L2 L6 L7
  have h := SuccessClock.body_arith NX N1 V39RLoopGrowth.pushBound Tst Lp Lc
    (NavJoin.joinBound g.vertices p s q₁ q₂ w Q k) L2 L6 L7 (X^10)
    hB1 hTst hLp hLc hJX hL2 hL6 hL7
  calc
    _ ≤ 200*((NX+N1+V39RLoopGrowth.pushBound+1)*((NX+N1+V39RLoopGrowth.pushBound+1)*X^10)) := h
    _ = bodyCoefficient*X^10 := by
      rw [bodyCoefficient,coefficientDatum.property]
      simp only [pow_two,Nat.mul_assoc]

/-- The visited-chain supremum is bounded without enumerating input pairs. -/
theorem loopBd_public (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hs : 4 ≤ s) (r : ℕ) (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K : ℕ) (x : V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (y : V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    loopBd g hg hs r hq ξ K x y ≤ bodyCoefficient*(publicScale g p s q₁ q₂ w Q r K)^10 := by
  unfold loopBd
  apply Finset.sup_le
  intro i _
  have hlev := iter_level (V39EdgeSourceFront.edgeActivity g hg (by omega) r hq) ξ ⟨K,(x,y)⟩ i
  generalize (lstep (V39EdgeSourceFront.edgeActivity g hg (by omega) r hq) ξ)^[i] ⟨K,(x,y)⟩ = lv at hlev ⊢
  rcases lv with ⟨_ | k,xy⟩
  · exact Nat.zero_le _
  · exact bodyClock_public g hg hs r hq ξ K k (by simp only at hlev; omega) xy.1 xy.2

end
#print axioms bodyClock_public
#print axioms loopBd_public
end CurrentAdditive.V39RLoop
