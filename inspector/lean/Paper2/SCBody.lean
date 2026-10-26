import Paper2.SCEntry

/-! Unit 3, clock bounds, segment (2), third part: owner-7's per-level body clock
`RLoop.bodyClock` (seven checked clocks and six handoffs) from four NAMED component
bounds (the level step clock `RLoop.stepClock`, the admitted `NavJoin.joinBound`, the
master-region length and the step-entry bank length), with every other summand
discharged here: the level-`k+1` and level-`k` codes (`L2`, `L6`), the nine
`NavJoin.outVec` codes (`L7`, via `derived_le`), the request labels, and the absolute
constants `RLoop.NX`, `RLoop.N1`, `StepXGrowth.pushBound` (absorbed into the exponent). -/

set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

namespace Paper2.SuccessClock

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The arithmetic shape of `RLoop.bodyClock` (seven clocks, six handoffs), with every
summand a variable: no definition is unfolded here. -/
theorem body_arith (NX N1 pB Tst Lp Lc J L2 L6 L7 B0 : ℕ) (hB1 : 1 ≤ B0)
    (hTst : Tst ≤ B0) (hLp : Lp ≤ 2 * B0) (hLc : Lc ≤ B0 + pB * Tst) (hJ : J ≤ B0)
    (hL2 : L2 ≤ B0) (hL6 : L6 ≤ 3 * B0) (hL7 : L7 ≤ 14 * B0) :
    (((((NX * (2 * Lp + 3) + 1 + Tst + 1) + (N1 * (Lc + 1) + 1) + 1) + J + 1) +
      (2 * (L2 + 1) + 1) + 1) + (4 * (2 * L6 + 3) + 1) + 1) + (9 * (L7 + 1) + 1) + 1 ≤
      200 * ((NX + N1 + pB + 1) * ((NX + N1 + pB + 1) * B0)) := by
  set E := NX + N1 + pB + 1 with hE
  have hEB : B0 ≤ E * B0 := Nat.le_mul_of_pos_left B0 (by omega)
  have hEEB : E * B0 ≤ E * (E * B0) := Nat.le_mul_of_pos_left _ (by omega)
  have hpT : pB * Tst ≤ E * B0 := Nat.mul_le_mul (by omega) hTst
  have hPre : NX * (2 * Lp + 3) ≤ 7 * (E * B0) := by
    calc _ ≤ E * (7 * B0) := Nat.mul_le_mul (by omega) (by omega)
      _ = 7 * (E * B0) := by ring
  have hClr : N1 * (Lc + 1) ≤ 3 * (E * (E * B0)) := by
    calc _ ≤ E * (3 * (E * B0)) := Nat.mul_le_mul (by omega) (by omega)
      _ = 3 * (E * (E * B0)) := by ring
  omega

theorem bodyClock_le (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s)
    (r : ℕ) (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q (k + 1))
    (T a : ℕ) (hT : 1 ≤ T) (hkT : k ≤ T) (hq₁ : q₁ ≤ 2 ^ (7 * T))
    (hc1 : codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 +
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).2 + 1 ≤ 2 ^ (288 * T))
    (hc0 : codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).1 +
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2 + 1 ≤ 2 ^ (288 * T))
    (hl : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).1.maxLen ≤ 2 ^ (26 * T) ∧
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.maxLen ≤ 2 ^ (26 * T))
    (hstep : RLoop.stepClock g hg hs r hq ξ k x y ≤ 2 ^ (a * T))
    (hjoin : NavJoin.joinBound g.vertices p s q₁ q₂ w Q k ≤ 2 ^ (a * T))
    (hmaster : (∑ z : SrcX.JX, (RLoop.master (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w)
      (Q := Q) g r z).length) ≤ 2 ^ (a * T))
    (hbank : (∑ b : TemplateStepX.JT, ((Sum.elim (TemplateStepX.W0f k x y)
      (RLoop.E0k (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k)) b).length) ≤
        2 ^ (a * T)) :
    RLoop.bodyClock g hg hs r hq ξ k x y ≤
      2 ^ ((a + 2 * (RLoop.NX + RLoop.N1 + StepXGrowth.pushBound) + 316) * T) := by
  have hw : 1 ≤ w := NeZero.one_le
  have hQ : 1 ≤ Q := NeZero.one_le
  obtain ⟨e1, -, e3, e4, e5, e6, e7⟩ := derived_le (n := g.vertices) (s := s) (q₁ := q₁)
    (q₂ := q₂) hw hQ (copies p .bit) (.ticket p) k
  change codeSize (Code.append (.ticket w) (taggedCode q₁ q₂ s
      (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2)) ≤
    codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 at e1
  change codeSize (outerCode q₁ q₂ s (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2) ≤
    codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 at e3
  change codeSize (copies (s + 1) (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2) ≤
    codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1 at e4
  change codeSize (graphRowsCode (V := Fin g.vertices) q₁ q₂ s
      (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).1) ≤
    codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).2 at e6
  have hap : codeSize (Code.append (.ticket q₁) (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).1) =
      3 + (3 + (q₁ + 1)) + codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).1 := rfl
  -- the common majorant `B0` of every linear summand
  let B0 := 2 ^ ((a + 298) * T)
  have hTle : T ≤ 2 ^ T := Nat.lt_two_pow_self.le
  have hA : 2 ^ (a * T) ≤ B0 := pw_mono (by omega)
  have h288 : 2 ^ (288 * T) ≤ B0 := pw_mono (by omega)
  have h7 : 2 ^ (7 * T) ≤ B0 := pw_mono (by omega)
  have h26 : 2 ^ (26 * T) ≤ B0 := pw_mono (by omega)
  have hT1 : 2 ^ T ≤ B0 := by
    have := pw_mono (a := 1) (b := a + 298) (T := T) (by omega); simpa using this
  have hB1 : 1 ≤ B0 := Nat.one_le_two_pow
  have h7' : 7 ≤ 2 ^ (288 * T) := (small_le (e := 3) hT (by norm_num)).trans (pw_mono (by norm_num))
  -- the nine `outVec` codes and the request labels
  have hL7 : (∑ i : Fin 9, (NavJoin.outVec g.vertices p s q₁ q₂ w Q k i).length) ≤ 12 * B0 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, NavJoin.outVec, Matrix.cons_val_zero,
      Matrix.cons_val_succ, encodeCode_length]
    omega
  have hr1 := (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).1.length_le
    (RecursiveEntries.request (SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by omega) hq) ξ k x y).1
  have hr2 := (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.length_le
    (RecursiveEntries.request (SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
      (by omega) hq) ξ k x y).2
  have hl1 := hl.1
  have hl2 := hl.2
  have ec1 := encodeCode_length (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1
  have ec2 := encodeCode_length (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).2
  have ec3 := encodeCode_length (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).1
  have ec4 := encodeCode_length (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2
  have hfin : ∀ D : ℕ, 200 * ((D + 1) * ((D + 1) * B0)) ≤ 2 ^ ((a + 2 * D + 316) * T) := by
    intro D
    have h200 : 200 ≤ 2 ^ (8 * T) := small_le hT (by norm_num)
    have hE : D + 1 ≤ 2 ^ ((D + 1) * T) := pw_const hT
    have := pw_mul h200 (pw_mul hE (pw_mul hE (le_refl B0)))
    refine this.trans (pw_mono ?_)
    show 8 + ((D + 1) + ((D + 1) + (a + 298))) ≤ a + 2 * D + 316
    omega
  unfold RLoop.bodyClock
  extract_lets C c c' activity req Tst Lp Lc L2 L6 L7
  have hTst : Tst ≤ B0 := hstep.trans hA
  have hLp : Lp ≤ 2 * B0 := by
    change (∑ z : SrcX.JX, (RLoop.master (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w)
      (Q := Q) g r z).length) + k ≤ 2 * B0
    omega
  have hLc : Lc ≤ B0 + StepXGrowth.pushBound * Tst := by
    change (∑ b : TemplateStepX.JT, ((Sum.elim (TemplateStepX.W0f k x y)
      (RLoop.E0k (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) g r k)) b).length) +
      StepXGrowth.pushBound * Tst ≤ B0 + StepXGrowth.pushBound * Tst
    exact Nat.add_le_add_right (hbank.trans hA) _
  have hL2 : L2 ≤ B0 := by
    change (encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).1).length +
      (encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q (k + 1)).2).length ≤ B0
    omega
  have hL6 : L6 ≤ 3 * B0 := by
    change (encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).1).length +
      (encodeCode (seedRecursiveCodes g.vertices p s q₁ q₂ w Q k).2).length +
      ((defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).1.encode
        (RecursiveEntries.request (SourceActiveRank.scanAtCanonical
          (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) ξ k x y).1).length +
      ((defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode
        (RecursiveEntries.request (SourceActiveRank.scanAtCanonical
          (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) ξ k x y).2).length ≤ 3 * B0
    omega
  have hL7' : L7 ≤ 14 * B0 := by
    change (∑ i : Fin 9, (NavJoin.outVec g.vertices p s q₁ q₂ w Q k i).length) +
      ((defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).1.encode
        (RecursiveEntries.request (SourceActiveRank.scanAtCanonical
          (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) ξ k x y).1).length +
      ((defaultCarrierCodecs g.vertices p s q₁ q₂ w Q k).2.encode
        (RecursiveEntries.request (SourceActiveRank.scanAtCanonical
          (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) ξ k x y).2).length ≤ 14 * B0
    omega
  have hJ : NavJoin.joinBound g.vertices p s q₁ q₂ w Q k ≤ B0 := hjoin.trans hA
  clear_value C c c' activity req Tst Lp Lc L2 L6 L7
  generalize RLoop.NX = nx at *
  generalize RLoop.N1 = n1 at *
  generalize StepXGrowth.pushBound = pb at *
  exact (body_arith nx n1 pb Tst Lp Lc (NavJoin.joinBound g.vertices p s q₁ q₂ w Q k) L2 L6 L7 B0
    hB1 hTst hLp hLc hJ hL2 hL6 hL7').trans (hfin (nx + n1 + pb))

end Paper2.SuccessClock

#print axioms Paper2.SuccessClock.bodyClock_le
