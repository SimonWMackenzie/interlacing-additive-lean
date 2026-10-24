import Paper2.SC2Req

/-! Lane a-success-clock-owner-2, segment (1c): the explicit clocks of the
source arms (`SrcU.scanPosBound`, `OTGen.fullGBound`, `DefaultWordLoop.bodyBound`
and `levelBound`) at most a fixed power of a scale `X` that dominates every
scalar, code size, label length, graph byte length and default word of the
level. Pure arithmetic over the literal production clock expressions. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.SuccessClock2

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries

theorem semanticRank_le (kind : CanonicalEndpointRankMachine.Kind)
    (item : CanonicalEndpointRankMachine.ItemKind) (u v x : ℕ) :
    CanonicalEndpointRankMachine.semanticRank kind item u v x ≤ x + 2 := by
  cases item <;> cases kind <;> simp only [CanonicalEndpointRankMachine.semanticRank] <;>
    (try split_ifs) <;> omega

/-- The scan-and-position clock of the source arms. -/
theorem scanPosBound_X (g : EncodedGraph.Graph) (hg : g.Valid) (a r ig xv : ℕ) (kb : Bool)
    {X : ℕ} (hX : 1048576 ≤ X) (ha : a ≤ X) (hr : r ≤ X) (hig : ig ≤ X) (hxv : xv ≤ X)
    (hn : g.vertices ≤ X) (hm : g.edges.length ≤ X)
    (hG : (EncodedGraph.encode g).length + 1 ≤ X) (hmn : 2 * g.edges.length * g.vertices ≤ X) :
    SrcU.scanPosBound g hg a r ig xv kb ≤ X ^ 4 := by
  obtain ⟨h2, h3, h4, h5, -⟩ := xchain hX
  have hd := ScanDecodeMachine.decodeBound_le a r g.edges.length
  have d1 : a / r ≤ a := Nat.div_le_self _ _
  have d2 : a / r / 3 ≤ a / r := Nat.div_le_self _ _
  have d3 : a / r / 3 / g.edges.length ≤ a / r / 3 := Nat.div_le_self _ _
  unfold SrcU.scanPosBound
  by_cases hsp : 0 < g.edges.length ∧ a / r / 3 / g.edges.length = ig
  · rw [dif_pos hsp]
    dsimp only
    generalize CanonicalEdgeTape.graphEdge g hg = edge
    have hmod := Nat.mod_lt (a / r / 3) hsp.1
    have hw := CanonicalEdgeTape.word_length_le edge
    have hu := (edge ⟨a / r / 3 % g.edges.length, hmod⟩ true).isLt
    have hv := (edge ⟨a / r / 3 % g.edges.length, hmod⟩ false).isLt
    have hsr := semanticRank_le (RankRun.kindOfNat (a / r % 3)) (RankRun.itemOfBool kb)
      (edge ⟨a / r / 3 % g.edges.length, hmod⟩ false).val
      (edge ⟨a / r / 3 % g.edges.length, hmod⟩ true).val xv
    have hc : ((EncodedGraph.encode g).length + 1) ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left hG 3
    have mx : max (edge ⟨a / r / 3 % g.edges.length, hmod⟩ false).val
        (max (edge ⟨a / r / 3 % g.edges.length, hmod⟩ true).val xv) ≤ X := by
      simp only [max_le_iff]; omega
    have hmod' : a / r / 3 % g.edges.length ≤ a / r / 3 := Nat.mod_le _ _
    simp only [UnaryFieldListParserScratch.fuel]
    omega
  · rw [dif_neg hsp]
    omega

theorem bodyGBound_le (Tf tok restLen a : ℕ) :
    OTGen.bodyGBound Tf tok restLen a ≤ Tf + 2 * tok + restLen + 3 * a + 20 := by
  unfold OTGen.bodyGBound; omega

/-- The generic outer-token equality clock. -/
theorem fullGBound_X (s : ℕ) (Tf tok : ℕ → ℕ) (rest : ℕ → List Bool) {X : ℕ}
    (hX : 1048576 ≤ X) (hs0 : 0 < s) (hs : s ≤ X) (hTf : ∀ i < s, Tf i ≤ X ^ 4)
    (htok : ∀ i, tok i ≤ X) (hrest : ∀ i, (rest i).length ≤ X) :
    OTGen.fullGBound s Tf tok rest ≤ X ^ 7 := by
  obtain ⟨h2, h3, h4, h5, h6, h7, -⟩ := xchain hX
  have hl : OTGen.loopGBd s Tf tok rest (tok 0) ≤ 2 * X ^ 4 := by
    unfold OTGen.loopGBd
    apply Finset.sup_le
    intro i hi
    rw [Finset.mem_range] at hi
    have := bodyGBound_le (Tf i) (tok i) (rest i).length (tok 0)
    have := hTf i hi; have := htok i; have := htok 0; have := hrest i
    omega
  have hm : s * (OTGen.loopGBd s Tf tok rest (tok 0) + 2) ≤ X * (3 * X ^ 4) :=
    Nat.mul_le_mul hs (by omega)
  have he : X * (3 * X ^ 4) = 3 * X ^ 5 := by ring
  have := hTf 0 hs0; have := htok 0; have := hrest 0
  unfold OTGen.fullGBound
  omega

/-- The body clock of the default-word level loop. -/
theorem wordBody_X (q₁ s Q w : ℕ) (R C : List Bool) {X : ℕ} (hX : 1048576 ≤ X)
    (hq : q₁ + s + 1 ≤ X) (hQ : Q ≤ X) (hw : w ≤ X) (hR : R.length ≤ X) (hC : C.length ≤ X) :
    DefaultWordLoop.bodyBound q₁ s Q w R C ≤ X ^ 5 := by
  obtain ⟨h2, h3, h4, h5, -⟩ := xchain hX
  have m1 : (q₁ + s + 1) * C.length ≤ X * X := Nat.mul_le_mul hq hC
  have m2 : Q * (4 + (q₁ + s + 1) * C.length) ≤ X * (4 + X * X) := Nat.mul_le_mul hQ (by omega)
  have m3 : Q * (2 * (4 + (q₁ + s + 1) * C.length) + 3) ≤ X * (2 * (4 + X * X) + 3) :=
    Nat.mul_le_mul hQ (by omega)
  have m4 : q₁ * (2 * C.length + 3) ≤ X * (2 * X + 3) := Nat.mul_le_mul (by omega) (by omega)
  have m5 : s * (2 * C.length + 3) ≤ X * (2 * X + 3) := Nat.mul_le_mul (by omega) (by omega)
  have m6 : w * (2 * ([true, false, false, false] ++ R).length + 3) ≤ X * (2 * (4 + X) + 3) :=
    Nat.mul_le_mul hw (by simp; omega)
  have m7 : w * ([true, false, false, false] ++ R).length ≤ X * (4 + X) :=
    Nat.mul_le_mul hw (by simp; omega)
  have e1 : X * (4 + X * X) = 4 * X + X ^ 3 := by ring
  have e2 : X * (2 * (4 + X * X) + 3) = 11 * X + 2 * X ^ 3 := by ring
  have e3 : X * (2 * X + 3) = 2 * X ^ 2 + 3 * X := by ring
  have e4 : X * (2 * (4 + X) + 3) = 2 * X ^ 2 + 11 * X := by ring
  have e5 : X * (4 + X) = X ^ 2 + 4 * X := by ring
  have e6 : X * X = X ^ 2 := by ring
  unfold DefaultWordLoop.bodyBound CanonicalDefaultWordScratch.RowMachine.rowBound
  simp only [DefaultWordLoop.innerW, CanonicalDefaultWordScratch.RowMachine.innerWord_length,
    CanonicalDefaultWordScratch.repeatWord_length, List.length_append, List.length_cons,
    List.length_nil] at m6 m7 ⊢
  omega

/-- The default-word level loop clock at level `j`, from the default words of the levels `< j`. -/
theorem levelBound_X (p s q₁ q₂ w Q j : ℕ) {X : ℕ} (hX : 1048576 ≤ X)
    (hq : q₁ + s + 1 ≤ X) (hQ : Q ≤ X) (hw : w ≤ X) (hj : j ≤ X)
    (hW : ∀ i < j, (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q i).1.length ≤ X ∧
      (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q i).2.length ≤ X) :
    DefaultWordLoop.levelBound p s q₁ q₂ w Q j ≤ X ^ 6 := by
  obtain ⟨h2, h3, h4, h5, h6, -⟩ := xchain hX
  have hs : DefaultWordLoop.levelBound p s q₁ q₂ w Q j ≤ j * X ^ 5 := by
    unfold DefaultWordLoop.levelBound
    calc (Finset.range j).sum (fun i => DefaultWordLoop.bodyBound q₁ s Q w
          (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q i).1
          (CanonicalDefaultWordScratch.words p s q₁ q₂ w Q i).2)
        ≤ (Finset.range j).sum (fun _ => X ^ 5) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_range] at hi
          exact wordBody_X q₁ s Q w _ _ hX hq hQ hw (hW i hi).1 (hW i hi).2
      _ = j * X ^ 5 := by simp
  have hm : j * X ^ 5 ≤ X * X ^ 5 := Nat.mul_le_mul_right _ hj
  have he : X * X ^ 5 = X ^ 6 := by ring
  omega

end Paper2.SuccessClock2

#print axioms Paper2.SuccessClock2.scanPosBound_X
#print axioms Paper2.SuccessClock2.fullGBound_X
#print axioms Paper2.SuccessClock2.levelBound_X
