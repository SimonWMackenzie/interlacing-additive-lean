import Paper2.WTable
import Paper2.SCFetch

/-! Unit 3, clock bounds, segment (2), second part: owner-7's `loopBd` from a bound on the
per-level body clock of every visited level, and owner-8's `Tent` (the sup of `entryBd`)
from `loopBd`, the level-`K` / level-`0` code and label caps and the sample dimensions,
in the exponent form `2^(e*T)`. Pure arithmetic about the private owner-7/owner-8 clock
expressions (`RLoop.loopBd`, `RLoop.clockLv`, `WEntry.coreBd`, `WEntry.entryBd`,
`WEntry.Tent`) and the admitted fetch clocks (via `SCFetch`). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.SuccessClock

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries

theorem small_le {c e T : ℕ} (hT : 1 ≤ T) (h : c ≤ 2 ^ e) : c ≤ 2 ^ (e * T) :=
  h.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_right e hT))

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- `loopBd` (a `Finset.sup` over the visited levels) is bounded by any uniform bound on the
body clock of every level `k + 1 ≤ K` and every pair of that level. -/
theorem loopBd_le (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s)
    (r : ℕ) (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q K)
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K) (X : ℕ)
    (hbody : ∀ k, k + 1 ≤ K →
      ∀ (x' : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
          s q₁ q₂ w Q (k + 1))
        (y' : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
          s q₁ q₂ w Q (k + 1)),
        RLoop.bodyClock g hg hs r hq ξ k x' y' ≤ X) :
    RLoop.loopBd g hg hs r hq ξ K x y ≤ X := by
  unfold RLoop.loopBd
  apply Finset.sup_le
  intro i _
  have hlev := RLoop.iter_level
    (SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) ξ
    ⟨K, (x, y)⟩ i
  generalize (RLoop.lstep (SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg)
    (by omega) hq) ξ)^[i] ⟨K, (x, y)⟩ = lv at hlev ⊢
  rcases lv with ⟨_ | k, xy⟩
  · exact Nat.zero_le _
  · have hk : k + 1 ≤ K := by
      simp only at hlev
      omega
    exact hbody k hk xy.1 xy.2

/-- `Tent` from the code, label and dimension caps and a bound on `loopBd` for every entry. -/
theorem Tent_le (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices] (hs : 4 ≤ s)
    (r : ℕ) (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin g.edges.length) * r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K mX mY : ℕ)
    (xs : Fin mX → Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (ys : Fin mY → Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices))
      s q₁ q₂ w Q K)
    (T a : ℕ) (hT : 1 ≤ T) (hKT : K ≤ T) (hp : p ≤ 2 ^ (7 * T))
    (hcK : codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).1 +
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q K).2 + 1 ≤ 2 ^ (288 * T))
    (hc0 : codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q 0).1 +
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q 0).2 + 1 ≤ 2 ^ (288 * T))
    (hlK : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q K).1.maxLen ≤ 2 ^ (26 * T) ∧
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q K).2.maxLen ≤ 2 ^ (26 * T))
    (hl0 : (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q 0).1.maxLen ≤ 2 ^ (26 * T) ∧
      (defaultCarrierCodecs g.vertices p s q₁ q₂ w Q 0).2.maxLen ≤ 2 ^ (26 * T))
    (hmX : mX ≤ 2 ^ (29 * T)) (hmY : mY ≤ 2 ^ (29 * T))
    (hloop : ∀ i j, RLoop.loopBd g hg hs r hq ξ K (xs i) (ys j) ≤ 2 ^ (a * T)) :
    WEntry.Tent g hg hs r hq ξ K mX mY xs ys ≤ 2 ^ ((a + 360) * T) := by
  unfold WEntry.Tent
  apply Finset.sup_le
  rintro ⟨i, j⟩ _
  let C := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q K
  let c := seedRecursiveCodes g.vertices p s q₁ q₂ w Q K
  let C0 := defaultCarrierCodecs g.vertices p s q₁ q₂ w Q 0
  let c0 := seedRecursiveCodes g.vertices p s q₁ q₂ w Q 0
  let V := 2 ^ ((a + 353) * T)
  have hV1 : 1 ≤ V := Nat.one_le_two_pow
  have mono : ∀ e, e ≤ a + 353 → 2 ^ (e * T) ≤ V := fun e he => pw_mono he
  -- sample lists
  have hFc : (WEntry.colWords g K mY ys).flatten.length ≤ 2 ^ (55 * T) := by
    have h := ofFn_flatten_le C.2 mY ys
    have h2 : mY * C.2.maxLen ≤ 2 ^ (55 * T) := by
      have := pw_mul hmY hlK.2
      simpa using this
    exact h.trans h2
  have hFr : (WEntry.rowWords g K mX xs).flatten.length ≤ 2 ^ (55 * T) := by
    have h := ofFn_flatten_le C.1 mX xs
    have h2 : mX * C.1.maxLen ≤ 2 ^ (55 * T) := by
      have := pw_mul hmX hlK.1
      simpa using this
    exact h.trans h2
  have hNc : (WEntry.colWords g K mY ys).length = mY := List.length_ofFn
  have hNr : (WEntry.rowWords g K mX xs).length = mX := List.length_ofFn
  have h29 : 2 ^ (29 * T) ≤ 2 ^ (55 * T) := pw_mono (by omega)
  have h8 : 8 ≤ 2 ^ (3 * T) := small_le hT (by norm_num)
  have hZ6 : 6 * 2 ^ (55 * T) ≤ 2 ^ (58 * T) := by
    have : 2 ^ (3 * T) * 2 ^ (55 * T) = 2 ^ (58 * T) := by rw [← pow_add]; ring_nf
    nlinarith [Nat.one_le_two_pow (n := 55 * T)]
  have h80 : 80 ≤ 2 ^ (7 * T) := small_le hT (by norm_num)
  have hrow := rowBound_le c.2 c.1 (WEntry.colWords g K mY ys) (WEntry.rowWords g K mX xs) i.val []
  have hcol := colBound_le c.2 (WEntry.colWords g K mY ys) j.val (WEntry.rowWords g K mX xs).flatten
  have hrowV : FetchIndexed.rowBound c.2 c.1 (WEntry.colWords g K mY ys)
      (WEntry.rowWords g K mX xs) i.val [] ≤ V := by
    have hZ : (WEntry.colWords g K mY ys).flatten.length + (WEntry.rowWords g K mX xs).flatten.length +
        (WEntry.colWords g K mY ys).length + (WEntry.rowWords g K mX xs).length + i.val +
        ([] : List Bool).length + 1 ≤ 2 ^ (58 * T) := by
      simp only [List.length_nil, hNc, hNr]
      have := i.isLt
      omega
    have hS : codeSize c.2 + codeSize c.1 + 1 ≤ 2 ^ (288 * T) := by
      change codeSize c.1 + codeSize c.2 + 1 ≤ _ at hcK; omega
    have hm := pw_mul h80 (pw_mul hS hZ)
    exact hrow.trans (by
      calc 80 * ((codeSize c.2 + codeSize c.1 + 1) * _) ≤ _ := hm
        _ ≤ V := mono _ (by omega))
  have hcolV : FetchIndexed.colBound c.2 (WEntry.colWords g K mY ys) j.val
      (WEntry.rowWords g K mX xs).flatten ≤ V := by
    have hZ : (WEntry.colWords g K mY ys).flatten.length + (WEntry.colWords g K mY ys).length +
        j.val + (WEntry.rowWords g K mX xs).flatten.length + 1 ≤ 2 ^ (58 * T) := by
      simp only [hNc]
      have := j.isLt
      omega
    have hS : codeSize c.2 + 1 ≤ 2 ^ (288 * T) := by
      change codeSize c.1 + codeSize c.2 + 1 ≤ _ at hcK; omega
    have h60 : 60 ≤ 2 ^ (7 * T) := by omega
    have hm := pw_mul h60 (pw_mul hS hZ)
    exact hcol.trans (by
      calc 60 * ((codeSize c.2 + 1) * _) ≤ _ := hm
        _ ≤ V := mono _ (by omega))
  -- evaluator
  have hTle : T ≤ 2 ^ T := Nat.lt_two_pow_self.le
  have h288 : 2 ^ (288 * T) ≤ 2 ^ (290 * T) := pw_mono (by omega)
  have h26 : 2 ^ (26 * T) ≤ 2 ^ (288 * T) := pw_mono (by omega)
  have hT288 : 2 ^ T ≤ 2 ^ (288 * T) := by
    have := pw_mono (a := 1) (b := 288) (T := T) (by omega); simpa using this
  have h4 : 4 * 2 ^ (288 * T) ≤ 2 ^ (290 * T) := by
    have e : 2 ^ (2 * T) * 2 ^ (288 * T) = 2 ^ (290 * T) := by rw [← pow_add]; ring_nf
    have : 4 ≤ 2 ^ (2 * T) := small_le hT (by norm_num)
    nlinarith [Nat.one_le_two_pow (n := 288 * T)]
  have hxi := C.1.length_le (xs i)
  have hyj := C.2.length_le (ys j)
  have hU : 2 ^ (290 * T) ≤ V := mono _ (by omega)
  have hloopV : K * (RLoop.loopBd g hg hs r hq ξ K (xs i) (ys j) + 2) ≤ V := by
    have h1 : RLoop.loopBd g hg hs r hq ξ K (xs i) (ys j) + 2 ≤ 2 ^ ((a + 2) * T) := by
      have := pw_add hT (hloop i j) (show 2 ≤ 2 ^ (1 * T) from small_le hT (by norm_num))
      simpa [Nat.add_assoc] using this
    have h2 : K ≤ 2 ^ (1 * T) := by simpa using hKT.trans hTle
    exact (pw_mul h2 h1).trans (mono _ (by omega))
  have hpV : p ≤ V := hp.trans (mono _ (by omega))
  have hsd1 := fun z => C0.1.length_le z
  have hsd2 := fun z => C0.2.length_le z
  unfold WEntry.entryBd WEntry.coreBd
  simp only [encodeCode_length]
  change FetchIndexed.rowBound c.2 c.1 _ _ i.val [] + FetchIndexed.colBound c.2 _ j.val _ + _ +
    (2 * ((C.1.encode (xs i)).length + (C.2.encode (ys j)).length + 1) + 1) + 3 ≤ _
  have hc0' : codeSize c0.1 + codeSize c0.2 + 1 ≤ 2 ^ (288 * T) := hc0
  have hcK' : codeSize c.1 + codeSize c.2 + 1 ≤ 2 ^ (288 * T) := hcK
  have hfin : 2 ^ 7 * V ≤ 2 ^ ((a + 360) * T) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by nlinarith)
  have hs1 := hsd1 (RecursiveEntries.seedRequest
    (SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) ξ K
      (xs i) (ys j)).1
  have hs2 := hsd2 (RecursiveEntries.seedRequest
    (SourceActiveRank.scanAtCanonical (CanonicalEdgeTape.graphEdge g hg) (by omega) hq) ξ K
      (xs i) (ys j)).2
  have hlK1 := hlK.1
  have hlK2 := hlK.2
  have hl01 := hl0.1
  have hl02 := hl0.2
  have hKV : K ≤ V := (hKT.trans hTle).trans (hT288.trans (h288.trans hU))
  simp only [C, c, C0, c0] at *
  omega

end Paper2.SuccessClock

#print axioms Paper2.SuccessClock.loopBd_le
#print axioms Paper2.SuccessClock.Tent_le
