import Paper2.RLoopStep
import Paper2.SC2Arith
import Paper2.SC2Codec

/-! Lane a-success-clock-owner-2, segment (1b): the request-selection clock
`RequestSelect.clock`, the locate clock `LocateUniform.locBound` and the prefix
selection clock `TemplateStepX.selClock`, each at most `X^5` when every
scalar, code size and label length of the level is at most `X`. Pure
arithmetic over the literal production clock expressions. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.SuccessClock2

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries

theorem xchain {X : ℕ} (hX : 1048576 ≤ X) :
    1048576 * X ≤ X ^ 2 ∧ 1048576 * X ^ 2 ≤ X ^ 3 ∧ 1048576 * X ^ 3 ≤ X ^ 4 ∧
      1048576 * X ^ 4 ≤ X ^ 5 ∧ 1048576 * X ^ 5 ≤ X ^ 6 ∧ 1048576 * X ^ 6 ≤ X ^ 7 ∧
      1048576 * X ^ 7 ≤ X ^ 8 := by
  refine ⟨x1 hX, xstep hX 2, xstep hX 3, xstep hX 4, xstep hX 5, xstep hX 6, xstep hX 7⟩

theorem reqClock_X (Y : List Bool) (j i : ℕ) (E G : Code) (cs rs : List (List Bool)) {X : ℕ}
    (hX : 1048576 ≤ X) (hY : Y.length ≤ X) (hj : j ≤ X) (hi : i ≤ X)
    (hE : codeSize E ≤ X) (hG : codeSize G ≤ X)
    (hcs : cs.flatten.length ≤ X ^ 2) (hcl : cs.length ≤ X)
    (hrs : rs.flatten.length ≤ X ^ 2) (hrl : rs.length ≤ X) :
    RequestSelect.clock Y j i E G cs rs ≤ X ^ 5 := by
  have c1 := colBound_X E cs j [] hX hE hcs hcl hj (by simp)
  have c2 := colBound_X G rs i [] hX hG hrs hrl hi (by simp)
  obtain ⟨h2, h3, h4, h5, -⟩ := xchain hX
  unfold RequestSelect.clock
  omega

theorem locBound_X {Y : Type} (q₁ q₂ s : ℕ) (cy : PrefixCodec Y) (col : Code) (pp : ℕ)
    (z : SourceMatrix.TaggedColumn q₁ q₂ s Y) {X : ℕ} (hX : 1048576 ≤ X)
    (hs : s + 1 ≤ X) (hpp : pp ≤ X)
    (hO : codeSize (outerCode q₁ q₂ s col) ≤ X) (hC : codeSize (copies (s + 1) col) ≤ X)
    (hoc : (outerColumnCodec q₁ q₂ s cy).maxLen ≤ X) (hpc : (piCodec cy (s + 1)).maxLen ≤ X) :
    LocateUniform.locBound q₁ q₂ s cy col pp z ≤ X ^ 5 := by
  obtain ⟨h2, h3, h4, h5, -⟩ := xchain hX
  cases z with
  | fixedTail js =>
      obtain ⟨f1, f2⟩ := ofFn_X (outerColumnCodec q₁ q₂ s cy) s js (by omega) hoc
      have c := colBound_X _ _ pp [] hX hO f1 f2 hpp (by simp)
      simp only [LocateUniform.locBound]
      omega
  | diagonal j =>
      have e := (outerColumnCodec q₁ q₂ s cy).length_le j
      have c := colBound_X (outerCode q₁ q₂ s col) [(outerColumnCodec q₁ q₂ s cy).encode j] 0 []
        hX hO (by simp; omega) (by simp; omega) (by omega) (by simp)
      simp only [LocateUniform.locBound]
      omega
  | unrestricted Z =>
      have e := (piCodec cy (s + 1)).length_le Z.1
      obtain ⟨f1, f2⟩ := ofFn_X (outerColumnCodec q₁ q₂ s cy) s Z.2 (by omega) hoc
      have c := rowBound_X (copies (s + 1) col) (outerCode q₁ q₂ s col)
        [(piCodec cy (s + 1)).encode Z.1] _ pp [] hX hC hO (by simp; omega) f1
        (by simp; omega) f2 hpp (by simp)
      simp only [LocateUniform.locBound]
      omega

end Paper2.SuccessClock2

#print axioms Paper2.SuccessClock2.reqClock_X
#print axioms Paper2.SuccessClock2.locBound_X
