import Paper2.SC2Sched

/-! Lane a-success-clock-owner-2, segments (2) and (3): the master-region
length `∑ z : SrcX.JX, (RLoop.master g r z).length` and the step-entry bank
length `∑ b : TemplateStepX.JT, (Sum.elim (TemplateStepX.W0f k x y) (RLoop.E0k g r k) b).length`,
computed cell by cell from the literal production bank definitions, then the
premises `Hmaster` and `Hbank` of the admitted `SuccessClock.Tent_sched` at the
public schedule with the same exponent `2601` as `Hstep`, `Hjoin`. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.SuccessClock2

open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries Paper2.ParameterizedCanonicalSource
  Paper2.SourceProfileParameters

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The source-arm entry bank at level `0` (no row word, no column word), cell by cell. -/
theorem WXb_sum_le (g : EncodedGraph.Graph) (r : ℕ) :
    (∑ z : SrcX.JX, (SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      g r 0 [] [] z).length) ≤
      codeSize (seedRecursiveCodes g.vertices p s q₁ q₂ w Q 0).2 +
        codeSize (outerCode q₁ q₂ s (seedRecursiveCodes g.vertices p s q₁ q₂ w Q 0).2) +
        (EncodedGraph.encode g).length + 3 * s + r + g.edges.length + q₁ + Q + p + w + 1 := by
  simp (config := {decide := true}) [SrcX.WXb, Fintype.sum_sum_type, Fin.sum_univ_succ,
    OTBody.BB, FetchIndexed.FB, FetchIndexed.ext5, FetchLabel.fb, FetchLabel.ext4,
    FetchLabel.eb, OutputSkipper.bk, OutputSkipper.ext, CodeHeaderMachine.contents,
    SrcU.JJ0, ScanDecodeMachine.D0, EndpointOperands.entry, GraphPrefixBind.initBank,
    PublicGraphEndpointMachine.initialBank, RankRun.RB, DefaultWordLoop.entry, DefaultWordLoop.bk,
    CanonicalDefaultWordScratch.RowMachine.B, DefaultColumnRound.B,
    SourceNormalizationMachineDecode.start, OTOps.u, ScanDecodeMachine.u, encodeCode_length]
  omega

/-- The master region is the level-`0` source-arm bank with five cells blanked. -/
theorem master_sum_le (g : EncodedGraph.Graph) (r : ℕ) :
    (∑ z : SrcX.JX, (RLoop.master (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      g r z).length) ≤
    (∑ z : SrcX.JX, (SrcX.WXb (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      g r 0 [] [] z).length) := by
  apply Finset.sum_le_sum
  intro z _
  unfold RLoop.master
  split_ifs <;> simp

/-- The step-entry master part: the master region plus the `k` counter marks. -/
theorem E0k_sum_le (g : EncodedGraph.Graph) (r k : ℕ) :
    (∑ z : SrcX.JX, (RLoop.E0k (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      g r k z).length) ≤
    (∑ z : SrcX.JX, (RLoop.master (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      g r z).length) + k := by
  have h : ∀ z : SrcX.JX, (RLoop.E0k (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      g r k z).length ≤ (RLoop.master (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      g r z).length + (if z = RLoop.marksX then k else 0) := by
    intro z
    unfold RLoop.E0k
    split_ifs <;> simp
  calc _ ≤ ∑ z : SrcX.JX, ((RLoop.master (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w)
        (Q := Q) g r z).length + (if z = RLoop.marksX then k else 0)) :=
          Finset.sum_le_sum (fun z _ => h z)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp

/-- The level entry bank on `J`: the two serialized level-`k+1` codes and the two encoded labels. -/
theorem W0f_sum_le {n : ℕ} [NeZero n] (k : ℕ)
    (x : Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1))
    (y : Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q (k + 1)) :
    (∑ b : TemplateStep.J, (TemplateStepX.W0f k x y b).length) ≤
      codeSize (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).1 +
        codeSize (seedRecursiveCodes n p s q₁ q₂ w Q (k + 1)).2 +
        (defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).1.maxLen +
        (defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).2.maxLen := by
  have h1 := (defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).1.length_le x
  have h2 := (defaultCarrierCodecs n p s q₁ q₂ w Q (k + 1)).2.length_le y
  simp (config := {decide := true}) [TemplateStepX.W0f, Fintype.sum_sum_type, Fin.sum_univ_succ,
    NavJoin.jb, NavJoin.inVec, RequestSelect.mk, RequestSelect.inner, RequestSelect.vec,
    FetchLabel.fb, FetchLabel.ext4, FetchLabel.eb, OutputSkipper.bk, OutputSkipper.ext,
    CodeHeaderMachine.contents, encodeCode_length]
  omega

end Paper2.SuccessClock2

#print axioms Paper2.SuccessClock2.WXb_sum_le
#print axioms Paper2.SuccessClock2.master_sum_le
#print axioms Paper2.SuccessClock2.E0k_sum_le
#print axioms Paper2.SuccessClock2.W0f_sum_le
