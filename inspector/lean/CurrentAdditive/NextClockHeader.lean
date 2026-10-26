import CurrentAdditive.NextClockWriter

/-! Exact physical header-copy charge and the source-length polynomial
envelope for the final framing pass. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoSourceCodec Paper2.YaoLookup Paper2.YaoClockPoly
open Paper2.HeaderA

set_option maxHeartbeats 2000000

def headerCopyBudget {t : ℕ} (x : YaoSource t) : ℕ :=
  let b := paddedEdgeBits x.2.1
  let d := publicFieldDegree b t
  let rows := rowCount x.1 b t
  let cols := columnCount b t d
  (2*rows+2)+(2*cols+2)+(2*(2*b+4*t+2)+2)+
    (2*(rows*cols)+2)

theorem headerCopyCost_eq {t : ℕ} (x : YaoSource t)
    (u c : ℕ) :
    let d := publicFieldDegree (paddedEdgeBits x.2.1) t
    let W := writerOutputBank t 16 d
      (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c)
      x.2.2 (sourceThresholdOutput x u)
    CopyFill.fillCost (headerJobs t 16) W = headerCopyBudget x := by
  dsimp only
  let d := publicFieldDegree (paddedEdgeBits x.2.1) t
  let W := writerOutputBank t 16 d
    (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c)
    x.2.2 (sourceThresholdOutput x u)
  have hW := writerOutputBank_header_inputs t 16 d
    (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c)
    x.2.2 (sourceThresholdOutput x u)
  obtain ⟨_, _, hrowsW, hcolsW, hthrW⟩ := hW
  have hrows := (sourceThresholdOutput_writer_inputs x u).2.2.2.2.2.2.1
  have hcols := (sourceThresholdOutput_writer_inputs x u).2.2.2.2.2.2.2
  have hthr := sourceThresholdOutput_thr x u
  have hbits := writerOutputBank_bits t 16 d
    (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c)
    x.2.2 (sourceThresholdOutput x u)
  have hbitslen : (W (.writer (.inr .output))).length =
      rowCount x.1 (paddedEdgeBits x.2.1) t *
        columnCount (paddedEdgeBits x.2.1) t d := by
    dsimp only [W]
    rw [hbits]
    simp only [table, Paper2.YaoMaterialization.tabulate_length]
  change W (.dimensions 5) = _ at hrowsW
  change W (.dimensions 7) = _ at hcolsW
  change W (.threshold 1) = _ at hthrW
  change CopyFill.fillCost (headerJobs t 16) W = headerCopyBudget x
  simp only [CopyFill.fillCost, headerJobs, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  rw [hrowsW, hcolsW, hthrW]
  simp [hrows, hcols, hthr, hbitslen, headerCopyBudget, Nat.add_assoc]
  exact Or.inl rfl

theorem poly_headerCopyBudget (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (headerCopyBudget (t := t)) := by
  have hr := poly_public_rows t
  have hc := poly_public_columns t ht
  have hb := poly_b (t := t)
  unfold headerCopyBudget
  repeat' poly_step

def headerPrintBudget {t : ℕ} (x : YaoSource t) : ℕ :=
  let b := paddedEdgeBits x.2.1
  let d := publicFieldDegree b t
  let rows := rowCount x.1 b t
  let cols := columnCount b t d
  UnaryBinaryEncoding.coefficient*(rows+1)^2 +
    UnaryBinaryEncoding.coefficient*(cols+1)^2 +
    UnaryBinaryEncoding.coefficient*(2*b+4*t+2+1)^2 +
    (2*(natField rows ++ natField cols ++
      natField (2*b+4*t+2)).length+2)+3

theorem poly_headerPrintBudget (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (headerPrintBudget (t := t)) := by
  have hr := poly_public_rows t
  have hc := poly_public_columns t ht
  have hb := poly_b (t := t)
  unfold headerPrintBudget
  simp only [List.length_append]
  repeat' poly_step

def thresholdWriterBudget {t : ℕ} (x : YaoSource t) : ℕ :=
  let b := paddedEdgeBits x.2.1
  ((2*b+2)+(2*(2*b+2)+(4*t+3)+2)+1) +
    ((writerCopyBudget x+1+
      canonicalTableClockCoefficient *
        (canonicalCellSize t
          (publicFieldDegree b t) x.2.2+1)^12+1) +
     (headerCopyBudget x+1+headerPrintBudget x+1)+1)+1

theorem poly_thresholdWriterBudget (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (thresholdWriterBudget (t := t)) := by
  have hb := poly_b (t := t)
  have hw := poly_writerCopyBudget t ht
  have hc := poly_tableClock t ht
  have hh := poly_headerCopyBudget t ht
  have hp := poly_headerPrintBudget t ht
  unfold thresholdWriterBudget
  repeat' poly_step

#print axioms headerCopyCost_eq
#print axioms poly_headerCopyBudget
#print axioms poly_headerPrintBudget
#print axioms poly_thresholdWriterBudget

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
