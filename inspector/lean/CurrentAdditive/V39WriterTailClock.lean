import CurrentAdditive.V39ScalarClock
import Paper2.YaoClockPoly

noncomputable section
namespace CurrentAdditive.V39ScalarSetup

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.SmallBias CurrentAdditive.V38Source CurrentAdditive.V38Encoded
open CurrentAdditive.V39SourceRenderer CurrentAdditive.V39SourceOutputSize
open CurrentAdditive.V39SourceAddressResource CurrentAdditive.V39SourceFieldWidths
open Paper2.YaoSourceCodec Paper2.RecursiveLabelCodecScratch Paper2.YaoClockPoly
open Paper2.UnaryFieldListParserScratch

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def writerSize {t : ℕ} (src : YaoSource t) : ℕ :=
  let H := 2 ^ edgeBits src.2.1
  let nPad := H * (arity t + 1)
  let body := (tokens (List.ofFn (flatten src.2.2))).length
  (sourceInstance src).rows + (sourceInstance src).cols + body + nPad + arity t + H + 1

def writerCopyBudget {t : ℕ} (src : YaoSource t) : ℕ :=
  let H := 2 ^ edgeBits src.2.1
  let R2 := (2 ^ v38FieldDegree (edgeBits src.2.1) t) ^ 2
  let nPad := H * (arity t + 1)
  let body := (tokens (List.ofFn (flatten src.2.2))).length
  2 * (H ^ (2 ^ (t - 1)) + R2 + H + body + arity t + R2 * nPad + nPad +
    (sourceInstance src).rows + (sourceInstance src).cols) + 18

def headerCopyBudget {t : ℕ} (src : YaoSource t) : ℕ :=
  let R := (sourceInstance src).rows
  let C := (sourceInstance src).cols
  let B := (sourceInstance src).threshold
  2 * (R + C + B + R * C) + 8

def headerRunBudget {t : ℕ} (src : YaoSource t) : ℕ :=
  let R := (sourceInstance src).rows
  let C := (sourceInstance src).cols
  let B := (sourceInstance src).threshold
  UnaryBinaryEncoding.coefficient * ((R + 1) ^ 2 + (C + 1) ^ 2 + (B + 1) ^ 2) +
    2 * (natField R ++ natField C ++ natField B).length + 5

/-- Exact numeric tail supplied by the prepared writer/header construction.
The table coefficient is fixed independently of the source input. -/
def writerHeaderBudget {t : ℕ} (tableCoefficient : ℕ) (src : YaoSource t) : ℕ :=
  writerCopyBudget src + tableCoefficient * (writerSize src + 1) ^ 12 +
    headerCopyBudget src + headerRunBudget src + 5

theorem poly_writer_header_budget (t tableCoefficient : ℕ) :
    PolyIn (fun src : YaoSource t => writerHeaderBudget tableCoefficient src) := by
  have hH : PolyIn (fun src : YaoSource t => 2 ^ edgeBits src.2.1) := by
    simpa only [edgeBits_eq_paddedEdgeBits, Paper2.YaoLookup.paddedEdgeCount] using
      (poly_H (t := t))
  have hR : PolyIn (fun src : YaoSource t => (sourceInstance src).rows) :=
    ⟨rowCoefficient t, 2 ^ (t - 1) + 1, instance_rows_bound⟩
  have hC : PolyIn (fun src : YaoSource t => (sourceInstance src).cols) :=
    ⟨columnCoefficient t, 11, instance_cols_bound⟩
  have hB : PolyIn (fun src : YaoSource t => (sourceInstance src).threshold) := by
    refine ⟨4 * t + 6, 1, fun src => ?_⟩
    simpa only [pow_one] using instance_threshold_bound src
  have hR2 : PolyIn (fun src : YaoSource t =>
      (2 ^ v38FieldDegree (edgeBits src.2.1) t) ^ 2) :=
    ⟨(2 ^ (14 * t)) ^ 2 * 2 ^ 10, 10, field_label_count_le⟩
  simp only [writerHeaderBudget, writerCopyBudget, writerSize,
    headerCopyBudget, headerRunBudget, List.length_append]
  repeat' poly_step

theorem writerHeaderBudget_selected_poly {t : ℕ} (G : GLSourceInput t)
    (tableCoefficient : ℕ) :
    ∃ c d : ℕ, ∀ input,
      writerHeaderBudget tableCoefficient (selectedSource G input) ≤
        c * (input.length + 1) ^ d := by
  obtain ⟨c, d, hclock⟩ := poly_writer_header_budget t tableCoefficient
  obtain ⟨cS, dS, hsrc⟩ := CurrentAdditive.V38Machine.source_encoded_length_poly G
  refine ⟨c * (cS + 1) ^ d, dS * d, fun input => ?_⟩
  have hp : 1 ≤ (input.length + 1) ^ dS := Nat.one_le_pow _ _ (by omega)
  have hn : (encode (selectedSource G input)).length + 1 ≤
      (cS + 1) * (input.length + 1) ^ dS := by
    have hs := hsrc input
    nlinarith
  calc
    _ ≤ c * ((encode (selectedSource G input)).length + 1) ^ d := hclock _
    _ ≤ c * ((cS + 1) * (input.length + 1) ^ dS) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn _)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

#print axioms poly_writer_header_budget
#print axioms writerHeaderBudget_selected_poly

end CurrentAdditive.V39ScalarSetup
