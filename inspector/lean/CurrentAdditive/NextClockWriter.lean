import CurrentAdditive.NextClockDimensions

/-! Literal nine-word table-bank preparation and the prepared table clock
are polynomial in the valid encoded source length. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open EthInapproximability.CurrentPaper
open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff
open Paper2.YaoSourceCodec Paper2.YaoLookup Paper2.YaoClockPoly
open Paper2.YaoMachine Paper2.UnaryFieldListParserScratch

set_option maxHeartbeats 2000000

theorem poly_canonicalCellSize (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (fun x : YaoSource t =>
      canonicalCellSize t
        (publicFieldDegree (paddedEdgeBits x.2.1) t) x.2.2) := by
  have hr := poly_public_rows t
  have hc := poly_public_columns t ht
  have hbody := poly_tokens (t := t)
  have hH := poly_H' (t := t)
  have hn := poly_public_width t
  unfold canonicalCellSize
  repeat' poly_step

theorem poly_tableClock (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (fun x : YaoSource t =>
      canonicalTableClockCoefficient *
        (canonicalCellSize t
          (publicFieldDegree (paddedEdgeBits x.2.1) t) x.2.2 + 1)^12) := by
  exact poly_mul (poly_const _)
    (poly_pow (poly_add (poly_canonicalCellSize t ht) (poly_const 1)) 12)

def writerCopyBudget {t : ℕ} (x : YaoSource t) : ℕ :=
  let H := paddedEdgeCount x.2.1
  let d := publicFieldDegree (paddedEdgeBits x.2.1) t
  let n := H*(arity t+1)
  let q := 2^d
  let cap := H^(2^(t-1))
  let rows := rowCount x.1 (paddedEdgeBits x.2.1) t
  let cols := columnCount (paddedEdgeBits x.2.1) t d
  let body := (tokens (List.ofFn (flatten x.2.2))).length
  (2*cap+2)+(2*q^2+2)+(2*H+2)+(2*body+2)+
    (2*arity t+2)+(2*(q^2*n)+2)+(2*n+2)+
    (2*rows+2)+(2*cols+2)

theorem writerCopyCost_eq {t : ℕ} (x : YaoSource t)
    (u c : ℕ)
    (hpacked : sourceFieldOutput x u
      (.field (printerSlots
        CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
      CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.packedBits
        (publicFieldDegree (paddedEdgeBits x.2.1) t) c
        (paddedEdgeCount x.2.1*(arity t+1))) :
    CopyFill.fillCost (writerJobs t 16) (sourceThresholdOutput x u) =
      writerCopyBudget x := by
  obtain ⟨hcap,hR2,hH,hbody,hK,hn,hrows,hcols⟩ :=
    sourceThresholdOutput_writer_inputs x u
  have hfield : (sourceThresholdOutput x u
      (.field (printerSlots
        CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output))).length =
      (2^publicFieldDegree (paddedEdgeBits x.2.1) t)^2 *
        (paddedEdgeCount x.2.1*(arity t+1)) := by
    rw [sourceThresholdOutput_field, hpacked]
    exact packedFieldBits_length _ _ _
  simp [CopyFill.fillCost, writerJobs, writerCopyBudget,
    hcap, hR2, hH, hbody, hK, hfield, hn, hrows, hcols,
    Nat.add_assoc]

theorem poly_writerCopyBudget (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (writerCopyBudget (t := t)) := by
  have hH := poly_H (t := t)
  have hq := poly_public_order t ht
  have hn := poly_public_width t
  have hcap := poly_public_cap t
  have hbody := poly_tokens (t := t)
  have hr := poly_public_rows t
  have hc := poly_public_columns t ht
  unfold writerCopyBudget
  repeat' poly_step

#print axioms poly_canonicalCellSize
#print axioms poly_tableClock
#print axioms writerCopyCost_eq
#print axioms poly_writerCopyBudget

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
