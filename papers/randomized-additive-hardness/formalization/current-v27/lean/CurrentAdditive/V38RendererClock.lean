import CurrentAdditive.V38PhysicalRenderer
import CurrentAdditive.V39WriterTailClock
import CurrentAdditive.V39FieldCallerSourceClock

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
namespace CurrentAdditive.V38PhysicalRenderer

open Paper2.YaoSourceCodec Paper2.YaoLookup Paper2.YaoClockPoly
open CurrentAdditive.V38Encoded CurrentAdditive.SmallBias
open CurrentAdditive.V39SourceAddressResource
open CurrentAdditive.V38ReadyScalars (b d H)
open CurrentAdditive.V38TablePrinter.Ambient

theorem scalar_clock_poly (t : ℕ) :
    PolyIn (fun x : YaoSource t =>
      V39ScalarSetup.scalarBudget t x.1 (b x) (H x) (d x)) := by
  refine ⟨V39ScalarSetup.scalarClockCoefficient t,
    V39ScalarSetup.scalarClockDegree t,fun x => ?_⟩
  simpa only [b,d,H,paddedEdgeCount,edgeBits_eq_paddedEdgeBits] using
    V39ScalarSetup.scalarBudget_source_bound x

theorem field_clock_poly (t : ℕ) :
    PolyIn (fun x : YaoSource t => V38AmbientFieldFull.fullClock (b x) t) := by
  refine ⟨((120*(2^(14*t))^5)*2^25),25,fun x => ?_⟩
  exact (V38AmbientFieldFull.fullClock_le (b x) t).trans
    (by simpa only [b,edgeBits_eq_paddedEdgeBits] using
      V39ScalarSetup.complete_caller_budget_source_bound x)

theorem tail_budget_eq {t : ℕ} (x : YaoSource t) :
    preparedBudget t (d x) x.2.2 =
      V39ScalarSetup.writerHeaderBudget V38TablePrinter.canonicalTableClockCoefficient x := by
  simp only [preparedBudget,writerCopyBudget,headerCopyBudget,headerRunBudget,
    V38TablePrinter.canonicalCellSize,
    V39ScalarSetup.writerHeaderBudget,V39ScalarSetup.writerCopyBudget,
    V39ScalarSetup.writerSize,V39ScalarSetup.headerCopyBudget,V39ScalarSetup.headerRunBudget,
    V39SourceRenderer.sourceInstance,V39SourceRenderer.selectedModulus,
    V38Executable.instanceOfTable,Paper2.EncodedSelectedOutput.instanceOf,
    edgeBits_eq_paddedEdgeBits,b,d,H,paddedEdgeCount]

theorem tail_clock_poly (t : ℕ) :
    PolyIn (fun x : YaoSource t => preparedBudget t (d x) x.2.2) := by
  simpa only [tail_budget_eq] using
    V39ScalarSetup.poly_writer_header_budget t V38TablePrinter.canonicalTableClockCoefficient

theorem clock_poly (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (fun x : YaoSource t => clock x) := by
  have hf := V38SourceFront.clock_poly t (by omega)
  have hs := scalar_clock_poly t
  have hfield := field_clock_poly t
  have htail := tail_clock_poly t
  unfold clock V38ReadyField.clock V38ReadyScalars.clock
  repeat' poly_step

#print axioms scalar_clock_poly
#print axioms field_clock_poly
#print axioms tail_budget_eq
#print axioms clock_poly
end CurrentAdditive.V38PhysicalRenderer
