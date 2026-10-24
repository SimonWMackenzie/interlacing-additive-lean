import Paper2.YaoOperationalShared
import EthInapproximability.CurrentPaper.MatrixTemplateMachine

/-!
One physical subroutine of the frozen v12 Yao entry. The input is a prepared
big-endian selector word and a literal payload slice at the given position.
The fixed five-stack program performs binary decoding, unary address
construction, sequential indexed lookup, output push, and bank cleanup.
Preparation of the two input banks is not charged by this theorem.
-/

namespace Paper2.YaoPhysicalSlice

open Paper2.YaoLookup Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open EthInapproximability.CurrentPaper

/-- The literal payload bits, across *all* selector addresses, at one
sample label and one edge position. This is not a precomputed answer bit. -/
def payloadSlice (t b lambda : ℕ) (bits : SerializedTape t b lambda)
    (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) : List Bool :=
  List.ofFn (fun h : Fin (2 ^ b) => readTape t b lambda bits (.inr (l, h, p)))

theorem payloadSlice_length (t b lambda : ℕ) (bits : SerializedTape t b lambda)
    (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) :
    (payloadSlice t b lambda bits l p).length = 2 ^ b := by
  simp [payloadSlice]

theorem payloadSlice_get (t b lambda : ℕ) (bits : SerializedTape t b lambda)
    (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) (h : Fin (2 ^ b)) :
    (payloadSlice t b lambda bits l p)[h.val]?.getD false =
      readTape t b lambda bits (.inr (l, h, p)) := by
  simp [payloadSlice, h.isLt]

/-- The selector bank is the canonical big-endian encoding of the address
computed from the actual little-endian fair-bit selector block. Its physical
extraction/reordering from the flat tape is deliberately outside this call. -/
def selectorWord (t b lambda : ℕ) (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) : List Bool :=
  List.ofFn ((MatrixMaterialization.wordCode b).symm
    (CappedSampler.bitsTicketEquiv b
      (fun i => readTape t b lambda bits (.inl (z, g, i)))))

theorem selectorWord_length (t b lambda : ℕ) (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) :
    (selectorWord t b lambda bits z g).length = b := by
  simp [selectorWord]

/-- A physical, fixed-control binary selector decoder and indexed payload
lookup. Every bit moved by the program, including its temporary unary
counter and cleanup, is priced in the displayed `TM2` transition bound.
The supplied input banks are identified exactly and are not part of that
bound. The output is appended to an arbitrary prior output suffix. -/
theorem physical_payload_slice (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1)))
    (l : Fin (payloadCount t b lambda))
    (p : Fin (2 ^ t * 2 ^ t + 1)) (out : List Bool) :
    ∃ steps ≤ 6 * (2 ^ b) + 3 * b + 6,
      MatrixTemplateMachine.run steps
        (MatrixTemplateMachine.initial
          (selectorWord t b lambda bits z g)
          (payloadSlice t b lambda bits l p) out) =
        MatrixTemplateMachine.cfg none ((false, false), (false, false)) [] []
          (readTape t b lambda bits
            (.inr (l, CappedSampler.bitsTicketEquiv b
              (fun i => readTape t b lambda bits (.inl (z, g, i))), p)) :: out) := by
  let h := CappedSampler.bitsTicketEquiv b
    (fun i => readTape t b lambda bits (.inl (z, g, i)))
  have hr := MatrixTemplateMachine.sampled_label_run h
    (payloadSlice t b lambda bits l p) out
  rcases hr with ⟨steps, hsteps, hrun⟩
  refine ⟨steps, ?_, ?_⟩
  · rw [payloadSlice_length] at hsteps
    have hh := h.isLt
    omega
  · change MatrixTemplateMachine.run steps
        (MatrixTemplateMachine.initial
          (selectorWord t b lambda bits z g)
          (payloadSlice t b lambda bits l p) out) = _ at hrun
    rw [payloadSlice_get] at hrun
    exact hrun

/-- Instantiate the supplied position with the literal indexed edge-position
evaluator. The program output is now exactly the entry of the same matrix
used by the finite Yao lower-bound theorem, for real or padded edges. -/
theorem physical_matrix_entry {v e : ℕ} (t lambda : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda)
    (vertex : Fin v) (z : Fin (selectorCount t (paddedEdgeBits e) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount e))
    (l : Fin (payloadCount t (paddedEdgeBits e) lambda))
    (out : List Bool) :
    ∃ steps ≤ 6 * paddedEdgeCount e + 3 * paddedEdgeBits e + 6,
      MatrixTemplateMachine.run steps
        (MatrixTemplateMachine.initial
          (selectorWord t (paddedEdgeBits e) lambda bits z g)
          (payloadSlice t (paddedEdgeBits e) lambda bits l
            (positionEval (paddedEdgesEval edges) a vertex)) out) =
        MatrixTemplateMachine.cfg none ((false, false), (false, false)) [] []
          (matrixFromTape t lambda edges
            (readTape t (paddedEdgeBits e) lambda bits)
            (vertex, z) (g, a, l) :: out) := by
  obtain ⟨steps, ht, hr⟩ := physical_payload_slice t (paddedEdgeBits e) lambda bits z g l
    (positionEval (paddedEdgesEval edges) a vertex) out
  refine ⟨steps, ?_, ?_⟩
  · simpa [paddedEdgeCount] using ht
  · convert hr using 1

/-- Empty edge sets still use the padded address space of size one. No
source-edge positivity hypothesis is hidden in the physical entry theorem. -/
theorem physical_matrix_entry_empty_edges {v : ℕ} (t lambda : ℕ)
    (edges : Fin 0 → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits 0) lambda)
    (vertex : Fin v) (z : Fin (selectorCount t (paddedEdgeBits 0) lambda))
    (g : Fin (2 ^ (t - 1))) (a : Fin (paddedEdgeCount 0))
    (l : Fin (payloadCount t (paddedEdgeBits 0) lambda))
    (out : List Bool) :
    ∃ steps ≤ 6 * paddedEdgeCount 0 + 3 * paddedEdgeBits 0 + 6,
      MatrixTemplateMachine.run steps
        (MatrixTemplateMachine.initial
          (selectorWord t (paddedEdgeBits 0) lambda bits z g)
          (payloadSlice t (paddedEdgeBits 0) lambda bits l
            (positionEval (paddedEdgesEval edges) a vertex)) out) =
        MatrixTemplateMachine.cfg none ((false, false), (false, false)) [] []
          (matrixFromTape t lambda edges
            (readTape t (paddedEdgeBits 0) lambda bits)
            (vertex, z) (g, a, l) :: out) :=
  physical_matrix_entry t lambda edges bits vertex z g a l out

#print axioms payloadSlice_get
#print axioms physical_payload_slice
#print axioms physical_matrix_entry
#print axioms physical_matrix_entry_empty_edges

end Paper2.YaoPhysicalSlice
