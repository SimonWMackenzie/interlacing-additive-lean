import CurrentAdditive.V38PrinterWhole

/-! Exact physical output framing for the canonical table, conditional only on
the three unary header cells and the already printed row-major table word. -/

namespace CurrentAdditive.V38TablePrinter

open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication
open Paper2.YaoFrame Paper2.HeaderA Paper2.YaoLookup

noncomputable section

theorem canonical_header_run {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    let b := paddedEdgeBits e
    let rows := rowCount v b t
    let cols := columnCount b t d
    let thr := 2 * b + 4 * t + 2
    let bits := (table b t d modulus (le_paddedEdgeCount e) edges).bits
    ∃ steps ≤ UnaryBinaryEncoding.coefficient * (rows + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient * (cols + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient * (thr + 1) ^ 2 +
        (2 * (natField rows ++ natField cols ++ natField thr).length + 2) + 3,
      ((advance Paper2.HeaderA.prog)^[steps])
        (⟨some progStart, progCtl, Hin rows cols thr bits []⟩ :
          TM2.Cfg (fun _ : HB => Bool) _ _) =
        ⟨none, progCtl,
          fun k => if k = outH then
            encodeInstance
              (instanceOfTable b t d modulus (le_paddedEdgeCount e) edges)
          else []⟩ := by
  dsimp only
  let b := paddedEdgeBits e
  let rows := rowCount v b t
  let cols := columnCount b t d
  let thr := 2 * b + 4 * t + 2
  let bits := (table b t d modulus (le_paddedEdgeCount e) edges).bits
  obtain ⟨steps, hsteps, hrun⟩ := header_run_exact rows cols thr bits []
  refine ⟨steps, hsteps, ?_⟩
  rw [hrun]
  congr 1
  funext k
  simp [Hout, instanceOfTable, CurrentAdditive.V38Executable.instanceOfTable,
    Paper2.EncodedSelectedOutput.instanceOf,
    encodeInstance, rows, cols, thr, bits, b]

#print axioms canonical_header_run

end

end CurrentAdditive.V38TablePrinter
