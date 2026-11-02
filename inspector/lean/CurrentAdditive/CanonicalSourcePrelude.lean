import Paper2.YaoMachineRun
import Paper2.YaoClockPoly

/-!
The valid-source front end of the canonical renderer.  This is an actual
two-stage TM2 program: the inherited unary source header parser followed by
the inherited physical prelude.  It starts with only the encoded source on
the input cell.  Its exit bank contains the exact unary vertex count, edge
count, address width, address capacity, arity, and tokenized edge body.
The canonical field and table stages are separate continuations.
-/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoMachine Paper2.YaoPrelude Paper2.YaoHeaderParser
open Paper2.YaoSourceCodec Paper2.YaoLookup
open Paper2.YaoLowerBound
open Paper2.YaoEntryControllerJoin
open Paper2.RecursiveLabelCodecScratch
open Paper2.UnaryFieldListParserScratch

set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def program (t : ℕ) :=
  BitMachineRawSequence.program
    (headerProgram (s5 t 0))
    (preludeFull t 0 (thetaPlace t 0))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    (none, none) (preludeControl t 0, dimsControl)

def initialControl (t : ℕ) :=
  (((none : Option Bool), (none : Option Bool)), (preludeControl t 0, dimsControl))

def sourceReady {t : ℕ} (x : YaoSource t) : WStack t 0 → List Bool :=
  preludeFullOut (thetaPlace t 0)
    (headerOut (s5 t 0) (initBank 0 x []) x.1 x.2.1
      ((bodyCodec t x.1 x.2.1).encode (flatten x.2.2) ++ []))
    x.1 x.2.1

def sourceClock {t : ℕ} (x : YaoSource t) : ℕ :=
  ((2 * (encode x ++ []).length + 2) + (x.1 + x.2.1 + 2) + 1) +
    preludeFullClock t 0 x.1 x.2.1 + 1

theorem physical_source_prelude (t : ℕ) (ht : 1 ≤ t) (x : YaoSource t) :
    ∃ n ≤ sourceClock x, ∃ control,
      ((advance (program t))^[n])
        (⟨some (BitMachineRawSequence.leftLabel Paper2.YaoHeaderParser.startLabel),
          initialControl t, initBank 0 x []⟩ :
            TM2.Cfg (fun _ : WStack t 0 => Bool) _ _) =
        ⟨none, control, sourceReady x⟩ := by
  classical
  have hne0 : ∀ i : Fin 40, i ≠ 0 → (sN i : WStack t 0) ≠ sN 0 := by
    intro i hi h
    exact hi (by simpa [sN, st_injective.eq_iff] using h)
  have hneT : ∀ i : Fin 40,
      (sN i : WStack t 0) ≠ st (.inl (tapeSource t 0)) := by
    intro i h
    simp [sN, st_injective.eq_iff] at h
  have hW0 : ∀ i : Fin 40, i ≠ 0 → initBank 0 x [] (sN i) = [] := by
    intro i hi
    simp [initBank, hne0 i hi, hneT i]
  obtain ⟨t1, ht1, hr1⟩ := physical_header (s5 t 0) (initBank 0 x []) x []
    (by simp [s5, initBank])
    (by simp [s5, initBank, sN, Fin.ext_iff])
    (by simp [s5, initBank, sN, Fin.ext_iff])
    (by simp [s5, initBank, sN, Fin.ext_iff])
    (by simp [s5, initBank, sN, Fin.ext_iff])
  let W1 := headerOut (s5 t 0) (initBank 0 x []) x.1 x.2.1
    ((bodyCodec t x.1 x.2.1).encode (flatten x.2.2) ++ [])
  have hW1s : ∀ i : Fin 40, 5 ≤ i.val → W1 (sN i) = [] := by
    intro i hi
    simp only [W1, headerOut, s5, Function.Embedding.coeFn_mk]
    rw [Function.update_of_ne (by simp [sN, st_injective.eq_iff, Fin.ext_iff]; omega),
      Function.update_of_ne (by simp [sN, st_injective.eq_iff, Fin.ext_iff]; omega),
      Function.update_of_ne (by simp [sN, st_injective.eq_iff, Fin.ext_iff]; omega)]
    exact hW0 i (by intro h; subst h; simp at hi)
  obtain ⟨t2, ht2, c2, hr2⟩ :=
    physical_prelude_full t 0 ht (thetaPlace t 0) W1 x.1 x.2.1
      (by simp [W1, headerOut, s5, thetaPlace, thetaFun, thetaIdx, sN,
        st_injective.eq_iff, Function.update_apply])
      (by simp [W1, headerOut, s5, thetaPlace, thetaFun, thetaIdx, sN,
        st_injective.eq_iff, Function.update_apply])
      (by
        intro i hi
        have := hW1s (thetaIdx i) (by revert hi; revert i; decide)
        simpa [thetaPlace, thetaFun] using this)
      (by
        intro k
        simp only [thetaPlace, thetaFun, Function.Embedding.coeFn_mk,
          W1, headerOut, s5]
        rw [Function.update_of_ne (by simp [sN, st_injective.eq_iff]),
          Function.update_of_ne (by simp [sN, st_injective.eq_iff]),
          Function.update_of_ne (by simp [sN, st_injective.eq_iff])]
        simp [initBank, sN, st_injective.eq_iff])
  obtain ⟨n, hn, hrun⟩ := BitMachineRawSequence.runs
    (headerProgram (s5 t 0)) (preludeFull t 0 (thetaPlace t 0))
    Paper2.YaoHeaderParser.startLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    (none, none) (none, some false) (preludeControl t 0, dimsControl) c2
    (initBank 0 x []) W1 _ t1 t2 hr1 hr2
  exact ⟨n, by unfold sourceClock; omega, _, hrun⟩

/-- The source bits are physically available after the two-stage front end. -/
theorem sourceReady_public_cells {t : ℕ} (x : YaoSource t) :
    sourceReady x (sN 1) =
      Paper2.UnaryFieldListParserScratch.tokens (List.ofFn (flatten x.2.2)) ∧
    sourceReady x (sN 3) = List.replicate x.1 true ∧
    sourceReady x (sN 4) = List.replicate x.2.1 true ∧
    sourceReady x (sN 5) = List.replicate (paddedEdgeBits x.2.1) true ∧
    sourceReady x (sN 6) = List.replicate (paddedEdgeCount x.2.1) true ∧
    sourceReady x (sN 9) = List.replicate (arity t) true := by
  simp [sourceReady, preludeFullOut, preludeOut, headerOut, s5, thetaPlace,
    thetaFun, thetaIdx, sN, st_injective.eq_iff, initBank, bodyCodec,
    piCodec_encode_eq_tokens, Paper2.YaoLookup.paddedEdgeCount, arity]

/-- The physical header-and-prelude clock is polynomial in the valid source
code length for each fixed arity. -/
theorem sourceClock_poly (t : ℕ) (ht : 1 ≤ t) :
    Paper2.YaoClockPoly.PolyIn (fun x : YaoSource t => sourceClock x) := by
  apply Paper2.YaoClockPoly.poly_mono
    (g := fun x : YaoSource t => Paper2.YaoMachine.yaoClock 0 x)
  · intro x
    unfold sourceClock Paper2.YaoMachine.yaoClock
    omega
  · exact Paper2.YaoClockPoly.yaoClock_poly t 0 ht

#print axioms physical_source_prelude
#print axioms sourceReady_public_cells
#print axioms sourceClock_poly

end CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
