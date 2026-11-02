import CurrentAdditive.NumericCallbackPreparedJoin

/-! The numeric bits printed by the physical coordinate callback are the
ordered-alphabet code of the corresponding typed Code D coordinate. -/

namespace CurrentAdditive.TypedNumericCodeDJoin

open Paper2
open CurrentAdditive.ExecutableCodeSource
open CurrentAdditive.IndexedExecutableStep
open CurrentAdditive.OrderedAlphabetCodec
open CurrentAdditive.InjectiveCodeDTransport
open CurrentAdditive.SequentialSourceCode
open CurrentAdditive.IndexedExecutableStepRecovery
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open CurrentAdditive.MinimumRatioContext.MachineInvokeFull
open CurrentAdditive.CodeDCanonicalSourceV2
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Turing

theorem typed_physical_coordinate {Y : Type} [Fintype Y] [DecidableEq Y]
    (D q : Nat) (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ)
    (j : Fin (codeDArray D q μ table).size) (p : Fin q)
    (T : StackN contextTwoSize → List Bool)
    (h0 : T 0 = codeDGetterPacket
      (encodedSource (mapSource (encode μ table) (codeDArray D q μ table)))
      (numericPosition D q μ table j).val)
    (h6 : T 6 = List.replicate p.val true)
    (hlow : ∀ k : StackN contextTwoSize,
      1 ≤ k.val → k.val < 32 → k.val ≠ 6 → T k = [])
    (hhigh : ∀ k : StackN contextTwoSize,
      32 ≤ k.val → T k = []) :
    ∃ t,
      (((advance numericCoordinateProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
                recordSlots)))),
          (((CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              recordSlots,
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              wordSlots),
            ((((), none), ((), none)), none)),
           CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              coordinateSlots),
           coordinateReady T (List.replicate p.val true)⟩)).stk
          (6 : StackN contextTwoSize) =
        (encode μ table ((fromTable D q μ table).decode
          (codeDArrayPosition D q μ table j) p)).bits := by
  obtain ⟨t, ht⟩ := prepared_numeric_callback
    (mapSource (encode μ table) (codeDArray D q μ table))
    (numericPosition D q μ table j) p T h0 h6 hlow hhigh
  refine ⟨t, ?_⟩
  simpa only [numeric_coordinate_is_typed_position] using ht

#print axioms typed_physical_coordinate

end CurrentAdditive.TypedNumericCodeDJoin
