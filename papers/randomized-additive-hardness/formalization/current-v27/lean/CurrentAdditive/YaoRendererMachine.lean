import CurrentAdditive.NextClockFinal

/-! Relabel the single physical source-started renderer as an ordinary
finite-index bit machine. This file is subsequent to the frozen valid-source
packet. -/

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 65536

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.SmallBias
open CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec
open Paper2.YaoFrame Paper2.HeaderA

def rendererInputCell (t : ℕ) : Cell t 16 :=
  .source (sN 0)

def rendererOutputCell (t : ℕ) : Cell t 16 :=
  .header outH

noncomputable def rendererMachine (t : ℕ) : BitMachine.Machine :=
  ofFinite (P := rendererProgram t)
    (rendererInputCell t) (rendererOutputCell t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel
                      Paper2.YaoHeaderParser.startLabel)))))))))
    ((((((((CanonicalSourcePrelude.initialControl t,
      (none, (none, none))),
      ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        YaoDegreeMachine.afterCtrl)),
      ((none, none), (none, ((), false)))),
      (none, ((), (none, (false, false))))),
      (none, (none, ((), ((), (false, false)))))),
      ((none, none), prepEmbed none)),
      ((MultiMove.initial, ()), (false, (false, false)))),
      ((none, (none, (none, ()))),
        ((MultiMove.initial, writerTableControl),
          (MultiMove.initial, progCtl))))

theorem renderer_initial_bank (t : ℕ) (x : YaoSource t) :
    bank (sourceEmbed t 16) (blank t 16)
      (Paper2.YaoMachine.initBank 0 x []) =
    (fun j : Cell t 16 =>
      if j = rendererInputCell t then encode x else []) := by
  have hlocal : Paper2.YaoMachine.initBank 0 x [] =
      Function.update (fun _ => []) (sN 0) (encode x) := by
    funext j
    simp [Paper2.YaoMachine.initBank, Function.update]
  have hblank : bank (sourceEmbed t 16) (blank t 16)
      (fun _ => []) = blank t 16 := by
    apply bank_eq_self
    intro k
    rfl
  rw [hlocal, bank_update, hblank]
  funext j
  simp [blank, rendererInputCell, sourceEmbed, Function.update]

#print axioms renderer_initial_bank

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
