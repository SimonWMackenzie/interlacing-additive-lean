import EthInapproximability.CurrentPaper.SourcePrefixRawEntry

namespace EthInapproximability.CurrentPaper.SourcePrefixRawProgram

open Turing BitMachineEncoding
open SourcePrefixRawFrame
open EthInapproximability.CurrentPaper.SourceBooleanPrefix
open scoped Classical

def phase01 (q : Nat) :=
  BitMachineRawSequence.program
    (SourcePrefixRawInput.program q)
    (SourcePrefixRawHeader.program q)
    (SourcePrefixRawHeader.startLabel q)
    none (SourcePrefixRawHeader.initialControl q)

def phase012 (q : Nat) :=
  BitMachineRawSequence.program (phase01 q)
    (SourcePrefixRawVertex.program q)
    BitMachineCopy.Label.scan
    (none, SourcePrefixRawHeader.initialControl q) none

noncomputable def phase0123 (q : Nat) :=
  BitMachineRawSequence.program (phase012 q)
    (SourcePrefixRawLoop.program q)
    (.inr .copyScan)
    ((none, SourcePrefixRawHeader.initialControl q), none)
    (PrefixLoopCallback.initial, none)

noncomputable def program (q : Nat) :=
  BitMachineRawSequence.program (phase0123 q)
    (SourcePrefixRawStash.program q)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (((none, SourcePrefixRawHeader.initialControl q), none),
      (PrefixLoopCallback.initial, none))
    (none, none)

end EthInapproximability.CurrentPaper.SourcePrefixRawProgram
