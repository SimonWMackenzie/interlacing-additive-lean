import Paper2.A4Packetizer
import Paper2.A4PairMap
import Paper2.A4BankOut

/-!
# Unit 4 (Paper A), segment 1 (owner lane `owner:a-unit4-shell-3`): `H_T10Front` discharged

Production universe: `R3T10Machine`/`R3T10Envelope`/`R3T10Front`/`R3Packetizer` are
import-only copies of the frozen `A4T10Machine` (owner), `A4T10Envelope`/`A4T10Front`
(owner-2) and the Codex-checked `A4Packetizer`, importing the ADMITTED production modules
(`EthInapproximability.CurrentPaper.SourceGenericBooleanListMapper`, `Paper2.A4T10Finite`,
`Paper2.A4Shells`) instead of their bare private copies. **No ledger row is closed.**
-/

namespace Paper2.Unit4Shell.FrontClosed

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

/-- The generic glue contract `H_PairMap` holds (physical combinator `PairMap.machine`). -/
theorem H_PairMap_holds : T10Front.H_PairMap := PairMap.pair_map

/-- The generic glue contract `H_BankOut k` holds for every `k` (physical `BankOut.machine k`). -/
theorem H_BankOut_holds (k : ℕ) : T10Front.H_BankOut k := BankOut.bank_out k

/-- **The T10 front, discharged.** For every pair of cited records `D : DinurReduction` (X03)
and `B : BOTReduction (booleanOccurrence D)` (X04), parameters pending the author's D-A7, and
every fixed `k`, the HYP interface `Shells.H_T10Front D B k` holds: one fixed machine maps the
literal word `pair (encode Φ) tape` to the literal H-A3 bank
`encode ![encode (t10Graph D B Φ), 1^k, tape]` within `CF·(|input|+1)^EF`, for every valid
`Φ` and every tape of the selected law. The machine is
`composition (PairMap packetizer) (composition (PairMap (T10Machine.chain D B)) (BankOut k))`;
the middle stage of `T10Machine.chain D B` is the admitted Paper B generic-alphabet converter
(`SourceGenericComposite.BooleanListMapper.itemMachine D`, the lifted
`ConverterMachine.machine D.alphabet D.arity D.arity_pos`, correct by
`ConverterMachine.machine_dinur`). Every handoff is charged. Valid `Φ` only (malformed-input
routing is not covered). Does not close a ledger row. -/
theorem H_T10Front_holds (D : DinurReduction) (B : BOTReduction (booleanOccurrence D)) (k : ℕ) :
    Shells.H_T10Front D B k :=
  T10Front.front_of_glue D B H_PairMap_holds PairMapGlue.H_Packetizer_holds k (H_BankOut_holds k)

#print axioms H_PairMap_holds
#print axioms H_BankOut_holds
#print axioms H_T10Front_holds

end Paper2.Unit4Shell.FrontClosed
