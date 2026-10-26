import Paper2.A4T10Machine
import Paper2.A4PolyIn

/-!
# Unit 4 (Paper A), segment A4-S3 residue: polynomial envelope of the T10 chain clock

Owner lane `owner:a-unit4-shell-2` (private, 25 September 2026). Compiled with the frozen
B object roots (`-WithB`), because it imports the predecessor's `A4T10Machine` (frozen,
ACCEPT-CONDITIONAL on blockers B-1/B-2 of `a-unit4-shell-owner-audit/AUDIT.md`).

`chainTime D B Φ` (the literal charged clock of `T10Machine.chain D B`) is bounded by a fixed
polynomial of `|encode Φ|`. Every intermediate packet length is bounded by the banked
`BitMachine.output_length_bound` applied to the stage's own `item_run` (so no stage output is
assumed small), and every stage clock is the stage's literal `itemBound`. The records `D`
(X03), `B` (X04) remain parameters (D-A7 open).

**None of these statements closes a ledger row** (T10 stays open).
-/

namespace Paper2.Unit4Shell.T10Envelope

open EthInapproximability.CurrentPaper
open Paper2.Unit4Shell.Poly

variable (D : EncodedETHSource.DinurReduction)
  (B : EncodedETHSource.BOTReduction (EncodedETHSourceComposition.booleanOccurrence D))

/-- The input size. -/
def L (Φ : EncodedETHSource.ValidFormula) : ℕ := (EncodedCNF.encode Φ.val).length

theorem x0_poly : PolyIn L (fun Φ =>
    (SourceOriginalBranchPackets.sparsePacket Φ.val.variables Φ).length) := by
  refine mono (b := fun Φ => 4 * L Φ + 2) (fun Φ => ?_) (add (mul (const 4) self) (const 2))
  have h := SourceOriginalVariableCapture.original_n_le_input Φ.val
  simp only [SourceOriginalBranchPackets.sparsePacket, SourceOriginalBranchPackets.packet_length, L]
  omega

theorem t1_poly : PolyIn L (fun Φ => SourceOriginalDinurListMapper.itemBound D
    (SourceOriginalBranchPackets.sparsePacket Φ.val.variables Φ)) := by
  unfold SourceOriginalDinurListMapper.itemBound
  exact mul (const _) (pow (add x0_poly (const 3)) _)

theorem x1_poly : PolyIn L (fun Φ =>
    (SourceOriginalDinurListMapper.cspPacket D Φ.val.variables Φ).length) := by
  refine mono (fun Φ => BitMachine.output_length_bound _
    (SourceOriginalDinurListMapper.item_run D Φ Φ.val.variables))
    (add x0_poly (mul (t1_poly D) (const _)))

theorem t2_poly : PolyIn L (fun Φ => SourceGenericComposite.BooleanListMapper.itemBound D
    (SourceOriginalDinurListMapper.cspPacket D Φ.val.variables Φ)) := by
  unfold SourceGenericComposite.BooleanListMapper.itemBound
  exact add (mul (const 7) (add (x1_poly D) (const 2)))
    (mul (const _) (mul (const _) (pow (add (x1_poly D) (const 1)) 27)))

theorem x2_poly : PolyIn L (fun Φ =>
    (SourceGenericComposite.BooleanListMapper.boolPacket D Φ.val.variables Φ).length) := by
  refine mono (fun Φ => BitMachine.output_length_bound _
    (SourceGenericComposite.BooleanListMapper.item_run D Φ.val.variables Φ))
    (add (x1_poly D) (mul (t2_poly D) (const _)))

theorem t3_poly : PolyIn L (fun Φ => SourceOriginalBOTListMapper.itemBound B
    (SourceGenericComposite.BooleanListMapper.boolPacket D Φ.val.variables Φ)) := by
  unfold SourceOriginalBOTListMapper.itemBound
  exact mul (const _) (pow (add (x2_poly D) (const 3)) _)

/-- **Polynomial envelope of the T10 chain clock.** There are fixed `C, E` (depending only on
the records `D`, `B`) with `chainTime D B Φ ≤ C·(|encode Φ|+1)^E` for every valid `Φ`.
Does not close a ledger row. -/
theorem chainTime_poly : PolyIn L (T10Machine.chainTime D B) := by
  unfold T10Machine.chainTime
  exact add (add (add (t1_poly D) (mul (const 2) (x1_poly D))) (const 2))
    (add (add (add (t2_poly D) (mul (const 2) (x2_poly D))) (const 2)) (t3_poly D B))

/-- The chain's output packet is polynomially long in `|encode Φ|` (banked
`output_length_bound` on the checked `chain_outputs`). -/
theorem chainOutput_poly : PolyIn L (fun Φ => (SourceOriginalBranchPackets.packet
    Φ.val.variables (EncodedGraph.encode (T10Finite.t10Graph D B Φ))).length) :=
  mono (fun Φ => BitMachine.output_length_bound _ (T10Machine.chain_outputs D B Φ))
    (add x0_poly (mul (chainTime_poly D B) (const _)))

end Paper2.Unit4Shell.T10Envelope
