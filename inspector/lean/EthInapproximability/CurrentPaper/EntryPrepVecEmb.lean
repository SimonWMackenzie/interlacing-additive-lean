import EthInapproximability.CurrentPaper.EntryPrepCopyRun
import EthInapproximability.CurrentPaper.EntryPrepVecQ
import EthInapproximability.CurrentPaper.EntryPrepBudget2

/-!
# Segment 5b (part 2): the q/vectors workspace outside the tail region

Lane owner:b-stage4-entry-program-7 (Paper B, unit 2, map item 3).

A3 layout decision: the 137-cell workspace `VectorsFromGraphQ.Z2` is embedded (`ζ`) into
known-blank non-writer cells that are NOT in the range of the tail embedding
(`Out = {z : NWIdx // z ∉ range regionEmb}`, 176 cells). So the workspace never overlaps
a tail cell or a level-writer cell, it is blank in `midBank` (`mid_zeta`), and clearing it
restores `midBank` there. The placement is a fixed classical choice (like `regionEmb0`).
-/

namespace EthInapproximability.CurrentPaper.EntryPrepVec

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready OuterLevel0Prep
open EntryPrepBudget EntryTailEmbed EntryTailClear EntryPrepCopy

/-- Known-blank non-writer cells outside the tail region. -/
abbrev Out := {z : NWIdx // z ∉ Set.range regionEmb}

noncomputable instance instFintypeOut : Fintype Out := Fintype.ofFinite _

theorem card_Out : Fintype.card Out = 176 := by
  classical
  have h1 : Fintype.card Out = Fintype.card NWIdx - Fintype.card (Set.range regionEmb) := by
    convert Fintype.card_subtype_compl (fun z : NWIdx => z ∈ Set.range regionEmb)
  rw [h1, Set.card_range_of_injective regionEmb.injective, card_NWIdx, card_region]

theorem card_Z2_le : Fintype.card VectorsFromGraphQ.Z2 ≤ Fintype.card Out := by
  have h1 : Fintype.card VectorsFromGraphQ.Z2 = 137 := by convert EntryPrepBudget.card_Z2
  rw [h1, card_Out]
  decide

noncomputable def ζ0 : VectorsFromGraphQ.Z2 ↪ Out :=
  Classical.choice (Function.Embedding.nonempty_of_card_le card_Z2_le)

noncomputable def ζ : VectorsFromGraphQ.Z2 ↪ HStack :=
  ⟨fun x => nwMap (ζ0 x).1, fun a b h => ζ0.injective (Subtype.ext (nwMap_inj h))⟩

theorem ζ_apply (x : VectorsFromGraphQ.Z2) : ζ x = nwMap (ζ0 x).1 := rfl

theorem tail_ne_ζ (j : TSt) (x : VectorsFromGraphQ.Z2) : tailEmb j ≠ ζ x := by
  rcases j with a | k | i
  · intro h
    exact (ζ0 x).2 ⟨_, nwMap_inj h⟩
  · exact fun h => nwMap_ne_wcell _ k h.symm
  · intro h
    exact (ζ0 x).2 ⟨_, nwMap_inj h⟩

theorem nwMap_ne_mGw (z : NWIdx) : nwMap z ≠ mcell .Gw := by
  rcases z with x | r
  · intro h; cases h
  · rcases r with y | u | d | j | u | i | i | e <;> intro h <;> cases h

theorem ζ_ne_mGw (x : VectorsFromGraphQ.Z2) : ζ x ≠ mcell .Gw := nwMap_ne_mGw _

theorem tail_ne_mGw (j : TSt) : tailEmb j ≠ mcell .Gw := by
  rcases j with a | k | i
  · exact nwMap_ne_mGw _
  · intro h; cases h
  · exact nwMap_ne_mGw _

variable (Mm : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem mid_zeta (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (x : VectorsFromGraphQ.Z2) : midBank Mm G n c F Q P (ζ x) = [] := by
  unfold midBank
  rw [bank_outside _ _ _ _ (fun ⟨j, hj⟩ => tail_ne_ζ j x hj)]
  exact exit_blank_nw Mm G n c F Q P _

theorem mid_mGw (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    midBank Mm G n c F Q P (mcell .Gw) =
      EncodedGraph.encode (EncodedETHSource.serializeGraph G) := by
  unfold midBank
  rw [bank_outside _ _ _ _ (fun ⟨j, hj⟩ => tail_ne_mGw j hj)]
  show G4 (level0RowsBank Mm G n c F Q P) (Sum.inl (mc .Gw)) = _
  rw [WeightedLevel0Masters.ready_master Mm G n c F Q P .Gw (by decide) (by decide)
    (fun m h => by cases h)]
  exact (WeightedLevel0Masters.masterC_values Mm G n c).2.2.2.2.1

theorem mid_tail (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (j : TSt) :
    midBank Mm G n c F Q P (tailEmb j) =
      RawTableTail.startBank (EntryRunsRaw.cellBank (wMid G n c)) (r0 G n c) (c0 G n c)
        (Wlvl Mm G n c F Q P) j := by
  unfold midBank
  rw [bank_at]

/-! ## One push -/

def pushP (k : HStack) : Unit → TM2.Stmt (fun _ : HStack => Bool) Unit Unit :=
  fun _ => TM2.Stmt.push k (fun _ => true) TM2.Stmt.halt

theorem push_run (k : HStack) (S : HStack → List Bool) :
    ((advance (pushP k))^[1]) (⟨some (), (), S⟩ : TM2.Cfg (fun _ : HStack => Bool) Unit Unit) =
      ⟨none, (), Function.update S k (true :: S k)⟩ := by
  simp only [Function.iterate_one, advance, TM2.step, pushP, TM2.stepAux, Option.getD_some]

#print axioms card_Out
#print axioms tail_ne_ζ
#print axioms mid_zeta
#print axioms mid_mGw
#print axioms push_run

end EthInapproximability.CurrentPaper.EntryPrepVec
