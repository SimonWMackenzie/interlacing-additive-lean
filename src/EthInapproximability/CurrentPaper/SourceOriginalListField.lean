import EthInapproximability.CurrentPaper.SourceListMachineFields
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Physical one-field extraction in an arbitrary source producer bank

The original-n word and all cited-source private stacks live outside this
seven-stack field parser. The theorem states an exact embedded run, not a
unit-cost list lookup.
-/

namespace EthInapproximability.CurrentPaper.SourceOriginalListField

open Turing BitMachineEncoding EncodedCommunication

theorem embedded_field {K : Type*} [DecidableEq K]
    (ι : SourceListMachineFields.Stack ↪ K)
    (foreign : K → List Bool) (word suffix : List Bool) :
    ∃ t ≤ 20*(word.length+1)*(word.length.bits.length+1),
      ((advance (fun l => BitMachineStackEmbedding.stmt ι id id id none
        (SourceListMachineFields.program l)))^[t])
        (BitMachineStackEmbedding.cfg ι foreign id id none
          (SourceListMachineFields.cfg (some (.inl .scan))
            SourceListMachineFields.initialControl
            {input := natField word.length ++ (word ++ suffix)})) =
        BitMachineStackEmbedding.cfg ι foreign id id none
          (SourceListMachineFields.success word suffix) := by
  obtain ⟨a, ha, hlocal⟩ := SourceListMachineFields.field_encoded word suffix
  let c := SourceListMachineFields.cfg (some (.inl .scan))
    SourceListMachineFields.initialControl
    {input := natField word.length ++ (word ++ suffix)}
  have hhalt : (((advance SourceListMachineFields.program)^[a]) c).l = none := by
    change (SourceListMachineFields.run a c).l = none
    rw [hlocal]
    rfl
  obtain ⟨t, ht, hr⟩ := BitMachineStackEmbedding.outputs ι foreign id id id
    (fun _ => rfl) none SourceListMachineFields.program
    (fun l => BitMachineStackEmbedding.stmt ι id id id none
      (SourceListMachineFields.program l))
    (fun _ => rfl) c a hhalt
  refine ⟨t, ht.trans ha, ?_⟩
  change ((advance _)^[t]) (BitMachineStackEmbedding.cfg ι foreign id id none c) = _
  unfold SourceListMachineFields.run at hlocal
  rw [hlocal] at hr
  exact hr

end EthInapproximability.CurrentPaper.SourceOriginalListField
