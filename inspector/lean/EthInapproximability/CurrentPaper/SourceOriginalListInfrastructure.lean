import EthInapproximability.CurrentPaper.SourceOriginalListField
import EthInapproximability.CurrentPaper.SourceListMachineInitialize
import EthInapproximability.CurrentPaper.SourceListMachineCounter
import EthInapproximability.CurrentPaper.SourceListEncoding

/-!
# Embedded literal header and counter steps for the source packetizer

The ambient bank may contain the retained unary original n and arbitrary
private stacks of the cited sparsifier. Only the chosen local stacks move.
-/

namespace EthInapproximability.CurrentPaper.SourceOriginalListInfrastructure

open Turing BitMachineEncoding EncodedCommunication

theorem embedded_init {K : Type*} [DecidableEq K]
    (ι : SourceListMachineInitialize.Stack ↪ K)
    (foreign : K → List Bool) (xs : List (List Bool)) :
    ∃ t ≤ 5*xs.length.bits.length+5,
      ((advance (fun l => BitMachineStackEmbedding.stmt ι id id id none
        (SourceListMachineInitialize.program l)))^[t])
        (BitMachineStackEmbedding.cfg ι foreign id id none
          (SourceListMachineInitialize.cfg (some (.inl .scan))
            SourceListMachineInitialize.initialControl
            {input := SourceListEncoding.encode xs})) =
        BitMachineStackEmbedding.cfg ι foreign id id none
          (SourceListMachineInitialize.cfg none
            (SourceListMachineInitialize.doneControl true)
            {input := SourceListEncoding.fields xs,
             count := xs.length.bits,
             output := (natField xs.length).reverse}) := by
  obtain ⟨a, ha, hlocal⟩ := SourceListMachineInitialize.init_encoded xs.length
    (SourceListEncoding.fields xs) []
  let c := SourceListMachineInitialize.cfg (some (.inl .scan))
    SourceListMachineInitialize.initialControl
    {input := SourceListEncoding.encode xs}
  have hc : SourceListEncoding.encode xs =
      natField xs.length ++ SourceListEncoding.fields xs := rfl
  rw [← hc] at hlocal
  have hhalt : (((advance SourceListMachineInitialize.program)^[a]) c).l = none := by
    change (SourceListMachineInitialize.run a c).l = none
    rw [hlocal]
    rfl
  obtain ⟨t, ht, hr⟩ := BitMachineStackEmbedding.outputs ι foreign id id id
    (fun _ => rfl) none SourceListMachineInitialize.program
    (fun l => BitMachineStackEmbedding.stmt ι id id id none
      (SourceListMachineInitialize.program l))
    (fun _ => rfl) c a hhalt
  refine ⟨t, ht.trans ha, ?_⟩
  unfold SourceListMachineInitialize.run at hlocal
  rw [hlocal] at hr
  simpa only [List.append_nil, c] using hr

theorem embedded_counter {K : Type*} [DecidableEq K]
    (ι : SourceListMachineCounter.Stack ↪ K)
    (foreign : K → List Bool) (q : List Bool) :
    ∃ t ≤ 4*q.length+5,
      ((advance (fun l => BitMachineStackEmbedding.stmt ι id id id none
        (SourceListMachineCounter.program l)))^[t])
        (BitMachineStackEmbedding.cfg ι foreign id id none
          (SourceListMachineCounter.cfg (some (.inr .scan))
            SourceListMachineCounter.initialControl q [])) =
        BitMachineStackEmbedding.cfg ι foreign id id none
          (match ProtocolBinaryCounter.subOne q with
          | none => SourceListMachineCounter.cfg none
              (SourceListMachineCounter.doneControl false) q []
          | some q' => SourceListMachineCounter.cfg none
              (SourceListMachineCounter.doneControl true) q' []) := by
  obtain ⟨a, ha, hlocal⟩ := SourceListMachineCounter.counter_run q
  let c := SourceListMachineCounter.cfg (some (.inr .scan))
    SourceListMachineCounter.initialControl q []
  have hhalt : (((advance SourceListMachineCounter.program)^[a]) c).l = none := by
    change (SourceListMachineCounter.run a c).l = none
    rw [hlocal]
    split <;> rfl
  obtain ⟨t, ht, hr⟩ := BitMachineStackEmbedding.outputs ι foreign id id id
    (fun _ => rfl) none SourceListMachineCounter.program
    (fun l => BitMachineStackEmbedding.stmt ι id id id none
      (SourceListMachineCounter.program l))
    (fun _ => rfl) c a hhalt
  refine ⟨t, ht.trans ha, ?_⟩
  unfold SourceListMachineCounter.run at hlocal
  rw [hlocal] at hr
  exact hr

end EthInapproximability.CurrentPaper.SourceOriginalListInfrastructure
