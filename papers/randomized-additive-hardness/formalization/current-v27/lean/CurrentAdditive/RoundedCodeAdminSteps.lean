import CurrentAdditive.RoundedCodeAdmin

namespace EthInapproximability.CurrentPaper.RoundedCodeAdmin

open Turing BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
noncomputable section

private theorem join_run {c d : Config} {u : ℕ} (h : run u c = d) (v : ℕ) :
    run (u + v) c = run v d := by
  rw [Nat.add_comm u v]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem ticket_from_ready (a b : ℕ) (ha : 0 < a)
    (cs : List Code) (out : List Bool) (bits : Fin b → Bool) (suffix : List Bool) :
    ∃ t ≤ 1 + RoundedLoadedClock.coefficient * (a + b + 2) ^ 2,
      let input := Paper2.CappedTicketMachine.ticketWord bits ++ suffix
      let S := readyOldBank ⟨.ticket a :: cs, out⟩ input b
      run t (ready ⟨.ticket a :: cs, out⟩ input b) =
        ⟨none, (kindControl .ticket, RoundedLoadedDraw.initial),
          RoundedCodeDraw.resultBank S a b input suffix
            ((Paper2.RecursiveLabelCodecScratch.finCodec a).encode
              (CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
                (Paper2.CappedSampler.bitsTicketEquiv b bits)))⟩ := by
  let input := Paper2.CappedTicketMachine.ticketWord bits ++ suffix
  let S := readyOldBank ⟨.ticket a :: cs, out⟩ input b
  obtain ⟨t, ht, hr⟩ := draw_run .ticket S a b ha bits suffix
    (by rfl) (by rfl) (by rfl) (by rfl)
  refine ⟨1 + t, by omega, ?_⟩
  exact (join_run (route_ticket a cs out input b) t).trans hr

theorem branch_from_ready (a b : ℕ) (ha : 0 < a)
    (firstCut secondCut : ℕ) (first second third : Code)
    (cs : List Code) (out : List Bool) (bits : Fin b → Bool) (suffix : List Bool) :
    ∃ t ≤ 1 + RoundedLoadedClock.coefficient * (a + b + 2) ^ 2,
      let input := Paper2.CappedTicketMachine.ticketWord bits ++ suffix
      let state : State := ⟨.branch3 a firstCut secondCut first second third :: cs, out⟩
      let S := readyOldBank state input b
      run t (ready state input b) =
        ⟨none, (kindControl .branch3, RoundedLoadedDraw.initial),
          RoundedCodeDraw.resultBank S a b input suffix
            ((Paper2.RecursiveLabelCodecScratch.finCodec a).encode
              (CurrentAdditive.RoundedDraw.draw a (2 ^ b) ha (by positivity)
                (Paper2.CappedSampler.bitsTicketEquiv b bits)))⟩ := by
  let input := Paper2.CappedTicketMachine.ticketWord bits ++ suffix
  let state : State := ⟨.branch3 a firstCut secondCut first second third :: cs, out⟩
  let S := readyOldBank state input b
  obtain ⟨t, ht, hr⟩ := draw_run .branch3 S a b ha bits suffix
    (by rfl) (by rfl) (by rfl) (by rfl)
  refine ⟨1 + t, by omega, ?_⟩
  exact (join_run (route_branch a firstCut secondCut first second third cs out input b) t).trans hr

theorem done_from_ready (out bits : List Bool) (b : ℕ) :
    run 1 (ready ⟨[], out⟩ bits b) =
      ⟨none, initial, RoundedCodeDraw.inputBank (readyOldBank ⟨[], out⟩ bits b)⟩ := by
  simp [run, ready, initial, adminInitial, program, BitMachineEncoding.advance,
    TM2.step, TM2.stepAux, Paper2.CodeAdminReady.stopped,
    Paper2.CodeAdminMachine.cfg]

#print axioms ticket_from_ready
#print axioms branch_from_ready
#print axioms done_from_ready

end
end EthInapproximability.CurrentPaper.RoundedCodeAdmin
