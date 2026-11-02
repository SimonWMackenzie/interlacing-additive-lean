import CurrentAdditive.RoundedCodeStepClock

namespace EthInapproximability.CurrentPaper.RoundedCodeStep

open Turing BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorPositive Paper2.GeneratorStateSize
noncomputable section

private theorem join' {c d : Config} {u : ℕ} (h : run u c = d) (v : ℕ) :
    run (u + v) c = run v d := by
  rw [Nat.add_comm u v]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem done_step (root : Code) (s : State) (hp : PositiveState s) (ht : Trace root s)
    (out bits : List Bool) (b : ℕ)
    (hs : Paper2.GeneratorCode.normalize s = ⟨[], out⟩) :
    ∃ t ≤ cleanupCoefficient * (13 * (codeSize root + 3) ^ 2 + 2) +
        RoundedCodeReset.clearCount + 3,
      run t (start s bits b) =
        ⟨none, finalControl true, (RoundedCodeAdmin.start ⟨[], out⟩ bits b).stk⟩ := by
  obtain ⟨u, hu, hur⟩ := RoundedCodeAdmin.normalize_run root s hp ht bits b
  rw [hs] at hur
  have hd := RoundedCodeAdmin.done_from_ready out bits b
  let d : RoundedCodeAdmin.Config :=
    ⟨none, RoundedCodeAdmin.initial,
      RoundedCodeDraw.inputBank (RoundedCodeAdmin.readyOldBank ⟨[], out⟩ bits b)⟩
  have hadmin : RoundedCodeAdmin.run (u + 1) (RoundedCodeAdmin.start s bits b) = d := by
    rw [RoundedCodeAdmin.run, Nat.add_comm u 1, Function.iterate_add_apply]
    change RoundedCodeAdmin.run 1 (RoundedCodeAdmin.run u _) = _
    rw [hur]
    exact hd
  obtain ⟨v, hv, hvr⟩ := admin_to_route (RoundedCodeAdmin.start s bits b) d (u + 1) hadmin rfl
  have hroute := route_done d.var d.stk (by rfl)
  have hpref := (join' hvr 1).trans hroute
  have hc := source_cleanup_bound s bits b (v + 1) _ hpref
  change RoundedCodeReset.clock d.stk ≤
    RoundedCodeReset.clearCount * (BitMachineStackGrowth.perStep program * (v + 1)) +
      RoundedCodeReset.clearCount + 2 at hc
  obtain ⟨w, hw, hwr⟩ := cleanup_to_end (finalControl true).1 d.stk
  have hbank : RoundedCodeReset.resetBank d.stk =
      (RoundedCodeAdmin.start ⟨[], out⟩ bits b).stk :=
    RoundedCodeCanonical.reset_bank d.stk ⟨[], out⟩ bits b rfl rfl rfl rfl
  refine ⟨v + 1 + w, ?_, ?_⟩
  · have hbound : v + 1 ≤ 13 * (codeSize root + 3) ^ 2 + 2 := by omega
    have hm := Nat.mul_le_mul_left cleanupCoefficient hbound
    have hident : cleanupCoefficient * (v + 1) =
        v + 1 + RoundedCodeReset.clearCount * (BitMachineStackGrowth.perStep program * (v + 1)) := by
      unfold cleanupCoefficient
      ring
    rw [hident] at hm
    omega
  · have hresult := (join' hpref w).trans hwr
    simpa only [hbank] using hresult

#print axioms done_step

end
end EthInapproximability.CurrentPaper.RoundedCodeStep
