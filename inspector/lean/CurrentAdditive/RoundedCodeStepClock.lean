import CurrentAdditive.RoundedCodeStep

namespace EthInapproximability.CurrentPaper.RoundedCodeStep

open Turing BitMachineEncoding
noncomputable section

private theorem join_run' {c d : Config} {u : ℕ} (h : run u c = d) (v : ℕ) :
    run (u + v) c = run v d := by
  rw [Nat.add_comm u v]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def cleanupCoefficient : ℕ :=
  1 + RoundedCodeReset.clearCount * BitMachineStackGrowth.perStep program

theorem prefix_to_cleanup (c d : RoundedCodeAdmin.Config) (ta : ℕ)
    (ha : RoundedCodeAdmin.run ta c = d) (hd : d.l = none)
    (kind : Paper2.CodeHeaderMachine.Kind) (hk : d.var.1.1.2 = some kind)
    (e : RoundedCodeHandle.Config) (th : ℕ)
    (hh : RoundedCodeHandle.run th (RoundedCodeHandle.start kind d.stk) = e)
    (he : e.l = none) :
    ∃ t ≤ ta + th + 1,
      run t (adminCfg c) =
        ⟨some (.cleanup (.inl 0)), handleLift kind e.var, e.stk⟩ := by
  obtain ⟨a, hat, har⟩ := admin_to_route c d ta ha hd
  have hr := route_success d.var d.stk kind hk
  obtain ⟨h, hht, hhr⟩ := handle_to_cleanup kind (RoundedCodeHandle.start kind d.stk) e th hh he
  exact ⟨a + 1 + h, by omega, (join_run' ((join_run' har 1).trans hr) h).trans hhr⟩

/-- For the actual source input bank every discarded stack starts empty.
The complete cleanup cost is therefore a fixed linear multiple of the actual
preceding step time, including all newly introduced arithmetic workspaces. -/
theorem source_cleanup_bound (s : Paper2.GeneratorCode.State) (bits : List Bool) (b : ℕ)
    (u : ℕ) (c : Config) (hr : run u (start s bits b) = c) :
    RoundedCodeReset.clock c.stk ≤
      RoundedCodeReset.clearCount * (BitMachineStackGrowth.perStep program * u) +
        RoundedCodeReset.clearCount + 2 := by
  have h := RoundedCodeReset.clock_le_of_run program (start s bits b) u 0 (by
    intro i
    change ((RoundedCodeAdmin.start s bits b).stk (RoundedCodeReset.slot i)).length ≤ 0
    rw [RoundedCodeCanonical.initial_private_blank]
    rfl)
  change RoundedCodeReset.clock (run u (start s bits b)).stk ≤ _ at h
  rw [hr] at h
  simpa only [Nat.zero_add] using h

theorem compose_source_success_clock (s : Paper2.GeneratorCode.State)
    (bits : List Bool) (b : ℕ) (d : RoundedCodeAdmin.Config) (ta : ℕ)
    (ha : RoundedCodeAdmin.run ta (RoundedCodeAdmin.start s bits b) = d) (hd : d.l = none)
    (kind : Paper2.CodeHeaderMachine.Kind) (hk : d.var.1.1.2 = some kind)
    (e : RoundedCodeHandle.Config) (th : ℕ)
    (hh : RoundedCodeHandle.run th (RoundedCodeHandle.start kind d.stk) = e)
    (he : e.l = none) :
    ∃ t ≤ cleanupCoefficient * (ta + th + 1) + RoundedCodeReset.clearCount + 3,
      run t (start s bits b) = ⟨none, finalControl false, RoundedCodeReset.resetBank e.stk⟩ := by
  obtain ⟨u, hu, hr⟩ := prefix_to_cleanup (RoundedCodeAdmin.start s bits b) d ta ha hd
    kind hk e th hh he
  have hc := source_cleanup_bound s bits b u _ hr
  change RoundedCodeReset.clock e.stk ≤
    RoundedCodeReset.clearCount * (BitMachineStackGrowth.perStep program * u) +
      RoundedCodeReset.clearCount + 2 at hc
  obtain ⟨r, hrt, hrr⟩ := cleanup_to_end (handleLift kind e.var).1 e.stk
  refine ⟨u + r, ?_, (join_run' hr r).trans hrr⟩
  have hm := Nat.mul_le_mul_left cleanupCoefficient hu
  have hident : cleanupCoefficient * u =
      u + RoundedCodeReset.clearCount * (BitMachineStackGrowth.perStep program * u) := by
    unfold cleanupCoefficient
    ring
  rw [hident] at hm
  omega

#print axioms source_cleanup_bound
#print axioms compose_source_success_clock

end
end EthInapproximability.CurrentPaper.RoundedCodeStep
