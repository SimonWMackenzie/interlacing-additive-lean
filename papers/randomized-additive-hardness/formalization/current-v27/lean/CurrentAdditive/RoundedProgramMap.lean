import CurrentAdditive.RoundedProgram
namespace CurrentAdditive.RoundedProgram

open Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingCapped
open CurrentAdditive.RoundedDraw
noncomputable section
set_option maxHeartbeats 1000000

variable {α β : Type*}

theorem runBitsRounded_map (f : α → β) (b N : ℕ) (p : Program α)
    (bits : BitBlocks b N) :
    runBitsRounded denominator step b denominator_pos N (Program.map f p) bits =
      Program.map f (runBitsRounded denominator step b denominator_pos N p bits) := by
  induction N generalizing p with
  | zero => rfl
  | succ N ih =>
      cases p with
      | pure a => exact ih (.pure a) bits.2
      | draw n hn next =>
          exact ih (next (draw n (2 ^ b) hn (by positivity)
            (Paper2.CappedSampler.bitsTicketEquiv b bits.1))) bits.2

def mapState {A : ℕ} (f : α → β) (s : State α A) : State β A :=
  ⟨Program.map f s.val, by simpa only [Program.maxAlphabet_map] using s.property⟩

theorem runState_map {A : ℕ} (f : α → β) (b N : ℕ) (s : State α A)
    (bits : BitBlocks b N) :
    (runState b N (mapState f s) bits).val = Program.map f (runState b N s bits).val := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
      rcases s with ⟨p, hp⟩
      cases p with
      | pure a => exact ih ⟨.pure a, hp⟩ bits.2
      | draw n hn next =>
          exact ih (stateStep ⟨.draw n hn next, hp⟩ (draw n (2 ^ b) hn (by positivity)
            (Paper2.CappedSampler.bitsTicketEquiv b bits.1))) bits.2

theorem leafValue_spec (p : Program α) (h : p.maxDraws = 0) :
    p = .pure (leafValue p h) := by
  cases p with
  | pure a => rfl
  | draw n hn next => simp at h

theorem runProgram_map {A : ℕ} (f : α → β) (b N : ℕ) (s : State α A)
    (hN : s.val.maxDraws ≤ N) (bits : BitBlocks b N) :
    runProgram b N (mapState f s) (by simpa only [mapState, Program.maxDraws_map] using hN) bits =
      f (runProgram b N s hN bits) := by
  have hzero : (runState b N s bits).val.maxDraws = 0 := by
    have h := runState_draws_le b N s bits
    omega
  have he : (runState b N (mapState f s) bits).val =
      .pure (f (runProgram b N s hN bits)) := by
    rw [runState_map, leafValue_spec _ hzero]
    rfl
  exact leafValue_of_eq_pure _ _ _ he

#print axioms runProgram_map

end
end CurrentAdditive.RoundedProgram
