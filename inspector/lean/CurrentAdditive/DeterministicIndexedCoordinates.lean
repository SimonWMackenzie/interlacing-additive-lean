import CurrentAdditive.DeterministicIndexedProfilePrefix
import Paper2.RestrictionProfiles

/-! Every coordinate projection of the actual indexed source pushes its law
to the target base law. Duplicate indices remain distinct before projection. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2

theorem codeSource_coordinate_pushes
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    {D q : ℕ} (μ : PositiveRationalLaw Y)
    (src : CodeSource D q Y μ) (hD : 1 ≤ D)
    (p : Fin q) :
    src.law.toFiniteLaw.PushesTo μ.toFiniteLaw (fun z => src.decode z p) := by
  classical
  intro E
  let S : Finset (Fin q) := {p}
  let pS : S := ⟨p, by simp [S]⟩
  have hS : S.card ≤ D := by simpa [S] using hD
  have hsource := src.exactLaw S hS (fun f : S → Y => E (f pS))
  have hleft : (fun z : src.Label => E (src.decode z p)) =
      (fun z => E ((fun i : S => src.decode z i) pS)) := rfl
  rw [hleft, hsource]
  have huniq (i : S) : i = pS := by
    rcases i with ⟨i, hi⟩
    apply Subtype.ext
    exact Finset.mem_singleton.mp hi
  have hev : (fun f : S → Y => E (f pS)) =
      (fun f => ∀ i : S, (if i = pS then E (f i) else True)) := by
    funext f
    apply propext
    simp [huniq]
  rw [hev]
  have hpi := Paper2.FiniteLaw.pi_prob_coordinatewise
    (fun _ : S => μ.toFiniteLaw)
    (fun i a => if i = pS then E a else True)
  rw [hpi]
  have huniv : (Finset.univ : Finset S) = {pS} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact huniq i
  change (Finset.univ : Finset S).prod
    (fun i => μ.toFiniteLaw.prob (fun a => if i = pS then E a else True)) =
      μ.toFiniteLaw.prob E
  rw [huniv]
  simp

end CurrentAdditive.DeterministicIndexedMatrix
