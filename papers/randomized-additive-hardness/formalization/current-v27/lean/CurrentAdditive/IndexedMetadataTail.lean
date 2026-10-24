import CurrentAdditive.IndexedFlagTail

/-! The literal metadata mixture supplies the template-flag mean in the
incoming-mass tail argument. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2
open scoped BigOperators

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : Sources.InternalStreams src μI w)

def isTemplateFlag : Fin s ⊕ I → Bool
  | .inl _ => true
  | .inr _ => false

private theorem metadata_coordinate_pushes (hD : 1 ≤ D) (p : Fin w)
    (E : (Fin s ⊕ I) → Prop) :
    streams.metadataStream.law.toFiniteLaw.prob
      (fun seed => E (streams.metadataStream.decode seed p)) =
      (metadataLaw μI).toFiniteLaw.prob E := by
  classical
  let S : Finset (Fin w) := {p}
  let pS : S := ⟨p, by simp [S]⟩
  have hS : S.card ≤ D := by simpa [S] using hD
  have hsource := streams.metadataStream.exactLaw S hS
    (fun f : S → Fin s ⊕ I => E (f pS))
  rw [hsource]
  have huniq (i : S) : i = pS := by
    rcases i with ⟨i, hi⟩
    apply Subtype.ext
    exact Finset.mem_singleton.mp hi
  have hev : (fun f : S → Fin s ⊕ I => E (f pS)) =
      (fun f => ∀ i : S, (if i = pS then E (f i) else True)) := by
    funext f
    apply propext
    simp [huniq]
  rw [hev]
  have hpi := FiniteLaw.pi_prob_coordinatewise
    (fun _ : S => (metadataLaw μI).toFiniteLaw)
    (fun i a => if i = pS then E a else True)
  rw [hpi]
  have huniv : (Finset.univ : Finset S) = {pS} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact huniq i
  change (Finset.univ : Finset S).prod
    (fun i => (metadataLaw μI).toFiniteLaw.prob
      (fun a => if i = pS then E a else True)) =
    (metadataLaw μI).toFiniteLaw.prob E
  rw [huniv]
  simp

theorem metadata_template_probability :
    (metadataLaw μI).toFiniteLaw.prob
      (fun a => isTemplateFlag (s := s) a = true) = 255 / 256 := by
  classical
  unfold FiniteLaw.prob PositiveRationalLaw.toFiniteLaw metadataLaw
  rw [Fintype.sum_sum_type]
  have htotal : (∑ i : Fin s,
      ((PositiveRationalLaw.uniform (Fin s)).weight i : ℝ)) = 1 := by
    exact_mod_cast (PositiveRationalLaw.uniform (Fin s)).total
  simp [isTemplateFlag, ← Finset.mul_sum, htotal]

theorem metadata_template_coordinate_mean (hD : 1 ≤ D)
    (i : Fin w) :
    streams.metadataStream.law.toFiniteLaw.prob
      (fun seed => isTemplateFlag
        (streams.metadataStream.decode seed i) = true) = 255 / 256 := by
  calc
    _ = (metadataLaw μI).toFiniteLaw.prob
          (fun a => isTemplateFlag a = true) :=
            metadata_coordinate_pushes src streams hD i _
    _ = _ := metadata_template_probability (μI := μI)

/-- The actual metadata stream's lower-tail bound for any distinct original
outer positions. -/
theorem metadata_half_template_tail (hD : 8*256 ≤ D)
    {m : ℕ} (e : Fin m → Fin w) (he : Function.Injective e) :
    streams.metadataStream.law.toFiniteLaw.prob (fun seed =>
      (∑ i : Fin m,
        if isTemplateFlag (streams.metadataStream.decode seed (e i))
        then (1 : ℝ) else 0) < (m : ℝ) / 2) ≤
      2 * ((64 : ℝ) * m) ^ 128 /
        (((255 / 256 : ℝ) - 1/2) * m) ^ 256 := by
  apply indexed_flag_half_tail streams.metadataStream hD e he
    (isTemplateFlag (s := s)) (255 / 256) (by norm_num)
  intro i
  exact metadata_template_coordinate_mean src streams (by omega) (e i)

#print axioms metadata_template_probability
#print axioms metadata_half_template_tail

end CurrentAdditive.DeterministicIndexedMatrix
