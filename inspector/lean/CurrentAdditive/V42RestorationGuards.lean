import CurrentAdditive.V42AlignmentGuards

namespace CurrentAdditive.V42RestorationGuards

open V42Schedule

private theorem cast_le {a b:ℚ} (h:a ≤ b) : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast h

theorem delta_eq (k : ℕ) :
    (eta k:ℝ)/(16*(w k:ℝ))=(deltaU k:ℝ) := by
  have hh := congrArg (fun q:ℚ => (q:ℝ)) (recipe_exact k 0).2.2.2.2.2.2
  push_cast at hh
  exact hh.symm

theorem phi_pos (b : ℕ) : 0 < (rho b:ℝ) := by unfold rho; positivity

theorem phi_le_one (b : ℕ) : (rho b:ℝ) ≤ 1 := by
  rw [cast_rho_dyadic]
  exact V39ExceptionBudget.dyadic_le_one b

theorem delta_pos (k : ℕ) : 0 < (eta k:ℝ)/(16*(w k:ℝ)) := by
  rw [delta_eq]
  unfold deltaU
  positivity

theorem delta_small (k : ℕ) (hk : 1 ≤ k) :
    (eta k:ℝ)/(16*(w k:ℝ)) ≤ 1/64 := by
  rw [delta_eq]
  have hh := reciprocal_le (4+10*k) 6 (by omega)
  have hq : deltaU k ≤ (1:ℚ)/64 := by simpa [deltaU] using hh
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using cast_le hq

theorem restoration_scale (k : ℕ) :
    (Q k:ℝ)*(theta k:ℝ) ≤ 1/20 := by
  have hh : (Q k:ℝ)*(theta k:ℝ)=1/512 := by
    have he := congrArg (fun q:ℚ => (q:ℝ)) (Q_theta k)
    push_cast at he
    exact he
  rw [hh]
  norm_num

theorem generated_width (k : ℕ) (hk : 200 ≤ k) :
    128*((V38Moments.exceptionCount (rho (4*k):ℝ)
      (((eta k:ℝ)/(16*(w k:ℝ)))/2):ℝ)+1) ≤ (Q k:ℝ) := by
  rw [delta_eq]
  exact_mod_cast generated_restoration_count k hk

structure GeneratedGuards (k : ℕ) : Prop where
  alignment : V42AlignmentGuards.Guards k (4*k)
  Q_pow : Q k=2^(24*k)
  phi_pos : 0 < (rho (4*k):ℝ)
  phi_le_one : (rho (4*k):ℝ) ≤ 1
  delta_pos : 0 < (eta k:ℝ)/(16*(w k:ℝ))
  delta_small : (eta k:ℝ)/(16*(w k:ℝ)) ≤ 1/64
  restoration_width : 128*((V38Moments.exceptionCount (rho (4*k):ℝ)
    (((eta k:ℝ)/(16*(w k:ℝ)))/2):ℝ)+1) ≤ (Q k:ℝ)
  restoration_scale : (Q k:ℝ)*(theta k:ℝ) ≤ 1/20

theorem generated_guards (k : ℕ) (hk : 200 ≤ k) : GeneratedGuards k :=
  ⟨V42AlignmentGuards.guards k (4*k) hk (by omega),rfl,phi_pos _,phi_le_one _,
    delta_pos k,delta_small k (by omega),generated_width k hk,restoration_scale k⟩

#print axioms generated_width
#print axioms generated_guards

end CurrentAdditive.V42RestorationGuards
