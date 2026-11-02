import CurrentAdditive.V38UniformSmallBlockAdapter
import Paper2.RestorationBridge

/-! The inherited defect induction needs three two-copy lower bounds.
The current two-threshold *one-copy* profile supplies those bounds directly:
two-block high, two-block low, and a projected single copy respectively.
No third one-copy profile threshold is introduced. -/

namespace CurrentAdditive.V39TwoCopyBundleFin2

open Paper2 Workspace.Types.CommComplexity Workspace.Types.Interlace
open Paper2.V38UniformSmallBlockAdapter

variable {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

private theorem family_lower (F : X → Y → Bool) (p d : ℕ) (x z : ℝ)
    (hx : x ≤ 1) (hz : z ≤ 1)
    (h : ∀ (R : Finset (Fin p × X)) (K : Finset (Fin p → Y)),
      (R,K) ∈ NPCC.bracketGE X Y p x z →
      d ≤ D (NPCC.subgame (interlaceFun F p) R K)) :
    d ≤ ClassicalRows.restrictionCost F p x z := by
  classical
  have hne : {a : ℕ | ∃ RC ∈ NPCC.bracketGE X Y p x z,
      a=D (NPCC.subgame (interlaceFun F p) RC.1 RC.2)}.Nonempty := by
    obtain ⟨RC,hRC⟩ := NPCC.bracketGE.nonempty (X := X) (Y := Y) p x z hx hz Fintype.card_pos
    exact ⟨_,RC,hRC,rfl⟩
  obtain ⟨RC,hRC,heq⟩ := Nat.sInf_mem hne
  change d ≤ sInf {a : ℕ | ∃ RC ∈ NPCC.bracketGE X Y p x z,
    a=D (NPCC.subgame (interlaceFun F p) RC.1 RC.2)}
  rw [heq]
  exact h RC.1 RC.2 hRC

theorem two_copy_input (F : X → Y → Bool) (C : ℕ) (hC : 3 ≤ C)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1/4)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F
      (FiniteLaw.uniform X) (FiniteLaw.uniform Y) θ ((C : ℤ)-1)) :
    EthBridge.TwoCopyBundle F C θ (3/5) := by
  classical
  have hp' : V38RestrictionProfiles.TwoThresholdProfile F
      (FiniteLaw.uniform X) (FiniteLaw.uniform Y) θ ((C-1 : ℕ) : ℤ) := by
    simpa only [Nat.cast_sub (by omega : 1 ≤ C),Nat.cast_one] using hp
  have ht : C ≤ ClassicalRows.restrictionCost F 2 (2*θ) (9/25) := by
    apply family_lower F 2 C (2*θ) (9/25) (by linarith) (by norm_num)
    intro R K hmem
    exact two_block_C_of_profile F C θ hC hθ hp R K hmem
  have hm : C-1 ≤ ClassicalRows.restrictionCost F 2 (2*θ) (9/50) := by
    apply family_lower F 2 (C-1) (2*θ) (9/50) (by linarith) (by norm_num)
    intro R K hmem
    obtain ⟨hrow,hcol⟩ := bracket_to_uniform_mass 2 (2*θ) (9/50) R K hmem
    have h := V38SmallBlocks.two_block_low F (FiniteLaw.uniform X) (FiniteLaw.uniform Y)
      θ (C-1) (by omega) hθ hp' (R : Set _) (K : Set _) hrow hcol
    rwa [finite_restrictionD_eq] at h
  have hb : C-2 ≤ ClassicalRows.restrictionCost F 2 (2*θ) (9/100) := by
    apply family_lower F 2 (C-2) (2*θ) (9/100) (by linarith) (by norm_num)
    intro R K hmem
    obtain ⟨hrow,hcol⟩ := bracket_to_uniform_mass 2 (2*θ) (9/100) R K hmem
    obtain ⟨i,hi⟩ := V38SmallBlocks.exists_large_pair_coordinate
      (FiniteLaw.uniform Y) (K : Set (Fin 2 → Y)) (3/10) (by norm_num at *; exact hcol)
    have h := V38SmallBlocks.singleton_profile_bound F
      (FiniteLaw.uniform X) (FiniteLaw.uniform Y) 2 θ ((C : ℤ)-1) hp
      (R : Set _) (K : Set _) i (by
        have hh := hrow i
        simp only [Finset.mem_coe]
        linarith)
      (⟨1,by omega⟩ : Fin 2) (by convert hi using 1 <;> norm_num)
    rw [finite_restrictionD_eq] at h
    change ((C : ℤ)-1)-1 ≤ (D (NPCC.subgame (interlaceFun F 2) R K) : ℤ) at h
    have hh : (C-2 : ℕ) ≤ D (NPCC.subgame (interlaceFun F 2) R K) := by omega
    exact hh
  change C ≤ ClassicalRows.lambda F 2 (2*θ) ((3/5 : ℝ)^2)
  apply (ClassicalRows.le_lambda_iff F 2 C (2*θ) ((3/5 : ℝ)^2)).mpr
  norm_num only [show ((3/5 : ℝ)^2)=(9/25 : ℝ) by norm_num,
    show ((9/25 : ℝ)/2)=(9/50 : ℝ) by norm_num,
    show ((9/25 : ℝ)/4)=(9/100 : ℝ) by norm_num]
  exact ⟨ht,by omega,by omega⟩

#print axioms two_copy_input

end CurrentAdditive.V39TwoCopyBundleFin2
