import CurrentAdditive.QuarticCheckBit
import CurrentAdditive.QuarticLayout

/-! Lift the exact v27 check controller to the shared front/master layout.
The numeric preparer need only expose two unary count cells in the scratch
region; the remaining scratch cells may contain arbitrary words. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.CurrentAdditive.QuarticCheckLayout

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticCheckBit

variable (FS : Type) [Fintype FS] [DecidableEq FS]

noncomputable def scratchCell (z : FS) : Fin (Lift.a FS + 3) := Lift.ιFS FS z

theorem scratch_ne_scratch {x y : FS} (h : x ≠ y) :
    scratchCell FS x ≠ scratchCell FS y := (Lift.ιFS FS).injective.ne h

theorem scratch_ne_flag (x : FS) : scratchCell FS x ≠ Lift.flag₁ FS := by
  intro h
  have h' := Lift.pos_injective FS h
  cases h'

theorem flag_ne_scratch (x : FS) : Lift.flag₁ FS ≠ scratchCell FS x :=
  (scratch_ne_flag FS x).symm

@[simp] theorem pos_eq_iff (x y : Lift.W FS ⊕ Fin 3) :
    Lift.pos FS x = Lift.pos FS y ↔ x = y := (Lift.pos_injective FS).eq_iff

noncomputable def checkProgLayout27 (A B : FS) (Δ : ℕ) (γ : ℚ) :=
  checkProg27 (scratchCell FS A) (scratchCell FS B) (Lift.flag₁ FS) Δ γ

theorem scratch_value (P : Fin 3 → List Bool) (st : SuccessOrient.Stack → List Bool)
    (c : Fin 3 → List Bool) (Z : FS → List Bool) (x : FS) :
    Lift.layoutBank FS P (Lift.region FS st c Z) (scratchCell FS x) = Z x := by
  simp [scratchCell, Lift.ιFS, Lift.layoutBank_inl, Lift.region]

theorem flag_value (P : Fin 3 → List Bool) (st : SuccessOrient.Stack → List Bool)
    (c : Fin 3 → List Bool) (Z : FS → List Bool) :
    Lift.layoutBank FS P (Lift.region FS st c Z) (Lift.flag₁ FS) = c 0 := by
  simp [Lift.flag₁, Lift.layoutBank_inl, Lift.region]

theorem check_layout_run27 (A B : FS) (hAB : A ≠ B)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ)
    (P : Fin 3 → List Bool) (st : SuccessOrient.Stack → List Bool)
    (Z : FS → List Bool)
    (hA : Z A = List.replicate g.vertices true)
    (hB : Z B = List.replicate g.edges.length true) :
    ∃ (w : CheckBit.DV (NA27 Δ γ) (NB27 Δ γ)) (bit : Bool)
      (Z' : FS → List Bool),
      ((advance (checkProgLayout27 FS A B Δ γ))^[g.vertices + g.edges.length + 2])
        (⟨some .rdA, CheckBit.ctl0 (NA27 Δ γ) (NB27 Δ γ),
          Lift.layoutBank FS P (Lift.region FS st ![[], [], []] Z)⟩ :
          TM2.Cfg (fun _ : Fin (Lift.a FS + 3) => Bool) CheckBit.DL
            (CheckBit.DV (NA27 Δ γ) (NB27 Δ γ))) =
        ⟨none, w, Lift.layoutBank FS P (Lift.region FS st ![[bit], [], []] Z')⟩ ∧
      (bit = true ↔ CurrentAdditive.QuarticSchedule.Checks27
        (V := Fin g.vertices) (Edges := Fin g.edges.length)
        (Nat.clog 2 g.vertices) Δ γ) := by
  let S := Lift.layoutBank FS P (Lift.region FS st ![[], [], []] Z)
  have hvA : S (scratchCell FS A) = List.replicate g.vertices true := by
    simpa [S] using (scratch_value FS P st ![[], [], []] Z A).trans hA
  have hvB : S (scratchCell FS B) = List.replicate g.edges.length true := by
    simpa [S] using (scratch_value FS P st ![[], [], []] Z B).trans hB
  obtain ⟨w, bit, hr, hbit⟩ := check_run27 (scratchCell FS A) (scratchCell FS B)
    (Lift.flag₁ FS) (scratch_ne_scratch FS hAB) (scratch_ne_flag FS A)
    (scratch_ne_flag FS B) Δ γ hγ hΔ g hg hn hinc hdeg S hvA hvB
  let S' := Function.update
    (Function.update (Function.update S (scratchCell FS A) []) (scratchCell FS B) [])
    (Lift.flag₁ FS) (bit :: S (Lift.flag₁ FS))
  let Z' : FS → List Bool := fun z => S' (scratchCell FS z)
  have hbank : S' = Lift.layoutBank FS P (Lift.region FS st ![[bit], [], []] Z') := by
    apply Lift.bank_ext FS
    intro x
    rcases x with (i | x | x | x | x | x | z) | i
    · fin_cases i <;>
        simp [S', S, Lift.layoutBank_inl, Lift.region, Lift.flag₁,
          scratchCell, Lift.ιFS, Function.update, pos_eq_iff]
    · simp [S', S, Lift.layoutBank_inl, Lift.region, Lift.flag₁,
        scratchCell, Lift.ιFS, Function.update, pos_eq_iff]
    · simp [S', S, Lift.layoutBank_inl, Lift.region, Lift.flag₁,
        scratchCell, Lift.ιFS, Function.update, pos_eq_iff]
    · simp [S', S, Lift.layoutBank_inl, Lift.region, Lift.flag₁,
        scratchCell, Lift.ιFS, Function.update, pos_eq_iff]
    · simp [S', S, Lift.layoutBank_inl, Lift.region, Lift.flag₁,
        scratchCell, Lift.ιFS, Function.update, pos_eq_iff]
    · simp [S', S, Lift.layoutBank_inl, Lift.region, Lift.flag₁,
        scratchCell, Lift.ιFS, Function.update, pos_eq_iff]
    · rw [Lift.layoutBank_inl]
      change S' (scratchCell FS z) = Z' z
      rfl
    · simp [S', S, Lift.layoutBank_inr, Lift.flag₁,
        scratchCell, Lift.ιFS, Function.update, pos_eq_iff]
  refine ⟨w, bit, Z', ?_, hbit⟩
  simpa only [checkProgLayout27, S', hbank] using hr

#print axioms check_layout_run27

end Paper2.CurrentAdditive.QuarticCheckLayout
