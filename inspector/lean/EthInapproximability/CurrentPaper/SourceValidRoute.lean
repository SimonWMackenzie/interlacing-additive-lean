import EthInapproximability.CurrentPaper.SourceValidCombined

namespace EthInapproximability.CurrentPaper.SourceValidAcceptance

open Turing BitMachineEncoding
open scoped Classical

theorem positive_route_unique (a q : Nat) (input : List Bool)
    (t₁ t₂ : Nat) (v₁ v₂ : SourceCSPGuardOutputCombined.PrefixControl)
    (S₁ S₂ : SourceCSPInputFrame.Stack → List Bool)
    (hr₁ : ((advance (SourceCSPGuardOutputCombined.program a q))^[t₁])
      (SourceCSPGuardOutputCombined.initial a q input) =
        ⟨some .route, (v₁, none), S₁⟩)
    (hv₁ : v₁.2.2 = some .positive)
    (hr₂ : ((advance (SourceCSPGuardOutputCombined.program a q))^[t₂])
      (SourceCSPGuardOutputCombined.initial a q input) =
        ⟨some .route, (v₂, none), S₂⟩) :
    v₂.2.2 = some .positive := by
  let M := SourceCSPGuardOutputCombined.program a q
  let c := SourceCSPGuardOutputCombined.initial a q input
  have hpos : ((advance M)^[t₁ + 2]) c =
      ⟨none, (v₁, none), S₁⟩ := by
    rw [show t₁ + 2 = 2 + t₁ by omega,
      Function.iterate_add_apply, hr₁]
    exact SourceCSPGuardOutputCombined.route_positive a q v₁ S₁ hv₁
  cases hv₂ : v₂.2.2 with
  | none =>
      have hnone : SourceCSPGuardOutputCombined.routeRun a q 2 v₂ S₂ =
          ⟨none, (v₂, none), S₂⟩ := by
        simp [SourceCSPGuardOutputCombined.routeRun,
          Function.iterate_succ_apply', advance, TM2.step, TM2.stepAux,
          SourceCSPGuardOutputCombined.program, hv₂]
      have hlast : ((advance M)^[t₂ + 2]) c =
          ⟨none, (v₂, none), S₂⟩ := by
        rw [show t₂ + 2 = 2 + t₂ by omega,
          Function.iterate_add_apply, hr₂]
        exact hnone
      have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique
        M c (t₁ + 2) (t₂ + 2) (by rw [hpos]) (by rw [hlast])
      have hv := congrArg (fun x => x.var.1.2.2) heq
      rw [hpos, hlast] at hv
      simp only at hv
      exact False.elim (by rw [hv₁, hv₂] at hv; cases hv)
  | some tag =>
      cases tag with
      | positive => rfl
      | reject =>
          obtain ⟨tr, T, _, hroute, _, _⟩ :=
            SourceCSPGuardOutputCombined.route_reject a q v₂ S₂ hv₂
          have hlast : ((advance M)^[t₂ + tr]) c =
              ⟨none, (SourceCSPGuardOutputCombined.rejectControl, none), T⟩ := by
            rw [show t₂ + tr = tr + t₂ by omega,
              Function.iterate_add_apply, hr₂]
            exact hroute
          have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique
            M c (t₁ + 2) (t₂ + tr) (by rw [hpos]) (by rw [hlast])
          have hv := congrArg (fun x => x.var.1.2.2) heq
          rw [hpos, hlast] at hv
          simp [SourceCSPGuardOutputCombined.rejectControl, hv₁] at hv
      | zero =>
          obtain ⟨tr, T, _, hroute, _, _⟩ :=
            SourceCSPGuardOutputCombined.route_zero a q v₂ S₂ hv₂
          have hlast : ((advance M)^[t₂ + tr]) c =
              ⟨none, (SourceCSPGuardOutputCombined.zeroControl, none), T⟩ := by
            rw [show t₂ + tr = tr + t₂ by omega,
              Function.iterate_add_apply, hr₂]
            exact hroute
          have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique
            M c (t₁ + 2) (t₂ + tr) (by rw [hpos]) (by rw [hlast])
          have hv := congrArg (fun x => x.var.1.2.2) heq
          rw [hpos, hlast] at hv
          simp [SourceCSPGuardOutputCombined.zeroControl, hv₁] at hv

theorem raw_positive_route {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hn : 0 < P.vertices) :
    ∃ tp v Sp,
      tp ≤ SourceCSPGuardDispatchSequence.bound a q
        (EncodedETHSource.constraintBits P).length ∧
      ((advance (SourceCSPGuardOutputCombined.program a q))^[tp])
        (SourceCSPGuardOutputCombined.initial a q
          (EncodedETHSource.constraintBits P)) =
        (⟨some .route, (v, none), Sp⟩ :
          TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool) _ _) ∧
      v.2.2 = some .positive := by
  obtain ⟨t₁, v₁, S₁, ht₁, hr₁, hv₁⟩ := combined_positive P hn
  obtain ⟨t₂, v₂, S₂, ht₂, hr₂, _⟩ :=
    SourceCSPGlobalPositiveLiteral.positive_literal a q
      (EncodedETHSource.constraintBits P)
  exact ⟨t₂, v₂, S₂, ht₂, hr₂,
    positive_route_unique a q (EncodedETHSource.constraintBits P)
      t₁ t₂ v₁ v₂ S₁ S₂ hr₁ hv₁ hr₂⟩

#print axioms positive_route_unique
#print axioms raw_positive_route

end EthInapproximability.CurrentPaper.SourceValidAcceptance
