import Paper2.SamplerAffineRound
import EthInapproximability.CurrentPaper.BitMachineInline

set_option maxHeartbeats 5000000

namespace Paper2.SamplerAffineLoop

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := SamplerAffineRound.Stack

inductive Label where
  | check (b : Bool)
  | work (b : Bool) (l : SamplerAffineRound.Label)
  deriving DecidableEq, Fintype

abbrev Control := SamplerAffineRound.Control × Option Bool

def startControl : Control := (SamplerAffineRound.initialControl, none)
def endControl (b : Bool) : Control :=
  (SamplerAffineRound.initialControl, some b)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .check b =>
      .pop 6 (fun v bit => (v.1, bit))
        (.branch (fun v => v.2.isSome)
          (.load (fun _ => startControl)
            (.goto (fun _ => .work b SamplerAffineRound.initialLabel)))
          (.load (fun _ => endControl b) .halt))
  | .work b l =>
      BitMachineInline.stmt (Label.work b)
        (fun v => (v, none)) Prod.fst
        (some (.check (!b))) (SamplerAffineRound.program b l)

theorem check_nonempty (b : Bool) (S : Stack → List Bool) (k : Nat)
    (hfuel : S 6 = List.replicate (k+1) true) :
    advance program
      (⟨some (.check b), startControl, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (.work b SamplerAffineRound.initialLabel), startControl,
        Function.update S 6 (List.replicate k true)⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program,
    startControl, hfuel, List.replicate_succ]

theorem check_empty (b : Bool) (S : Stack → List Bool)
    (hfuel : S 6 = []) :
    advance program
      (⟨some (.check b), startControl, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none, endControl b, S⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program,
    startControl, endControl, hfuel]

theorem round_inline (b : Bool) (S : Stack → List Bool)
    (A B C D r c u v : Nat)
    (h : SamplerAffineRound.Invariant b S A B C D r c u v) :
    ∃ t ≤ u + v + 3 +
      MatrixAddressMachine.exactTime c B A +
      MatrixAddressMachine.exactTime r D C + 2,
      ((advance program)^[t])
        (⟨some (.work b SamplerAffineRound.initialLabel), startControl, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (.check (!b)), startControl,
        SamplerAffineRound.afterRound b S (A+B*c) (C+D*r)⟩ := by
  obtain ⟨tr, htr, hr⟩ :=
    SamplerAffineRound.round_run_inv b S A B C D r c u v h
  have hhalt :
      (((advance (SamplerAffineRound.program b))^[tr])
        (⟨some SamplerAffineRound.initialLabel,
          SamplerAffineRound.initialControl, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            SamplerAffineRound.Label SamplerAffineRound.Control)).l = none := by
    rw [hr]
  obtain ⟨t, ht, hrun⟩ := BitMachineInline.outputs
    (Label.work b) (fun v => (v, none)) Prod.fst
    (by intro v; rfl) (some (.check (!b)))
    (SamplerAffineRound.program b) program (by intro l; rfl)
    (⟨some SamplerAffineRound.initialLabel,
      SamplerAffineRound.initialControl, S⟩) tr hhalt
  rw [hr] at hrun
  refine ⟨t, ht.trans htr, ?_⟩
  simpa only [BitMachineInline.cfg, startControl] using hrun

theorem fuel_update_invariant (b : Bool) (S : Stack → List Bool)
    (A B C D r c u v : Nat)
    (h : SamplerAffineRound.Invariant b S A B C D r c u v)
    (fuel : List Bool) :
    SamplerAffineRound.Invariant b (Function.update S 6 fuel)
      A B C D r c u v := by
  cases b <;>
    constructor <;>
    simp [SamplerAffineRound.row, SamplerAffineRound.col,
      h.coeffA, h.coeffB, h.coeffC, h.coeffD,
      h.work17, h.work18] <;>
    first
    | simpa [SamplerAffineRound.row, SamplerAffineRound.col] using h.activeRow
    | simpa [SamplerAffineRound.row, SamplerAffineRound.col] using h.activeCol
    | simpa [SamplerAffineRound.row, SamplerAffineRound.col] using h.inactiveRow
    | simpa [SamplerAffineRound.row, SamplerAffineRound.col] using h.inactiveCol

def values (A B C D : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, r, c => (r,c)
  | k+1, r, c => values A B C D k (A+B*c) (C+D*r)

def roundCap (A B C D r c u v : Nat) : Nat :=
  u + v + 3 + MatrixAddressMachine.exactTime c B A +
    MatrixAddressMachine.exactTime r D C + 2

def loopCap (A B C D : Nat) : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, _ => 1
  | k+1, r, c, u, v =>
      1 + roundCap A B C D r c u v +
        loopCap A B C D k (A+B*c) (C+D*r) r c

theorem run_fuel (k : Nat) (b : Bool) (S : Stack → List Bool)
    (A B C D r c u v : Nat)
    (h : SamplerAffineRound.Invariant b S A B C D r c u v)
    (hfuel : S 6 = List.replicate k true) :
    ∃ (t : Nat) (T : Stack → List Bool) (b' : Bool) (u' v' : Nat),
      t ≤ loopCap A B C D k r c u v ∧
      ((advance program)^[t])
        (⟨some (.check b), startControl, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none, endControl b', T⟩ ∧
      SamplerAffineRound.Invariant b' T A B C D
        (values A B C D k r c).1
        (values A B C D k r c).2 u' v' ∧
      T 6 = [] := by
  induction k generalizing b S r c u v with
  | zero =>
      refine ⟨1, S, b, u, v, by rfl, ?_, ?_, ?_⟩
      · simpa only [Function.iterate_one] using check_empty b S hfuel
      · exact h
      · exact hfuel
  | succ k ih =>
      let S₁ := Function.update S 6 (List.replicate k true)
      let r₁ := A+B*c
      let c₁ := C+D*r
      let S₂ := SamplerAffineRound.afterRound b S₁ r₁ c₁
      have hcheck := check_nonempty b S k hfuel
      have hInv₁ : SamplerAffineRound.Invariant b S₁ A B C D r c u v :=
        fuel_update_invariant b S A B C D r c u v h _
      obtain ⟨tr, htr, hr⟩ := round_inline b S₁ A B C D r c u v hInv₁
      have hInv₂ : SamplerAffineRound.Invariant (!b) S₂ A B C D
          r₁ c₁ r c := by
        simpa only [S₂, r₁, c₁] using
          SamplerAffineRound.round_invariant b S₁ A B C D r c u v hInv₁
      have hfuel₂ : S₂ 6 = List.replicate k true := by
        change (SamplerAffineRound.afterRound b S₁ r₁ c₁) 6 = _
        rw [SamplerAffineRound.round_fuel]
        exact Function.update_self ..
      obtain ⟨tt, T, b', u', v', htt, htail, hInvFinal, hFuelFinal⟩ :=
        ih (!b) S₂ r₁ c₁ r c hInv₂ hfuel₂
      have hprefix :
          ((advance program)^[1+tr])
            (⟨some (.check b), startControl, S⟩ :
              TM2.Cfg (fun _ : Stack => Bool) Label Control) =
          ⟨some (.check (!b)), startControl, S₂⟩ := by
        rw [show 1+tr = tr+1 by omega,
          Function.iterate_add_apply]
        simpa only [Function.iterate_one, S₁, S₂, r₁, c₁,
          hcheck] using hr
      refine ⟨1+tr+tt, T, b', u', v', ?_, ?_, ?_, hFuelFinal⟩
      · change 1+tr+tt ≤ 1 + roundCap A B C D r c u v +
          loopCap A B C D k r₁ c₁ r c
        have hrCap : tr ≤ roundCap A B C D r c u v := htr
        omega
      · rw [show 1+tr+tt = tt+(1+tr) by omega,
          Function.iterate_add_apply, hprefix]
        exact htail
      · simpa only [values, r₁, c₁] using hInvFinal

#print axioms run_fuel

end Paper2.SamplerAffineLoop
