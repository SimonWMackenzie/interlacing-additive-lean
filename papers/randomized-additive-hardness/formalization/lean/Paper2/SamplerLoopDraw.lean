import Paper2.SamplerDrawCount
import EthInapproximability.CurrentPaper.BitMachineInline

/-! One fixed Fin 32 controller: the unary-fuel affine loop, a one-step
dispatch on the physical terminal parity held in finite control, and the
physical draw-count writer for that parity. The loop theorem is restated
with an explicit frame (every cell other than the fuel and the two row/column
pairs is unchanged), which the checked `SamplerAffineLoop.run_fuel` does not
export. No parity, pair value, or draw count is supplied to the bank. -/

set_option maxHeartbeats 4000000

namespace Paper2.SamplerLoopDraw

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := Fin 32

/-- Cells a loop run may change: the fuel and both row/column pairs. -/
def Moving (j : Stack) : Prop := j = 6 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16

theorem afterRound_frame (b : Bool) (S : Stack → List Bool) (r c : Nat)
    (j : Stack) (hj : ¬ Moving j) :
    SamplerAffineRound.afterRound b S r c j = S j := by
  have h1 : j ≠ SamplerAffineRound.row (!b) := by
    intro h
    apply hj
    cases b <;> simp [SamplerAffineRound.row] at h <;> simp [Moving, h]
  have h2 : j ≠ SamplerAffineRound.col (!b) := by
    intro h
    apply hj
    cases b <;> simp [SamplerAffineRound.col] at h <;> simp [Moving, h]
  simp only [SamplerAffineRound.afterRound, SamplerAffineRound.afterRow,
    SamplerAffineRound.afterClear, Function.update_of_ne h1,
    Function.update_of_ne h2]

/-- `SamplerAffineLoop.run_fuel` with the explicit frame of unchanged cells. -/
theorem run_fuel_frame (k : Nat) (b : Bool) (S : Stack → List Bool)
    (A B C D r c u v : Nat)
    (h : SamplerAffineRound.Invariant b S A B C D r c u v)
    (hfuel : S 6 = List.replicate k true) :
    ∃ (t : Nat) (T : Stack → List Bool) (b' : Bool) (u' v' : Nat),
      t ≤ SamplerAffineLoop.loopCap A B C D k r c u v ∧
      ((advance SamplerAffineLoop.program)^[t])
        (⟨some (.check b), SamplerAffineLoop.startControl, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) SamplerAffineLoop.Label
            SamplerAffineLoop.Control) =
        ⟨none, SamplerAffineLoop.endControl b', T⟩ ∧
      SamplerAffineRound.Invariant b' T A B C D
        (SamplerAffineLoop.values A B C D k r c).1
        (SamplerAffineLoop.values A B C D k r c).2 u' v' ∧
      T 6 = [] ∧
      (∀ j : Stack, ¬ Moving j → T j = S j) := by
  induction k generalizing b S r c u v with
  | zero =>
      refine ⟨1, S, b, u, v, by rfl, ?_, ?_, ?_, fun _ _ => rfl⟩
      · simpa only [Function.iterate_one] using
          SamplerAffineLoop.check_empty b S hfuel
      · exact h
      · exact hfuel
  | succ k ih =>
      let S₁ := Function.update S 6 (List.replicate k true)
      let r₁ := A+B*c
      let c₁ := C+D*r
      let S₂ := SamplerAffineRound.afterRound b S₁ r₁ c₁
      have hcheck := SamplerAffineLoop.check_nonempty b S k hfuel
      have hInv₁ : SamplerAffineRound.Invariant b S₁ A B C D r c u v :=
        SamplerAffineLoop.fuel_update_invariant b S A B C D r c u v h _
      obtain ⟨tr, htr, hr⟩ :=
        SamplerAffineLoop.round_inline b S₁ A B C D r c u v hInv₁
      have hInv₂ : SamplerAffineRound.Invariant (!b) S₂ A B C D
          r₁ c₁ r c := by
        simpa only [S₂, r₁, c₁] using
          SamplerAffineRound.round_invariant b S₁ A B C D r c u v hInv₁
      have hfuel₂ : S₂ 6 = List.replicate k true := by
        change (SamplerAffineRound.afterRound b S₁ r₁ c₁) 6 = _
        rw [SamplerAffineRound.round_fuel]
        exact Function.update_self ..
      have hframe₂ : ∀ j : Stack, ¬ Moving j → S₂ j = S j := by
        intro j hj
        have h6 : j ≠ 6 := fun he => hj (Or.inl he)
        change SamplerAffineRound.afterRound b S₁ r₁ c₁ j = S j
        rw [afterRound_frame b S₁ r₁ c₁ j hj]
        simp only [S₁, Function.update_of_ne h6]
      obtain ⟨tt, T, b', u', v', htt, htail, hInvFinal, hFuelFinal,
          hFrameFinal⟩ := ih (!b) S₂ r₁ c₁ r c hInv₂ hfuel₂
      have hprefix :
          ((advance SamplerAffineLoop.program)^[1+tr])
            (⟨some (.check b), SamplerAffineLoop.startControl, S⟩ :
              TM2.Cfg (fun _ : Stack => Bool) SamplerAffineLoop.Label
                SamplerAffineLoop.Control) =
          ⟨some (.check (!b)), SamplerAffineLoop.startControl, S₂⟩ := by
        rw [show 1+tr = tr+1 by omega, Function.iterate_add_apply]
        simpa only [Function.iterate_one, S₁, S₂, r₁, c₁, hcheck] using hr
      refine ⟨1+tr+tt, T, b', u', v', ?_, ?_, ?_, hFuelFinal, ?_⟩
      · change 1+tr+tt ≤ 1 + SamplerAffineLoop.roundCap A B C D r c u v +
          SamplerAffineLoop.loopCap A B C D k r₁ c₁ r c
        have hrCap : tr ≤ SamplerAffineLoop.roundCap A B C D r c u v := htr
        omega
      · rw [show 1+tr+tt = tt+(1+tr) by omega,
          Function.iterate_add_apply, hprefix]
        exact htail
      · simpa only [SamplerAffineLoop.values, r₁, c₁] using hInvFinal
      · intro j hj
        rw [hFrameFinal j hj, hframe₂ j hj]

/-! ## Loop, parity dispatch, draw count -/

inductive Label where
  | loop (l : SamplerAffineLoop.Label)
  | dispatch
  | draw (b : Bool) (l : SamplerDrawCount.Label)

abbrev Control := SamplerAffineLoop.Control × SamplerDrawCount.Control

def drawStart : SamplerDrawCount.Label :=
  .inl (.inl (0 : SourceClauseFixedUnary.Label 1))
def drawControl : SamplerDrawCount.Control := (((),false),false)

/-- The dispatch reads only the parity bit stored in finite control. -/
def dispatchLabel (v : Control) : Label :=
  match v.1.2 with
  | some true => .draw true drawStart
  | _ => .draw false drawStart

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .loop l => BitMachineInline.stmt Label.loop (fun v => (v, drawControl))
      Prod.fst (some .dispatch) (SamplerAffineLoop.program l)
  | .dispatch => .goto dispatchLabel
  | .draw b l => BitMachineInline.stmt (Label.draw b)
      (fun w => (SamplerAffineLoop.endControl b, w)) Prod.snd none
      (SamplerDrawCount.program b l)

def startLabel (b : Bool) : Label := .loop (.check b)
def startControl : Control := (SamplerAffineLoop.startControl, drawControl)

theorem dispatch_step (b : Bool) (S : Stack → List Bool) :
    advance program
      (⟨some .dispatch, (SamplerAffineLoop.endControl b, drawControl), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some (.draw b drawStart), (SamplerAffineLoop.endControl b, drawControl),
        S⟩ := by
  cases b <;> rfl

def drawTime (r c mX mY : Nat) : Nat :=
  2 + MatrixAddressMachine.exactTime c mY 1 +
    MatrixAddressMachine.exactTime r mX 0 + 2

/-- Whole run from an arbitrary loop-invariant bank. The terminal parity is
read from finite control; the final bank is the checked draw-count bank over
the actual loop bank `T`, whose frame and invariant are exported. -/
theorem run (k : Nat) (b : Bool) (S : Stack → List Bool)
    (A B C D r c u v mX mY : Nat)
    (h : SamplerAffineRound.Invariant b S A B C D r c u v)
    (hfuel : S 6 = List.replicate k true)
    (hmX : S 7 = List.replicate mX true)
    (hmY : S 8 = List.replicate mY true)
    (h20 : S 20 = []) (h21 : S 21 = []) (h22 : S 22 = []) :
    ∃ (t : Nat) (T : Stack → List Bool) (b' : Bool) (u' v' : Nat),
      t ≤ SamplerAffineLoop.loopCap A B C D k r c u v + 1 +
        drawTime (SamplerAffineLoop.values A B C D k r c).1
          (SamplerAffineLoop.values A B C D k r c).2 mX mY ∧
      ((advance program)^[t])
        (⟨some (startLabel b), startControl, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none, (SamplerAffineLoop.endControl b', drawControl),
          SamplerDrawCount.finalBank T mY mX
            (SamplerAffineLoop.values A B C D k r c).2
            (SamplerAffineLoop.values A B C D k r c).1⟩ ∧
      SamplerAffineRound.Invariant b' T A B C D
        (SamplerAffineLoop.values A B C D k r c).1
        (SamplerAffineLoop.values A B C D k r c).2 u' v' ∧
      T 6 = [] ∧
      (∀ j : Stack, ¬ Moving j → T j = S j) := by
  obtain ⟨tl, T, b', u', v', htl, hloop, hInv, hT6, hframe⟩ :=
    run_fuel_frame k b S A B C D r c u v h hfuel
  let rk := (SamplerAffineLoop.values A B C D k r c).1
  let ck := (SamplerAffineLoop.values A B C D k r c).2
  have hhalt : (((advance SamplerAffineLoop.program)^[tl])
      (⟨some (.check b), SamplerAffineLoop.startControl, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) SamplerAffineLoop.Label
          SamplerAffineLoop.Control)).l = none := by
    rw [hloop]
  obtain ⟨n₁, hn₁, hr₁⟩ := BitMachineInline.outputs
    Label.loop (fun v => (v, drawControl)) Prod.fst (fun _ => rfl)
    (some Label.dispatch) SamplerAffineLoop.program program (fun _ => rfl)
    (⟨some (.check b), SamplerAffineLoop.startControl, S⟩ :
      TM2.Cfg (fun _ : Stack => Bool) SamplerAffineLoop.Label
        SamplerAffineLoop.Control) tl hhalt
  rw [hloop] at hr₁
  have hr₁' : ((advance program)^[n₁])
      (⟨some (startLabel b), startControl, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨some .dispatch, (SamplerAffineLoop.endControl b', drawControl), T⟩ := by
    simpa only [BitMachineInline.cfg, startLabel, startControl] using hr₁
  have hT7 : T 7 = List.replicate mX true := by
    rw [hframe 7 (by simp [Moving])]; exact hmX
  have hT8 : T 8 = List.replicate mY true := by
    rw [hframe 8 (by simp [Moving])]; exact hmY
  have hT20 : T 20 = [] := by
    rw [hframe 20 (by simp [Moving])]; exact h20
  have hT21 : T 21 = [] := by
    rw [hframe 21 (by simp [Moving])]; exact h21
  have hT22 : T 22 = [] := by
    rw [hframe 22 (by simp [Moving])]; exact h22
  obtain ⟨td, htd, hdraw⟩ := SamplerDrawCount.run b' T mY mX ck rk
    hInv.activeCol hInv.activeRow hT8 hT7 hInv.work17 hInv.work18
    hT20 hT21 hT22
  have hdhalt : (((advance (SamplerDrawCount.program b'))^[td])
      (⟨some drawStart, drawControl, T⟩ :
        TM2.Cfg (fun _ : Stack => Bool) SamplerDrawCount.Label
          SamplerDrawCount.Control)).l = none := by
    change (((advance (SamplerDrawCount.program b'))^[td])
      (⟨some (.inl (.inl (0 : SourceClauseFixedUnary.Label 1))),
        (((),false),false), T⟩ :
        TM2.Cfg (fun _ : Stack => Bool) SamplerDrawCount.Label
          SamplerDrawCount.Control)).l = none
    rw [hdraw]
  obtain ⟨n₂, hn₂, hr₂⟩ := BitMachineInline.outputs
    (Label.draw b') (fun w => (SamplerAffineLoop.endControl b', w)) Prod.snd
    (fun _ => rfl) none (SamplerDrawCount.program b') program (fun _ => rfl)
    (⟨some drawStart, drawControl, T⟩ :
      TM2.Cfg (fun _ : Stack => Bool) SamplerDrawCount.Label
        SamplerDrawCount.Control) td hdhalt
  have hdraw' : ((advance (SamplerDrawCount.program b'))^[td])
      (⟨some drawStart, drawControl, T⟩ :
        TM2.Cfg (fun _ : Stack => Bool) SamplerDrawCount.Label
          SamplerDrawCount.Control) =
      ⟨none, drawControl, SamplerDrawCount.finalBank T mY mX ck rk⟩ := hdraw
  rw [hdraw'] at hr₂
  have hr₂' : ((advance program)^[n₂])
      (⟨some (.draw b' drawStart), (SamplerAffineLoop.endControl b', drawControl),
        T⟩ : TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none, (SamplerAffineLoop.endControl b', drawControl),
        SamplerDrawCount.finalBank T mY mX ck rk⟩ := by
    simpa only [BitMachineInline.cfg] using hr₂
  refine ⟨n₁ + 1 + n₂, T, b', u', v', ?_, ?_, hInv, hT6, hframe⟩
  · have htd' : td ≤ 2 + MatrixAddressMachine.exactTime
        (SamplerAffineLoop.values A B C D k r c).2 mY 1 +
        MatrixAddressMachine.exactTime
          (SamplerAffineLoop.values A B C D k r c).1 mX 0 + 2 := htd
    simp only [drawTime]
    omega
  · rw [show n₁ + 1 + n₂ = n₂ + (1 + n₁) by omega,
      Function.iterate_add_apply, Function.iterate_add_apply,
      hr₁', Function.iterate_one, dispatch_step]
    exact hr₂'

#print axioms afterRound_frame
#print axioms run_fuel_frame
#print axioms dispatch_step
#print axioms run

end Paper2.SamplerLoopDraw
