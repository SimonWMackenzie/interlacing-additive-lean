import EthInapproximability.CurrentPaper.BitMachineInline
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-!
# Segment 2 building blocks: two-way dispatch, answer extraction, and a
# growth-bounded charged clear

Lane owner:b-stage4-entry-program-3 (Paper B, unit 2, map item 3).

Generic, fixed-controller pieces that the per-address Stage-4 entry program
needs and that no admitted module provides in this form:

* `program flag A B …`: ONE fixed controller that POPS a physical verdict
  bit from the stack `flag` (charged: one transition) and then runs the
  literally inlined instruction table of `A` (bit `true`) or of `B` (bit
  `false`) on the same bank. `run_left`/`run_right` transport an actual
  bounded run of the chosen branch, with its exact exit bank. No branch
  choice is an input: it is the bit on the stack.
* `moveBit src dst`: one transition moving the top bit of `src` onto `dst`
  (answer extraction into the entry cell).
* `clear_bounded`: the admitted `BitMachineClearBank.clear_bank_run` with a
  uniform time bound `n * B + n + 1` from a per-cell length bound `B`;
  `growth_bound` supplies such a `B` after any bounded run through the
  admitted `BitMachineStackGrowth.run_growth`.
-/

namespace EthInapproximability.CurrentPaper.EntryDispatch

open Turing BitMachineEncoding

variable {K LA LB VA VB : Type*} [DecidableEq K]

abbrev Label (LA LB : Type*) := Unit ⊕ (LA ⊕ LB)
abbrev Control (VA VB : Type*) := (VA × VB) × Option Bool

def program (flag : K) (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (a₀ : LA) (b₀ : LB) (v₀ : VA) (w₀ : VB) :
    Label LA LB → TM2.Stmt (fun _ : K => Bool) (Label LA LB) (Control VA VB)
  | .inl () => .pop flag (fun c b => (c.1, b))
      (.branch (fun c => c.2.getD false)
        (.load (fun _ => ((v₀, w₀), none)) (.goto (fun _ => .inr (.inl a₀))))
        (.load (fun _ => ((v₀, w₀), none)) (.goto (fun _ => .inr (.inr b₀)))))
  | .inr (.inl l) => BitMachineInline.stmt (fun l => (Sum.inr (Sum.inl l) : Label LA LB))
      (fun v => ((v, w₀), (none : Option Bool))) (fun c => c.1.1) none (A l)
  | .inr (.inr l) => BitMachineInline.stmt (fun l => (Sum.inr (Sum.inr l) : Label LA LB))
      (fun w => ((v₀, w), (none : Option Bool))) (fun c => c.1.2) none (B l)

theorem run_left (flag : K) (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (a₀ : LA) (b₀ : LB) (v₀ : VA) (w₀ : VB)
    (c : Control VA VB) (S : K → List Bool) (rest : List Bool)
    (hflag : S flag = true :: rest) (v₁ : VA) (T : K → List Bool) (ta : ℕ)
    (ha : ((advance A)^[ta])
      (⟨some a₀, v₀, Function.update S flag rest⟩ : TM2.Cfg (fun _ : K => Bool) LA VA) =
      ⟨none, v₁, T⟩) :
    ∃ t ≤ ta + 1, ((advance (program flag A B a₀ b₀ v₀ w₀))^[t])
      (⟨some (Sum.inl ()), c, S⟩ : TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
      ⟨none, ((v₁, w₀), none), T⟩ := by
  have hgate : advance (program flag A B a₀ b₀ v₀ w₀)
      (⟨some (Sum.inl ()), c, S⟩ : TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
      ⟨some (Sum.inr (Sum.inl a₀)), ((v₀, w₀), none), Function.update S flag rest⟩ := by
    simp [advance, TM2.step, TM2.stepAux, program, hflag]
  have hah : (((advance A)^[ta])
      (⟨some a₀, v₀, Function.update S flag rest⟩ : TM2.Cfg (fun _ : K => Bool) LA VA)).l =
      none := by rw [ha]
  obtain ⟨n, hn, hr⟩ := BitMachineInline.outputs
    (fun l => (Sum.inr (Sum.inl l) : Label LA LB))
    (fun v => ((v, w₀), (none : Option Bool))) (fun c => c.1.1) (fun _ => rfl) none A
    (program flag A B a₀ b₀ v₀ w₀) (fun _ => rfl) _ ta hah
  rw [ha] at hr
  refine ⟨n + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply, hgate]
  exact hr

theorem run_right (flag : K) (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (a₀ : LA) (b₀ : LB) (v₀ : VA) (w₀ : VB)
    (c : Control VA VB) (S : K → List Bool) (rest : List Bool)
    (hflag : S flag = false :: rest) (w₁ : VB) (T : K → List Bool) (tb : ℕ)
    (hb : ((advance B)^[tb])
      (⟨some b₀, w₀, Function.update S flag rest⟩ : TM2.Cfg (fun _ : K => Bool) LB VB) =
      ⟨none, w₁, T⟩) :
    ∃ t ≤ tb + 1, ((advance (program flag A B a₀ b₀ v₀ w₀))^[t])
      (⟨some (Sum.inl ()), c, S⟩ : TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
      ⟨none, ((v₀, w₁), none), T⟩ := by
  have hgate : advance (program flag A B a₀ b₀ v₀ w₀)
      (⟨some (Sum.inl ()), c, S⟩ : TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
      ⟨some (Sum.inr (Sum.inr b₀)), ((v₀, w₀), none), Function.update S flag rest⟩ := by
    simp [advance, TM2.step, TM2.stepAux, program, hflag]
  have hbh : (((advance B)^[tb])
      (⟨some b₀, w₀, Function.update S flag rest⟩ : TM2.Cfg (fun _ : K => Bool) LB VB)).l =
      none := by rw [hb]
  obtain ⟨n, hn, hr⟩ := BitMachineInline.outputs
    (fun l => (Sum.inr (Sum.inr l) : Label LA LB))
    (fun w => ((v₀, w), (none : Option Bool))) (fun c => c.1.2) (fun _ => rfl) none B
    (program flag A B a₀ b₀ v₀ w₀) (fun _ => rfl) _ tb hbh
  rw [hb] at hr
  refine ⟨n + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply, hgate]
  exact hr

/-! ## Answer extraction -/

def moveBit (src dst : K) : Unit → TM2.Stmt (fun _ : K => Bool) Unit (Option Bool)
  | () => .pop src (fun _ b => b) (.push dst (fun v => v.getD false) .halt)

theorem move_run (src dst : K) (hne : src ≠ dst) (S : K → List Bool) (b : Bool)
    (rest : List Bool) (hS : S src = b :: rest) :
    ((advance (moveBit src dst))^[1])
      (⟨some (), none, S⟩ : TM2.Cfg (fun _ : K => Bool) Unit (Option Bool)) =
      ⟨none, some b, Function.update (Function.update S src rest) dst (b :: S dst)⟩ := by
  simp [advance, TM2.step, TM2.stepAux, moveBit, hS, Function.update_of_ne hne.symm]

/-! ## Growth-bounded charged clear -/

theorem clear_bounded {L V : Type*}
    (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (reset : V → V) (next : L) (n : ℕ) (bank : Fin n → K)
    (hbank : Function.Injective bank) (label : Fin (n + 1) → L)
    (hsteps : ∀ i : Fin n, P (label i.castSucc) =
      BitMachineClearBank.clearStep (bank i) (label i.castSucc) (label i.succ))
    (hfinish : P (label (Fin.last n)) = BitMachineClearBank.finishStep reset next)
    (v : V) (S : K → List Bool) (B : ℕ) (hB : ∀ i, (S (bank i)).length ≤ B) :
    ∃ t ≤ n * B + n + 1, ((advance P)^[t]) ⟨some (label 0), (v, none), S⟩ =
      ⟨some next, (reset v, none), BitMachineClearBank.cleared bank S⟩ := by
  refine ⟨_, ?_, BitMachineClearBank.clear_bank_run P reset next n bank hbank label hsteps
    hfinish v S⟩
  have hs : ∑ i, (S (bank i)).length ≤ ∑ _i : Fin n, B :=
    Finset.sum_le_sum (fun i _ => hB i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
  omega

theorem growth_bound {L V : Type*} [Fintype L]
    (P : L → TM2.Stmt (fun _ : K => Bool) L V) (c : TM2.Cfg (fun _ : K => Bool) L V)
    (t T B0 : ℕ) (ht : t ≤ T) (j : K) (h0 : (c.stk j).length ≤ B0) :
    ((((advance P)^[t]) c).stk j).length ≤ B0 + BitMachineStackGrowth.perStep P * T := by
  have hg := BitMachineStackGrowth.run_growth P c t j
  have hm : BitMachineStackGrowth.perStep P * t ≤ BitMachineStackGrowth.perStep P * T :=
    Nat.mul_le_mul_left _ ht
  omega

#print axioms run_left
#print axioms run_right
#print axioms move_run
#print axioms clear_bounded
#print axioms growth_bound

end EthInapproximability.CurrentPaper.EntryDispatch
