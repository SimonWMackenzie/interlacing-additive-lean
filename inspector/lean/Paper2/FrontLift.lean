import Paper2.CheckBit

/-! Unit 3 (lock v12 App. D; T44/U10), lane a-success-table-13, segment (2): the front re-banked onto the H_A3 layout.

Bank of the front: `K13 = JF ⊕ Fin 1` (owner-12's full-front bank `JF` and one flag cell). ONE fixed program
(machine constants `Δ, γ`; `a = γ.num.toNat`, `b = γ.den` as in `FullFront.full_run_sched`)

  `front13 Δ γ = full a b Δ (lifted by Sum.inl) ; CheckBit.checkProg cA cB cO Δ γ`

(one production `BitMachineRawSequence` handoff), where `cA` = the produced unary `n` (LK `nC`), `cB` = the produced
unary `m` (QK cell 1), `cO` = the flag cell. It is embedded into the widened H_A3 bank `Fin (a FS + 3)` by ONE fixed
injection `ιK` built from the A3LLayout positions: the start-bank region onto the master start region `OS`, the packet
onto the three packet positions, the flag onto `flag₁`, everything else (the graph-byte front bank `J2`, the threshold
bank `JM`, the copy scratch) onto the front scratch `FS = J2 ⊕ (JM ⊕ Fin 1)`. From `Wrap.widen (a FS) X` the run ends in
exactly `layoutBank FS X (region FS (startBank …) ![[bit], [], []] Z)`. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace Paper2.FrontLift

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.FullFront (JF jg jt so pk zs full fullStart fullCtl F0 X0 exitBankG)
open Paper2.A3Assembly

/-- The front scratch. -/
abbrev FS := CountFront.J2 ⊕ (TMFront.JM ⊕ Fin 1)

set_option synthInstance.maxSize 16384 in
instance instFtFS : Fintype FS := inferInstance
instance instDecFS : DecidableEq FS :=
  @instDecidableEqSum _ _ FullFront.instDecJ2 (@instDecidableEqSum _ _ FullFront.instDecJM inferInstance)

/-- The front bank. -/
abbrev K13 := JF ⊕ Fin 1
instance instDecK13 : DecidableEq K13 := @instDecidableEqSum _ _ FullFront.instDecJF inferInstance

def ιL : JF ↪ K13 := ⟨Sum.inl, Sum.inl_injective⟩

def cA : K13 := .inl (jg (CountFront.jc (CountFront.lc LProducer.nC)))
def cB : K13 := .inl (jg (CountFront.jc (CountFront.qc (.inl 1))))
def cO : K13 := .inr 0

theorem cA_cB : cA ≠ cB := by simp [cA, cB, jg, CountFront.jc, CountFront.lc, CountFront.qc]
theorem cA_cO : cA ≠ cO := by simp [cA, cO]
theorem cB_cO : cB ≠ cO := by simp [cB, cO]

/-- The front program on `K13`. -/
def front13 (Δ : ℕ) (γ : ℚ) :=
  BitMachineRawSequence.program (Lift.liftP ιL (full γ.num.toNat γ.den Δ)) (CheckBit.checkProg cA cB cO Δ γ)
    CheckBit.DL.rdA fullCtl (CheckBit.ctl0 (CheckBit.NA Δ γ) (CheckBit.NB Δ γ))

/-! ### The layout injection -/

/-- A front-scratch cell as a work cell. -/
def fsW (z : FS) : Lift.W FS := .inr (.inr (.inr (.inr (.inr (.inr z)))))

/-- The layout cell of each front cell. -/
def toW : K13 → Lift.W FS ⊕ Fin 3
  | .inl (.inl x) => .inl (fsW (.inl x))
  | .inl (.inr (.inl x)) => .inl (fsW (.inr (.inl x)))
  | .inl (.inr (.inr (.inl x))) => .inl (.inr (.inl x))
  | .inl (.inr (.inr (.inr (.inl i)))) => .inr i
  | .inl (.inr (.inr (.inr (.inr z)))) => .inl (fsW (.inr (.inr z)))
  | .inr _ => .inl (.inl 0)

theorem toW_inj : Function.Injective toW := by
  intro x y h
  rcases x with (x | x | x | x | x) | x <;> rcases y with (y | y | y | y | y) | y <;>
    simp [toW, fsW] at h ⊢ <;> first | exact h | exact Subsingleton.elim _ _

/-- The fixed injection of the front bank into the widened H_A3 bank. -/
def ιK : K13 ↪ Fin (Lift.a FS + 3) := ⟨fun x => Lift.pos FS (toW x), (Lift.pos_injective FS).comp toW_inj⟩

/-- The front-scratch cell of the front bank. -/
def fsK : FS → K13
  | .inl x => .inl (.inl x)
  | .inr (.inl x) => .inl (.inr (.inl x))
  | .inr (.inr z) => .inl (.inr (.inr (.inr (.inr z))))

theorem toW_fsK (z : FS) : toW (fsK z) = .inl (fsW z) := by
  rcases z with z | z | z <;> rfl

/-- The re-banked front (ONE fixed program on `Fin (a FS + 3)`). -/
def front (Δ : ℕ) (γ : ℚ) := Lift.liftP ιK (front13 Δ γ)
def sF (Δ : ℕ) (γ : ℚ) := FullFront.labelOfP (front13 Δ γ)
  (BitMachineRawSequence.leftLabel (fullStart γ.num.toNat γ.den Δ))
def vF (Δ : ℕ) (γ : ℚ) := (fullCtl, CheckBit.ctl0 (CheckBit.NA Δ γ) (CheckBit.NB Δ γ))

/-! ### Bank identities -/

theorem bank_inl (S : JF → List Bool) : bank ιL (fun _ => []) S = Sum.elim S (fun _ => []) := by
  funext x
  rcases x with x | x
  · exact bank_at ιL _ S x
  · rw [bank_outside ιL _ S _ (by rintro ⟨y, hy⟩; cases hy)]
    rfl

theorem miss (S : K13 → List Bool) (x : Lift.W FS ⊕ Fin 3) (h : ∀ y, toW y ≠ x) :
    bank ιK (fun _ => []) S (Lift.pos FS x) = [] :=
  bank_outside ιK _ S _ (by rintro ⟨y, hy⟩; exact h y (Lift.pos_injective FS hy))

theorem hit (S : K13 → List Bool) (y : K13) : bank ιK (fun _ => []) S (Lift.pos FS (toW y)) = S y :=
  bank_at ιK _ S y

/-- **The general re-banking identity.** -/
theorem bank_layout (E : JF → List Bool) (c : List Bool) :
    bank ιK (fun _ => []) (Sum.elim E (fun _ => c)) =
      Lift.layoutBank FS (fun i => E (pk i))
        (Lift.region FS (fun x => E (so x)) ![c, [], []] (fun z => Sum.elim E (fun _ => c) (fsK z))) := by
  apply Lift.bank_ext
  intro x
  rcases x with (i | x | x | x | x | x | z) | i
  · rw [Lift.layoutBank_inl]
    fin_cases i
    · exact hit _ (.inr 0)
    · rw [miss _ _ (by intro y; rcases y with (y | y | y | y | y) | y <;> simp [toW, fsW])]
      rfl
    · rw [miss _ _ (by intro y; rcases y with (y | y | y | y | y) | y <;> simp [toW, fsW])]
      rfl
  · rw [Lift.layoutBank_inl]
    exact hit _ (.inl (so x))
  · rw [Lift.layoutBank_inl, miss _ _ (by intro y; rcases y with (y | y | y | y | y) | y <;> simp [toW, fsW])]
    rfl
  · rw [Lift.layoutBank_inl, miss _ _ (by intro y; rcases y with (y | y | y | y | y) | y <;> simp [toW, fsW])]
    rfl
  · rw [Lift.layoutBank_inl, miss _ _ (by intro y; rcases y with (y | y | y | y | y) | y <;> simp [toW, fsW])]
    rfl
  · rw [Lift.layoutBank_inl, miss _ _ (by intro y; rcases y with (y | y | y | y | y) | y <;> simp [toW, fsW])]
    rfl
  · rw [Lift.layoutBank_inl]
    have e : (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr z)))))) : Lift.W FS ⊕ Fin 3) =
        toW (fsK z) := by rw [toW_fsK]; rfl
    rw [e, hit]
    rfl
  · rw [Lift.layoutBank_inr]
    exact hit _ (.inl (pk i))

/-- The start bank: the widened packet. -/
theorem bank_start (X : Fin 3 → List Bool) :
    bank ιK (fun _ => []) (bank ιL (fun _ => []) (F0 X)) = Wrap.widen (Lift.a FS) X := by
  rw [bank_inl, bank_layout, Lift.widen_eq]
  congr 1
  funext x
  rcases x with i | x | x | x | x | x | z
  · fin_cases i <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases z with z | z | z <;> rfl

/-- The exit bank after the decision. -/
theorem bank_exit (E : JF → List Bool) (bit : Bool) :
    bank ιK (fun _ => [])
      (Function.update (Function.update (Function.update (bank ιL (fun _ => []) E) cA []) cB []) cO
        (bit :: bank ιL (fun _ => []) E cO)) =
      Lift.layoutBank FS (fun i => E (pk i))
        (Lift.region FS (fun x => E (so x)) ![[bit], [], []]
          (fun z => Function.update (Function.update (Function.update (bank ιL (fun _ => []) E) cA []) cB []) cO
            [bit] (fsK z))) := by
  have h0 : bank ιL (fun _ => []) E cO = [] := by rw [bank_inl]; rfl
  rw [h0]
  have hS : Function.update (Function.update (Function.update (bank ιL (fun _ => []) E) cA []) cB []) cO [bit] =
      Sum.elim (Function.update (Function.update E (jg (CountFront.jc (CountFront.lc LProducer.nC))) [])
        (jg (CountFront.jc (CountFront.qc (.inl 1)))) []) (fun _ => [bit]) := by
    rw [bank_inl]
    funext x
    rcases x with x | x
    · simp only [Function.update_apply, cA, cB, cO, Sum.elim_inl, Sum.inl.injEq, reduceCtorEq, if_false]
    · have : x = 0 := Subsingleton.elim _ _
      subst this
      simp [cO]
  rw [hS, bank_layout]
  congr 2

end

end Paper2.FrontLift

#print axioms Paper2.FrontLift.toW_inj
#print axioms Paper2.FrontLift.bank_layout
#print axioms Paper2.FrontLift.bank_start
#print axioms Paper2.FrontLift.bank_exit
