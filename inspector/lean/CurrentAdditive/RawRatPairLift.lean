import CurrentAdditive.MachineInvokeCore
import CurrentAdditive.RawRatPairAssembler
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! Physical embedding of the checked two-rational-word assembler into the
extended stateful-list bank. -/

namespace CurrentAdditive.MinimumRatioContext.RawRatPairLift

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MachineInvokeCore BitMachineStackEmbedding

def localSlot (N : ℕ) : Fin 7 ↪ StackN N :=
  ⟨![16,20,22,23,24,25,26], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all
    all_goals
      have hv := congrArg Fin.val h
      have h16 : 16 < 32 + N := by omega
      have h20 : 20 < 32 + N := by omega
      have h22 : 22 < 32 + N := by omega
      have h23 : 23 < 32 + N := by omega
      have h24 : 24 < 32 + N := by omega
      have h25 : 25 < 32 + N := by omega
      have h26 : 26 < 32 + N := by omega
      simp [Nat.mod_eq_of_lt h16, Nat.mod_eq_of_lt h20,
        Nat.mod_eq_of_lt h22, Nat.mod_eq_of_lt h23,
        Nat.mod_eq_of_lt h24, Nat.mod_eq_of_lt h25,
        Nat.mod_eq_of_lt h26] at hv⟩

def embed (N : ℕ) : RawRatPairAssembler.Stack 0 ↪ StackN N :=
  ⟨fun
    | .inl i => localSlot N i
    | .inr i => Fin.elim0 i,
   by
     intro a b h
     cases a with
     | inl a =>
         cases b with
         | inl b => exact congrArg Sum.inl ((localSlot N).injective h)
         | inr b => exact Fin.elim0 b
     | inr a => exact Fin.elim0 a⟩

def program (N : ℕ) :=
  fun l => stackStmt (embed N) (RawRatPairAssembler.program 0 l)

abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
  (BitMachineBankSerialize.Label 2)

abbrev Control := (Option Bool × Option Bool) × Option Bool

def start : Label :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)

def control : Control := ((none, none), none)

theorem initial_eq {N : ℕ} (S : StackN N → List Bool)
    (x y : List Bool)
    (hx : S 16 = x) (hy : S 20 = y)
    (h22 : S 22 = []) (h23 : S 23 = [])
    (h24 : S 24 = []) (h25 : S 25 = [])
    (h26 : S 26 = []) :
    bank (embed N) S
      (RawRatPairAssembler.initialBank x y (Fin.elim0)) = S := by
  apply bank_eq_self
  intro k
  cases k with
  | inl k =>
      fin_cases k <;>
        simp [RawRatPairAssembler.initialBank, embed, localSlot,
          hx, hy, h22, h23, h24, h25, h26]
  | inr k => exact Fin.elim0 k

theorem embedded_run {N : ℕ} (S : StackN N → List Bool)
    (x y : List Bool)
    (hx : S 16 = x) (hy : S 20 = y)
    (h22 : S 22 = []) (h23 : S 23 = [])
    (h24 : S 24 = []) (h25 : S 25 = [])
    (h26 : S 26 = []) :
    ∃ t ≤ 6 * (x.length + y.length + 2),
      ∃ R : BitMachineBankSerialize.Bank 2,
      ((advance (program N))^[t])
        (⟨some start, control, S⟩ :
          TM2.Cfg (fun _ : StackN N => Bool) _ _) =
        ⟨none, control,
          bank (embed N) S
            (RawRatPairAssembler.completedBank x y (Fin.elim0) R)⟩ := by
  obtain ⟨t, ht, R, hr⟩ :=
    RawRatPairAssembler.assembly_run x y (Fin.elim0 : Fin 0 → List Bool)
  have he := BitMachineStackRun.run (embed N) S
    (RawRatPairAssembler.program 0)
    (⟨some start, control,
      RawRatPairAssembler.initialBank x y (Fin.elim0)⟩ :
      TM2.Cfg (fun _ : RawRatPairAssembler.Stack 0 => Bool) _ _) t
  have hr' : ((advance (RawRatPairAssembler.program 0))^[t])
      (⟨some start, control,
        RawRatPairAssembler.initialBank x y (Fin.elim0)⟩ :
        TM2.Cfg (fun _ : RawRatPairAssembler.Stack 0 => Bool) _ _) =
      ⟨none, control,
        RawRatPairAssembler.completedBank x y (Fin.elim0) R⟩ := by
    simpa only [start, control] using hr
  rw [hr'] at he
  refine ⟨t, ht, R, ?_⟩
  simpa only [program, BitMachineStackEmbedding.stackCfg,
    initial_eq S x y hx hy h22 h23 h24 h25 h26] using he

#print axioms embedded_run

end CurrentAdditive.MinimumRatioContext.RawRatPairLift
