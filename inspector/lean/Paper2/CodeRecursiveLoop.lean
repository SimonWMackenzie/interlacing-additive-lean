import Paper2.CodeRecursiveRound

/-! A fixed finite controller iterates the checked physical successor round.
The number of rounds is supplied on a literal unary fuel stack. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeRecursiveLoop

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSource
open Paper2.CodeRecursiveColumn Paper2.CodeRecursiveRow
open Paper2.CodeRecursiveStep Paper2.CodeRecursiveRound

abbrev Stack := Fin 65
abbrev RoundStack := Paper2.CodeRecursiveColumn.Stack
abbrev RoundLabel := BitMachineRawSequence.Label StepLabel ReentryLabel
abbrev RoundControl := StepControl × ReentryControl
abbrev Label := RoundLabel ⊕ Unit
abbrev Control := RoundControl × Option Bool

def embedRound : RoundStack ↪ Stack where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro a b h
    exact Fin.ext (Fin.mk.inj h)

def foreign (fuel : List Bool) : Stack → List Bool :=
  fun i => if i = 64 then fuel else []

def roundStart : RoundLabel := BitMachineRawSequence.leftLabel stepStart
def roundControl : RoundControl := (stepControl,reentryControl)

noncomputable def program : Label →
    TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt embedRound Sum.inl
      (fun v => (v,none)) Prod.fst (some (.inr ()))
      (CodeRecursiveRound.program l)
  | .inr () => pop 64 (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (load (fun _ => (roundControl,none))
          (goto (fun _ => .inl roundStart)))
        (load (fun _ => (roundControl,none)) halt))

noncomputable def ready (n s q₁ q₂ w Q : Nat)
    (row col : Code) (fuel : List Bool) :
    TM2.Cfg (fun _ : Stack => Bool) Label Control :=
  ⟨some (.inr ()), (roundControl,none),
    BitMachineStackEmbedding.bank embedRound (foreign fuel)
      (initial n s q₁ q₂ w Q row col)⟩

noncomputable def finished (n s q₁ q₂ w Q : Nat)
    (row col : Code) :
    TM2.Cfg (fun _ : Stack => Bool) Label Control :=
  ⟨none, (roundControl,none),
    BitMachineStackEmbedding.bank embedRound (foreign [])
      (initial n s q₁ q₂ w Q row col)⟩

theorem bank_fuel (S : RoundStack → List Bool) (fuel : List Bool) :
    BitMachineStackEmbedding.bank embedRound (foreign fuel) S 64 = fuel := by
  rw [BitMachineStackEmbedding.bank_outside]
  · rfl
  · rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    simp [embedRound] at hv
    omega

theorem bank_update_fuel (S : RoundStack → List Bool)
    (old next : List Bool) :
    Function.update
      (BitMachineStackEmbedding.bank embedRound (foreign old) S)
      64 next =
    BitMachineStackEmbedding.bank embedRound (foreign next) S := by
  funext i
  by_cases hi : i = (64 : Stack)
  · subst i
    rw [Function.update_self, bank_fuel]
  · rw [Function.update_of_ne hi]
    by_cases he : ∃ j : RoundStack, embedRound j = i
    · obtain ⟨j,rfl⟩ := he
      rw [BitMachineStackEmbedding.bank_at,
        BitMachineStackEmbedding.bank_at]
    · rw [BitMachineStackEmbedding.bank_outside _ _ _ i he,
        BitMachineStackEmbedding.bank_outside _ _ _ i he]
      simp [foreign, hi]

theorem fuel_zero (n s q₁ q₂ w Q : Nat) (row col : Code) :
    advance program (ready n s q₁ q₂ w Q row col []) =
      finished n s q₁ q₂ w Q row col := by
  simp [advance, TM2.step, program, TM2.stepAux,
    ready, finished, bank_fuel, bank_update_fuel]

theorem fuel_cons (n s q₁ q₂ w Q : Nat) (row col : Code)
    (b : Bool) (fuel : List Bool) :
    advance program (ready n s q₁ q₂ w Q row col (b::fuel)) =
      ⟨some (.inl roundStart), (roundControl,none),
        BitMachineStackEmbedding.bank embedRound (foreign fuel)
          (initial n s q₁ q₂ w Q row col)⟩ := by
  simp [advance, TM2.step, program, TM2.stepAux, ready,
    bank_fuel, bank_update_fuel]

theorem round_run (n s q₁ q₂ w Q : Nat) (row col : Code)
    (fuel : List Bool) (hs : 3 ≤ s) :
    ∃ t ≤ CodeRecursiveRound.clock n s q₁ q₂ w Q row col,
      ((advance program)^[t])
        (⟨some (.inl roundStart), (roundControl,none),
          BitMachineStackEmbedding.bank embedRound (foreign fuel)
            (initial n s q₁ q₂ w Q row col)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ready n s q₁ q₂ w Q
          (rowCode q₁ q₂ s w Q col)
          (columnCode n s q₁ q₂ w Q row) fuel := by
  obtain ⟨t,ht,hr⟩ := CodeRecursiveRound.run_exact
    n s q₁ q₂ w Q row col hs
  have hhalt :
      (((advance CodeRecursiveRound.program)^[t])
        (⟨some roundStart, roundControl,
          initial n s q₁ q₂ w Q row col⟩ :
          TM2.Cfg (fun _ : RoundStack => Bool)
            RoundLabel RoundControl)).l = none := by
    rw [show
      ((advance CodeRecursiveRound.program)^[t])
        (⟨some roundStart, roundControl,
          initial n s q₁ q₂ w Q row col⟩ :
          TM2.Cfg (fun _ : RoundStack => Bool)
            RoundLabel RoundControl) =
      ⟨none, roundControl,
        initial n s q₁ q₂ w Q
          (rowCode q₁ q₂ s w Q col)
          (columnCode n s q₁ q₂ w Q row)⟩ by
        simpa only [roundStart, roundControl] using hr]
  obtain ⟨u,hu,hout⟩ := BitMachineStackEmbedding.outputs
    embedRound (foreign fuel) Sum.inl
    (fun v : RoundControl => (v,none)) Prod.fst
    (by intro; rfl) (some (.inr ()))
    CodeRecursiveRound.program program (by intro l; rfl)
    (⟨some roundStart, roundControl,
      initial n s q₁ q₂ w Q row col⟩ :
      TM2.Cfg (fun _ : RoundStack => Bool)
        RoundLabel RoundControl) t hhalt
  rw [show
    ((advance CodeRecursiveRound.program)^[t])
      (⟨some roundStart, roundControl,
        initial n s q₁ q₂ w Q row col⟩ :
        TM2.Cfg (fun _ : RoundStack => Bool)
          RoundLabel RoundControl) =
      ⟨none, roundControl,
        initial n s q₁ q₂ w Q
          (rowCode q₁ q₂ s w Q col)
          (columnCode n s q₁ q₂ w Q row)⟩ by
      simpa only [roundStart, roundControl] using hr] at hout
  refine ⟨u, hu.trans ht, ?_⟩
  simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    Option.map_none, ready] using hout

theorem one_round (n s q₁ q₂ w Q : Nat) (row col : Code)
    (b : Bool) (fuel : List Bool) (hs : 3 ≤ s) :
    ∃ t ≤ CodeRecursiveRound.clock n s q₁ q₂ w Q row col + 1,
      ((advance program)^[t])
        (ready n s q₁ q₂ w Q row col (b::fuel)) =
        ready n s q₁ q₂ w Q
          (rowCode q₁ q₂ s w Q col)
          (columnCode n s q₁ q₂ w Q row) fuel := by
  obtain ⟨t,ht,hr⟩ := round_run n s q₁ q₂ w Q row col fuel hs
  refine ⟨t+1, by omega, ?_⟩
  rw [Function.iterate_succ_apply, fuel_cons]
  exact hr

theorem recursiveCodes_succ (n s q₁ q₂ w Q : Nat)
    (row₀ col₀ : Code) (k : Nat) :
    recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1) =
      let old := recursiveCodes n s q₁ q₂ w Q row₀ col₀ k
      (rowCode q₁ q₂ s w Q old.2,
        columnCode n s q₁ q₂ w Q old.1) := by
  rfl

theorem recursiveCodes_shift (n s q₁ q₂ w Q : Nat)
    (row₀ col₀ : Code) (k : Nat) :
    recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1) =
      recursiveCodes n s q₁ q₂ w Q
        (rowCode q₁ q₂ s w Q col₀)
        (columnCode n s q₁ q₂ w Q row₀) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      calc
        recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1+1) =
            (rowCode q₁ q₂ s w Q
              (recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1)).2,
             columnCode n s q₁ q₂ w Q
              (recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1)).1) :=
          recursiveCodes_succ n s q₁ q₂ w Q row₀ col₀ (k+1)
        _ = (rowCode q₁ q₂ s w Q
              (recursiveCodes n s q₁ q₂ w Q
                (rowCode q₁ q₂ s w Q col₀)
                (columnCode n s q₁ q₂ w Q row₀) k).2,
             columnCode n s q₁ q₂ w Q
              (recursiveCodes n s q₁ q₂ w Q
                (rowCode q₁ q₂ s w Q col₀)
                (columnCode n s q₁ q₂ w Q row₀) k).1) := by rw [ih]
        _ = recursiveCodes n s q₁ q₂ w Q
              (rowCode q₁ q₂ s w Q col₀)
              (columnCode n s q₁ q₂ w Q row₀) (k+1) :=
          (recursiveCodes_succ n s q₁ q₂ w Q
            (rowCode q₁ q₂ s w Q col₀)
            (columnCode n s q₁ q₂ w Q row₀) k).symm

noncomputable def totalClock (n s q₁ q₂ w Q : Nat) :
    Code → Code → Nat → Nat
  | _, _, 0 => 1
  | row, col, k+1 =>
      CodeRecursiveRound.clock n s q₁ q₂ w Q row col + 1 +
        totalClock n s q₁ q₂ w Q
          (rowCode q₁ q₂ s w Q col)
          (columnCode n s q₁ q₂ w Q row) k

/-- Unary fuel drives a single fixed finite controller through exactly
the production recursive-code recurrence; the inductive witness is a time
bound, not an oracle supplying intermediate syntax to the machine. -/
theorem run_k (n s q₁ q₂ w Q : Nat) (row₀ col₀ : Code)
    (k : Nat) (hs : 3 ≤ s) :
    ∃ t ≤ totalClock n s q₁ q₂ w Q row₀ col₀ k,
      ((advance program)^[t])
        (ready n s q₁ q₂ w Q row₀ col₀
          (List.replicate k true)) =
        finished n s q₁ q₂ w Q
          (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).1
          (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).2 := by
  induction k generalizing row₀ col₀ with
  | zero =>
      refine ⟨1, by simp [totalClock], ?_⟩
      simpa only [List.replicate_zero, Function.iterate_one,
        recursiveCodes] using fuel_zero n s q₁ q₂ w Q row₀ col₀
  | succ k ih =>
      let row₁ := rowCode q₁ q₂ s w Q col₀
      let col₁ := columnCode n s q₁ q₂ w Q row₀
      obtain ⟨ta,hta,ha⟩ := one_round n s q₁ q₂ w Q
        row₀ col₀ true (List.replicate k true) hs
      obtain ⟨tb,htb,hb⟩ := ih row₁ col₁
      refine ⟨ta+tb, ?_, ?_⟩
      · dsimp [totalClock, row₁, col₁]
        dsimp [row₁, col₁] at htb
        omega
      · rw [show ta+tb = tb+ta by omega,
          Function.iterate_add_apply]
        simpa only [List.replicate_succ, row₁, col₁,
          recursiveCodes_shift n s q₁ q₂ w Q row₀ col₀ k] using
          congrArg ((advance program)^[tb]) ha |>.trans hb

#print axioms run_k

end Paper2.CodeRecursiveLoop
