import CurrentAdditive.GenericParameterBranch
import EthInapproximability.CurrentPaper.ExactParameterMachinePairInstall

/-!
# Physical two-operand parameter packing into a persistent bank

Two source-preserving Boolean-stack copies feed the fixed unary pair encoder.
A fourth phase copies its separated output into an empty persistent target.
All six fresh local cells and every foreign persistent cell are tracked.
-/

namespace CurrentAdditive.GenericParameterPair
export EthInapproximability.CurrentPaper.ExactParameterMachinePairInstall
  (LRLabel LRControl LRPLabel LRPControl Label Control startLabel startControl)

open Turing EthInapproximability.CurrentPaper EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.GenericParameterBranch

variable {Base : Type*} [DecidableEq Base]
abbrev Stack (Base : Type*) := Base ⊕ Fin 6

instance : DecidableEq (Stack Base) := inferInstance

def leftSlots (source : Base) : Fin 3 ↪ Stack Base where
  toFun
    | 0 => .inl source
    | 1 => .inr 0
    | _ => .inr 3
  inj' := by intro x y h; fin_cases x <;> fin_cases y <;> simp_all

def rightSlots (source : Base) : Fin 3 ↪ Stack Base where
  toFun
    | 0 => .inl source
    | 1 => .inr 1
    | _ => .inr 4
  inj' := by intro x y h; fin_cases x <;> fin_cases y <;> simp_all

def pairSlots : Fin 3 ↪ Stack Base where
  toFun
    | 0 => .inr 0
    | 1 => .inr 1
    | _ => .inr 2
  inj' := by intro x y h; fin_cases x <;> fin_cases y <;> simp_all

def outputSlots (target : Base) : Fin 3 ↪ Stack Base where
  toFun
    | 0 => .inr 2
    | 1 => .inl target
    | _ => .inr 5
  inj' := by intro x y h; fin_cases x <;> fin_cases y <;> simp_all

def initial (B : Base → List Bool) : Stack Base → List Bool :=
  Sum.elim B (fun _ => [])

def afterLeft (B : Base → List Bool) (n : ℕ) : Stack Base → List Bool :=
  Function.update (initial B) (.inr 0) (List.replicate n true)

def afterRight (B : Base → List Bool) (n m : ℕ) : Stack Base → List Bool :=
  Function.update (afterLeft B n) (.inr 1) (List.replicate m true)

def afterPair (B : Base → List Bool) (n m : ℕ) : Stack Base → List Bool :=
  Function.update
    (Function.update
      (Function.update (afterRight B n m) (.inr 0) [])
      (.inr 1) [])
    (.inr 2) (MatrixUnaryArithmetic.encodeInput n m)

def terminal (B : Base → List Bool) (target : Base) (n m : ℕ) :
    Stack Base → List Bool :=
  Function.update (afterPair B n m) (.inl target)
    (MatrixUnaryArithmetic.encodeInput n m)

def leftProgram (source : Base) :=
  CurrentAdditive.GenericParameterBranch.copyProgram (leftSlots source)
def rightProgram (source : Base) :=
  CurrentAdditive.GenericParameterBranch.copyProgram (rightSlots source)
def pairProgram (l : ExactParameterMachinePair.Label) :
    TM2.Stmt (fun _ : Stack Base => Bool) ExactParameterMachinePair.Label Bool :=
  BitMachineStackEmbedding.stmt pairSlots id id id none
    (ExactParameterMachinePair.program l)
def outputProgram (target : Base) :=
  CurrentAdditive.GenericParameterBranch.copyProgram (outputSlots target)

theorem run_left (B : Base → List Bool) (source : Base) (n : ℕ)
    (hsource : B source = List.replicate n true) :
    ∃ t ≤ 2*n+2,
      ((advance (leftProgram source))^[t])
        (⟨some .scan, none, initial B⟩ :
          TM2.Cfg (fun _ : Stack Base => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, afterLeft B n⟩ := by
  simpa only [leftProgram, initial, afterLeft, List.length_replicate]
    using CurrentAdditive.GenericParameterBranch.copy_run (leftSlots source) (initial B)
      (List.replicate n true) hsource (by rfl) (by rfl)

theorem run_right (B : Base → List Bool) (source : Base) (n m : ℕ)
    (hsource : B source = List.replicate m true) :
    ∃ t ≤ 2*m+2,
      ((advance (rightProgram source))^[t])
        (⟨some .scan, none, afterLeft B n⟩ :
          TM2.Cfg (fun _ : Stack Base => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, afterRight B n m⟩ := by
  have hs : afterLeft B n ((rightSlots source) 0) =
      List.replicate m true := by
    change B source = List.replicate m true
    exact hsource
  have ht : afterLeft B n ((rightSlots source) 1) = [] := by rfl
  have hw : afterLeft B n ((rightSlots source) 2) = [] := by rfl
  simpa only [rightProgram, afterRight, List.length_replicate]
    using CurrentAdditive.GenericParameterBranch.copy_run (rightSlots source)
      (afterLeft B n) (List.replicate m true) hs ht hw

theorem run_pair (B : Base → List Bool) (n m : ℕ) :
    ∃ t ≤ n+m+3,
      ((advance pairProgram)^[t])
        (⟨some .right, false, afterRight B n m⟩ :
          TM2.Cfg (fun _ : Stack Base => Bool) ExactParameterMachinePair.Label Bool) =
        ⟨none, false, afterPair B n m⟩ := by
  classical
  let c := ExactParameterMachinePair.cfg (some .right) false
    (List.replicate n true) (List.replicate m true) []
  have hbank : BitMachineStackEmbedding.bank pairSlots
      (afterRight B n m) c.stk = afterRight B n m := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> rfl
  have hlocal : ((advance ExactParameterMachinePair.program)^[n+m+3]) c =
      ExactParameterMachinePair.cfg none false [] []
        (MatrixUnaryArithmetic.encodeInput n m) := by
    exact ExactParameterMachinePair.exact_run n m
  have hhalt : (((advance ExactParameterMachinePair.program)^[n+m+3]) c).l =
      none := by rw [hlocal]; rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs pairSlots
    (afterRight B n m) id id id (by intro v; rfl) none
    ExactParameterMachinePair.program pairProgram (by intro l; rfl)
    c (n+m+3) hhalt
  rw [hlocal] at he
  change ((advance pairProgram)^[t])
      ⟨some .right, false,
        BitMachineStackEmbedding.bank pairSlots (afterRight B n m) c.stk⟩ =
      ⟨none, false,
        BitMachineStackEmbedding.bank pairSlots (afterRight B n m)
          (ExactParameterMachinePair.cfg none false [] []
            (MatrixUnaryArithmetic.encodeInput n m)).stk⟩ at he
  have hupdate :
      (ExactParameterMachinePair.cfg none false [] []
        (MatrixUnaryArithmetic.encodeInput n m)).stk =
      Function.update
        (Function.update (Function.update c.stk 0 []) 1 []) 2
        (MatrixUnaryArithmetic.encodeInput n m) := by
    funext k
    fin_cases k <;> rfl
  rw [hbank, hupdate, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update, hbank] at he
  exact ⟨t, ht, he⟩

theorem run_output (B : Base → List Bool) (target : Base) (n m : ℕ)
    (htarget : B target = []) :
    ∃ t ≤ 2 * (MatrixUnaryArithmetic.encodeInput n m).length + 2,
      ((advance (outputProgram target))^[t])
        (⟨some .scan, none, afterPair B n m⟩ :
          TM2.Cfg (fun _ : Stack Base => Bool) BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, terminal B target n m⟩ := by
  have hs : afterPair B n m ((outputSlots target) 0) =
      MatrixUnaryArithmetic.encodeInput n m := by rfl
  have ht : afterPair B n m ((outputSlots target) 1) = [] := by
    change B target = []
    exact htarget
  have hw : afterPair B n m ((outputSlots target) 2) = [] := by rfl
  exact CurrentAdditive.GenericParameterBranch.copy_run (outputSlots target)
    (afterPair B n m) (MatrixUnaryArithmetic.encodeInput n m) hs ht hw

def lrProgram (left right : Base) :
    LRLabel → TM2.Stmt (fun _ : Stack Base => Bool) LRLabel LRControl :=
  BitMachineRawSequence.program (leftProgram left) (rightProgram right)
    .scan none none

def lrpProgram (left right : Base) :
    LRPLabel → TM2.Stmt (fun _ : Stack Base => Bool) LRPLabel LRPControl :=
  BitMachineRawSequence.program (lrProgram left right) pairProgram
    .right (none, none) false

def program (left right target : Base) :
    Label → TM2.Stmt (fun _ : Stack Base => Bool) Label Control :=
  BitMachineRawSequence.program (lrpProgram left right)
    (outputProgram target) .scan ((none, none), false) none

/-- The two operands may be the same persistent source. Both are copied before
the consuming pair encoder runs, and the final persistent target is empty. -/
theorem run_install (B : Base → List Bool) (left right target : Base)
    (n m : ℕ) (hleft : B left = List.replicate n true)
    (hright : B right = List.replicate m true) (htarget : B target = []) :
    ∃ t ≤ (2*n+2) + (2*m+2) + (n+m+3) +
      (2*(MatrixUnaryArithmetic.encodeInput n m).length+2) + 3,
      ((advance (program left right target))^[t])
        (⟨some startLabel, startControl, initial B⟩ :
          TM2.Cfg (fun _ : Stack Base => Bool) Label Control) =
        ⟨none, startControl, terminal B target n m⟩ := by
  obtain ⟨tl, htl, hrl⟩ := run_left B left n hleft
  obtain ⟨tr, htr, hrr⟩ := run_right B right n m hright
  obtain ⟨tlr, htlr, hrlr⟩ := BitMachineRawSequence.runs
    (leftProgram left) (rightProgram right) .scan .scan
    none none none none
    (initial B) (afterLeft B n) (afterRight B n m) tl tr hrl hrr
  obtain ⟨tp, htp, hrp⟩ := run_pair B n m
  obtain ⟨tlrp, htlrp, hrlrp⟩ := BitMachineRawSequence.runs
    (lrProgram left right) pairProgram (.inl .scan) .right
    (none, none) (none, none) false false
    (initial B) (afterRight B n m) (afterPair B n m)
    tlr tp hrlr hrp
  obtain ⟨tout, htout, hrout⟩ := run_output B target n m htarget
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (lrpProgram left right) (outputProgram target)
    (.inl (.inl .scan)) .scan
    ((none, none), false) ((none, none), false) none none
    (initial B) (afterPair B n m) (terminal B target n m)
    tlrp tout hrlrp hrout
  refine ⟨t, by omega, ?_⟩
  simpa only [program, startLabel, startControl, lrProgram, lrpProgram]
    using hr

theorem terminal_target (B : Base → List Bool) (target : Base)
    (n m : ℕ) : terminal B target n m (.inl target) =
      MatrixUnaryArithmetic.encodeInput n m := by simp [terminal]

theorem terminal_base_other (B : Base → List Bool) (target j : Base)
    (n m : ℕ) (hj : j ≠ target) :
    terminal B target n m (.inl j) = B j := by
  have hne : (Sum.inl j : Stack Base) ≠ .inl target := by
    intro h
    exact hj (Sum.inl.inj h)
  rw [terminal, Function.update_of_ne hne]
  rfl

def framedProgram {J : Type*} [DecidableEq J]
    (left right target : Base) (ι : Stack Base ↪ J) (l : Label) :
    TM2.Stmt (fun _ : J => Bool) Label Control :=
  BitMachineStackEmbedding.stmt ι id id id none
    (program left right target l)

/-- Ambient version for the parameter compiler's growing Master bank. It
starts with the actual bank; only this pair-installation's six fresh local
stacks must be empty. Both unary inputs remain in their Base cells. -/
theorem run_install_framed_from_ambient {J : Type*} [DecidableEq J]
    (left right target : Base) (n m : ℕ)
    (ι : Stack Base ↪ J) (S : J → List Bool)
    (hleft : S (ι (.inl left)) = List.replicate n true)
    (hright : S (ι (.inl right)) = List.replicate m true)
    (htarget : S (ι (.inl target)) = [])
    (hfresh : ∀ k : Fin 6, S (ι (.inr k)) = []) :
    let B : Base → List Bool := fun j => S (ι (.inl j))
    ∃ t ≤ (2*n+2) + (2*m+2) + (n+m+3) +
      (2*(MatrixUnaryArithmetic.encodeInput n m).length+2) + 3,
      ((advance (framedProgram left right target ι))^[t])
        (⟨some startLabel, startControl, S⟩ :
          TM2.Cfg (fun _ : J => Bool) Label Control) =
        ⟨none, startControl,
          BitMachineStackEmbedding.bank ι S (terminal B target n m)⟩ := by
  classical
  dsimp only
  let B : Base → List Bool := fun j => S (ι (.inl j))
  have hplace : BitMachineStackEmbedding.bank ι S (initial B) = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    cases k with
    | inl j => rfl
    | inr j => exact (hfresh j).symm
  obtain ⟨u, hu, hr⟩ := run_install B left right target n m
    hleft hright htarget
  have hh : (((advance (program left right target))^[u])
      (⟨some startLabel, startControl, initial B⟩ :
        TM2.Cfg (fun _ : Stack Base => Bool) Label Control)).l = none := by
    rw [hr]
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs ι S
    id id id (by intro v; rfl) none
    (program left right target) (framedProgram left right target ι)
    (by intro l; rfl)
    (⟨some startLabel, startControl, initial B⟩ :
      TM2.Cfg (fun _ : Stack Base => Bool) Label Control) u hh
  rw [hr] at he
  change ((advance (framedProgram left right target ι))^[t])
      ⟨some startLabel, startControl,
        BitMachineStackEmbedding.bank ι S (initial B)⟩ =
      ⟨none, startControl,
        BitMachineStackEmbedding.bank ι S (terminal B target n m)⟩ at he
  rw [hplace] at he
  exact ⟨t, ht.trans hu, he⟩

theorem ambient_target {J : Type*} [DecidableEq J]
    (B : Base → List Bool) (target : Base) (n m : ℕ)
    (ι : Stack Base ↪ J) (S : J → List Bool) :
    BitMachineStackEmbedding.bank ι S (terminal B target n m)
      (ι (.inl target)) = MatrixUnaryArithmetic.encodeInput n m := by
  rw [BitMachineStackEmbedding.bank_at]
  exact terminal_target B target n m

theorem ambient_base_other {J : Type*} [DecidableEq J]
    (B : Base → List Bool) (target j : Base) (hj : j ≠ target)
    (n m : ℕ) (ι : Stack Base ↪ J) (S : J → List Bool) :
    BitMachineStackEmbedding.bank ι S (terminal B target n m)
      (ι (.inl j)) = B j := by
  rw [BitMachineStackEmbedding.bank_at]
  exact terminal_base_other B target j n m hj

theorem ambient_foreign {J : Type*} [DecidableEq J]
    (B : Base → List Bool) (target : Base) (n m : ℕ)
    (ι : Stack Base ↪ J) (S : J → List Bool)
    (j : J) (hj : ¬ ∃ k, ι k = j) :
    BitMachineStackEmbedding.bank ι S (terminal B target n m) j = S j :=
  BitMachineStackEmbedding.bank_outside ι S _ j hj

end CurrentAdditive.GenericParameterPair
