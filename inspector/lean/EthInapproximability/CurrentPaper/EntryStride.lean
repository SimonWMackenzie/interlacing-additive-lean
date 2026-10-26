import EthInapproximability.CurrentPaper.MatrixWeightedPower
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.FamilyRowGeneric

/-!
# Segment 2 building block: the physical template stride `b^(s-1-p)`

Lane owner:b-stage4-entry-program-3 (Paper B, unit 2, map item 3).

The template branch source (`MatrixStage4TemplateBitMachine.source_stride`)
holds the unary word `binBase^(s-1-p)`. This module produces it from the
unary operand words `b` (binBase), `s`, and the row's unary `p` (the
`RawRowSeed` quotient), with ONE fixed eight-phase controller on the bank
`SK = Fin 5 ⊕ MatrixWeightedPower.Stack`:

(1) copy `s` into the power fuel cell; (2) one pop (`s - 1`); (3) copy `p`;
(4) a lockstep monus loop (`s - 1 - p`, truncated); (5) push the unit
accumulator; (6) copy `b` into the power base cell; (7) the admitted
`MatrixWeightedPower.program` (`power_run`); (8) charged clear of the base
copy. Seven charged handoffs. Operand words are retained; every scratch cell
is returned blank; the accumulator cell holds exactly `b^(s-1-p)`.
-/

namespace EthInapproximability.CurrentPaper.EntryStride

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps

noncomputable section

abbrev PS := MatrixWeightedPower.Stack
abbrev SK := Fin 5 ⊕ PS

def w (j : Fin 5) : SK := .inl j
def pw (j : Fin 6) : SK := .inr (.inl j)
def fuel : SK := .inr (.inr 0)

def sS : Fin 3 ↪ SK := ⟨![w 1, fuel, w 4], by decide⟩
def sP : Fin 3 ↪ SK := ⟨![w 2, w 3, w 4], by decide⟩
def sB : Fin 3 ↪ SK := ⟨![w 0, pw 1, w 4], by decide⟩

def pop1 : Unit → TM2.Stmt (fun _ : SK => Bool) Unit (Option Bool)
  | () => .pop fuel (fun _ b => b) .halt

def monus : Unit → TM2.Stmt (fun _ : SK => Bool) Unit (Option Bool)
  | () => .pop (w 3) (fun _ b => b)
      (.branch (fun v => v.isSome) (.pop fuel (fun v _ => v) (.goto (fun _ => ()))) .halt)

def push1 : Unit → TM2.Stmt (fun _ : SK => Bool) Unit (Option Bool)
  | () => .push (pw 0) (fun _ => true) .halt

def pInj : PS ↪ SK := ⟨Sum.inr, Sum.inr_injective⟩
def powerProg := fun l => stackStmt pInj (MatrixWeightedPower.program l)

inductive CL where
  | loop | done
  deriving DecidableEq, Fintype

def clrBase : CL → TM2.Stmt (fun _ : SK => Bool) CL (Unit × Option Bool)
  | .loop => BitMachineClearBank.clearStep (pw 1) CL.loop CL.done
  | .done => .halt

/-! ## The fixed controller -/

def k8 := (((), none) : Unit × Option Bool)
def q7 := BitMachineRawSequence.program powerProg clrBase CL.loop (false, false) k8
def k7 := ((false, false), k8)
def q6 := BitMachineRawSequence.program (copyProgram sB) q7
  (BitMachineRawSequence.leftLabel (Sum.inr MatrixWeightedPower.Admin.test))
  (none : Option Bool) k7
def k6 := ((none : Option Bool), k7)
def q5 := BitMachineRawSequence.program push1 q6
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool) k6
def k5 := ((none : Option Bool), k6)
def q4 := BitMachineRawSequence.program monus q5
  (BitMachineRawSequence.leftLabel ()) (none : Option Bool) k5
def k4 := ((none : Option Bool), k5)
def q3 := BitMachineRawSequence.program (copyProgram sP) q4
  (BitMachineRawSequence.leftLabel ()) (none : Option Bool) k4
def k3 := ((none : Option Bool), k4)
def q2 := BitMachineRawSequence.program pop1 q3
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool) k3
def k2 := ((none : Option Bool), k3)
/-- The single fixed stride controller. -/
def program := BitMachineRawSequence.program (copyProgram sS) q2
  (BitMachineRawSequence.leftLabel ()) (none : Option Bool) k2
def initial := ((none : Option Bool), k2)

/-! ## Banks -/

def S0 (b s p : ℕ) : SK → List Bool :=
  Sum.elim (![List.replicate b true, List.replicate s true, List.replicate p true, [], []] :
    Fin 5 → List Bool) (fun _ => [])

def S1 (b s p : ℕ) : SK → List Bool := Function.update (S0 b s p) fuel (List.replicate s true)
def S2 (b s p : ℕ) : SK → List Bool :=
  Function.update (S1 b s p) fuel (List.replicate (s - 1) true)
def S3 (b s p : ℕ) : SK → List Bool := Function.update (S2 b s p) (w 3) (List.replicate p true)
def S4 (b s p : ℕ) : SK → List Bool :=
  Function.update (Function.update (S3 b s p) (w 3) []) fuel (List.replicate (s - 1 - p) true)
def S5 (b s p : ℕ) : SK → List Bool := Function.update (S4 b s p) (pw 0) [true]
def S6 (b s p : ℕ) : SK → List Bool := Function.update (S5 b s p) (pw 1) (List.replicate b true)
def S7 (b s p : ℕ) : SK → List Bool :=
  Function.update (Function.update (S6 b s p) (pw 0) (List.replicate (b ^ (s - 1 - p)) true))
    fuel []
def S8 (b s p : ℕ) : SK → List Bool := Function.update (S7 b s p) (pw 1) []

/-- The exact exit bank: operands retained, accumulator `b^(s-1-p)`, all
other cells blank. -/
def exitBank (b s p : ℕ) : SK → List Bool :=
  Function.update (S0 b s p) (pw 0) (List.replicate (b ^ (s - 1 - p)) true)

theorem S8_eq (b s p : ℕ) : S8 b s p = exitBank b s p := by
  funext k
  rcases k with k | (k | k)
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl
  · fin_cases k; rfl

/-! ## Phases -/

theorem f1 (b s p : ℕ) :
    ((advance (copyProgram sS))^[2 * s + 2])
      (⟨some BitMachineCopy.Label.scan, none, S0 b s p⟩ : TM2.Cfg (fun _ : SK => Bool) _ _) =
      ⟨none, none, S1 b s p⟩ := by
  have h := FamilyRowGeneric.copy_blank sS (S0 b s p) (by rfl) (by rfl)
  have hsrc : S0 b s p (sS 0) = List.replicate s true := rfl
  rw [hsrc, List.length_replicate] at h
  exact h

theorem f2 (b s p : ℕ) :
    ∃ v, ((advance pop1)^[1])
      (⟨some (), none, S1 b s p⟩ : TM2.Cfg (fun _ : SK => Bool) _ _) =
      ⟨none, v, S2 b s p⟩ := by
  refine ⟨(List.replicate s true).head?, ?_⟩
  have h : S1 b s p fuel = List.replicate s true := rfl
  simp only [Function.iterate_one, advance, TM2.step, TM2.stepAux, pop1, h,
    Option.getD_some, List.tail_replicate]
  rfl

theorem f3 (b s p : ℕ) :
    ((advance (copyProgram sP))^[2 * p + 2])
      (⟨some BitMachineCopy.Label.scan, none, S2 b s p⟩ : TM2.Cfg (fun _ : SK => Bool) _ _) =
      ⟨none, none, S3 b s p⟩ := by
  have h := FamilyRowGeneric.copy_blank sP (S2 b s p) (by rfl) (by rfl)
  have hsrc : S2 b s p (sP 0) = List.replicate p true := rfl
  rw [hsrc, List.length_replicate] at h
  exact h

theorem monus_run (S : SK → List Bool) (k n : ℕ) (v : Option Bool)
    (h3 : S (w 3) = List.replicate k true) (hf : S fuel = List.replicate n true) :
    ∃ v', ((advance monus)^[k + 1]) (⟨some (), v, S⟩ : TM2.Cfg (fun _ : SK => Bool) _ _) =
      ⟨none, v', Function.update (Function.update S (w 3) []) fuel
        (List.replicate (n - k) true)⟩ := by
  have hne : fuel ≠ w 3 := by decide
  induction k generalizing S n v with
  | zero =>
      refine ⟨none, ?_⟩
      have h3' : S (w 3) = [] := by simpa using h3
      have hu : Function.update (Function.update S (w 3) []) fuel
          (List.replicate (n - 0) true) = S := by
        funext j
        by_cases hj : j = fuel
        · subst hj
          rw [Function.update_self, Nat.sub_zero, hf]
        · rw [Function.update_of_ne hj]
          by_cases hj3 : j = w 3
          · subst hj3
            rw [Function.update_self, h3']
          · rw [Function.update_of_ne hj3]
      rw [hu, Function.iterate_one]
      have hS : Function.update S (w 3) (S (w 3)).tail = S :=
        Function.update_eq_self_iff.mpr (by rw [h3']; rfl)
      simp only [advance, TM2.step, TM2.stepAux, monus, Option.getD_some, h3',
        List.head?_nil, Option.isSome_none, cond_false]
      rw [← h3', hS]
  | succ k ih =>
      have hstep : advance monus (⟨some (), v, S⟩ : TM2.Cfg (fun _ : SK => Bool) _ _) =
          ⟨some (), some true, Function.update (Function.update S (w 3)
            (List.replicate k true)) fuel (List.replicate (n - 1) true)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, monus, h3, hf, List.replicate_succ,
          Function.update_of_ne hne, List.tail_replicate]
      obtain ⟨v', hv'⟩ := ih (Function.update (Function.update S (w 3)
          (List.replicate k true)) fuel (List.replicate (n - 1) true)) (n - 1) (some true)
        (by rw [Function.update_of_ne hne.symm, Function.update_self])
        (by rw [Function.update_self])
      refine ⟨v', ?_⟩
      rw [Function.iterate_succ_apply, hstep, hv']
      congr 1
      funext j
      by_cases hj : j = fuel
      · subst hj
        simp only [Function.update_self]
        congr 1
        omega
      · by_cases hj3 : j = w 3
        · subst hj3
          simp only [Function.update_of_ne hj, Function.update_self]
        · simp only [Function.update_of_ne hj, Function.update_of_ne hj3]

theorem f4 (b s p : ℕ) :
    ∃ v, ((advance monus)^[p + 1])
      (⟨some (), none, S3 b s p⟩ : TM2.Cfg (fun _ : SK => Bool) _ _) =
      ⟨none, v, S4 b s p⟩ := by
  obtain ⟨v, hv⟩ := monus_run (S3 b s p) p (s - 1) none rfl rfl
  exact ⟨v, hv⟩

theorem f5 (b s p : ℕ) :
    ((advance push1)^[1])
      (⟨some (), none, S4 b s p⟩ : TM2.Cfg (fun _ : SK => Bool) _ _) =
      ⟨none, none, S5 b s p⟩ := by
  have h : S4 b s p (pw 0) = [] := rfl
  simp only [Function.iterate_one, advance, TM2.step, TM2.stepAux, push1, h,
    Option.getD_some]
  rfl

theorem f6 (b s p : ℕ) :
    ((advance (copyProgram sB))^[2 * b + 2])
      (⟨some BitMachineCopy.Label.scan, none, S5 b s p⟩ : TM2.Cfg (fun _ : SK => Bool) _ _) =
      ⟨none, none, S6 b s p⟩ := by
  have h := FamilyRowGeneric.copy_blank sB (S5 b s p) (by rfl) (by rfl)
  have hsrc : S5 b s p (sB 0) = List.replicate b true := rfl
  rw [hsrc, List.length_replicate] at h
  exact h

theorem f7 (b s p : ℕ) :
    ∃ t ≤ MatrixWeightedPower.powerBound b (s - 1 - p),
      ((advance powerProg)^[t])
        (⟨some (Sum.inr MatrixWeightedPower.Admin.test), (false, false), S6 b s p⟩ :
          TM2.Cfg (fun _ : SK => Bool) _ _) =
        ⟨none, (false, false), S7 b s p⟩ := by
  obtain ⟨t, ht, hr⟩ := MatrixWeightedPower.power_run b (s - 1 - p)
  have hrun := BitMachineStackRun.run pInj (S6 b s p) MatrixWeightedPower.program
    (MatrixWeightedPower.cfg (some (.inr .test)) (false, false)
      (List.replicate 1 true) (List.replicate b true) [] (List.replicate (s - 1 - p) true)) t
  unfold MatrixWeightedPower.run at hr
  rw [hr] at hrun
  have hs : bank pInj (S6 b s p)
      (MatrixWeightedPower.cfg (some (.inr .test)) (false, false)
        (List.replicate 1 true) (List.replicate b true) []
        (List.replicate (s - 1 - p) true)).stk = S6 b s p := by
    apply bank_eq_self
    intro k
    rcases k with k | k
    · fin_cases k <;> rfl
    · fin_cases k; rfl
  have hf : bank pInj (S6 b s p)
      (MatrixWeightedPower.cfg none (false, false) (List.replicate (b ^ (s - 1 - p)) true)
        (List.replicate b true) [] []).stk = S7 b s p := by
    funext j
    rcases j with j | k
    · rw [bank_outside]
      · fin_cases j <;> rfl
      · rintro ⟨k, hk⟩
        cases hk
    · rw [show (Sum.inr k : SK) = pInj k from rfl, bank_at]
      rcases k with k | k
      · fin_cases k <;> rfl
      · fin_cases k; rfl
  simp only [MatrixWeightedPower.cfg] at hs hf
  simp only [stackCfg, MatrixWeightedPower.cfg, hs, hf] at hrun
  exact ⟨t, ht, hrun⟩

theorem f8 (b s p : ℕ) :
    ((advance clrBase)^[b + 2])
      (⟨some CL.loop, ((), none), S7 b s p⟩ : TM2.Cfg (fun _ : SK => Bool) _ _) =
      ⟨none, ((), none), S8 b s p⟩ := by
  have hp : clrBase CL.loop = BitMachineClearBank.clearStep (pw 1) CL.loop CL.done := rfl
  have h := BitMachineClearBank.clear_one_run clrBase (pw 1) CL.loop CL.done hp () (S7 b s p)
  have hv : S7 b s p (pw 1) = List.replicate b true := rfl
  rw [hv, List.length_replicate] at h
  rw [show b + 2 = (b + 1) + 1 by omega, Function.iterate_succ_apply', h]
  rfl

/-! ## The composite -/

def strideBound (b s p : ℕ) : ℕ :=
  (2 * s + 2) + 1 + (2 * p + 2) + (p + 1) + 1 + (2 * b + 2) +
    MatrixWeightedPower.powerBound b (s - 1 - p) + (b + 2) + 7

theorem stride_run (b s p : ℕ) :
    ∃ t ≤ strideBound b s p, ∃ v,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), initial,
          S0 b s p⟩ : TM2.Cfg (fun _ : SK => Bool) _ _) =
        ⟨none, v, exitBank b s p⟩ := by
  rw [← S8_eq]
  obtain ⟨t7, ht7, h7⟩ := f7 b s p
  obtain ⟨u7, hu7, r7⟩ := BitMachineRawSequence.runs powerProg clrBase
    (Sum.inr MatrixWeightedPower.Admin.test) CL.loop (false, false) (false, false) k8 k8
    (S6 b s p) (S7 b s p) (S8 b s p) t7 (b + 2) h7 (f8 b s p)
  obtain ⟨u6, hu6, r6⟩ := BitMachineRawSequence.runs (copyProgram sB) q7
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel (Sum.inr MatrixWeightedPower.Admin.test))
    none none k7 ((false, false), k8) (S5 b s p) (S6 b s p) (S8 b s p) (2 * b + 2) u7
    (f6 b s p) r7
  obtain ⟨u5, hu5, r5⟩ := BitMachineRawSequence.runs push1 q6 ()
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none none k6
    (none, ((false, false), k8)) (S4 b s p) (S5 b s p) (S8 b s p) 1 u6 (f5 b s p) r6
  obtain ⟨v4, h4⟩ := f4 b s p
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs monus q5 ()
    (BitMachineRawSequence.leftLabel ()) none v4 k5
    (none, (none, ((false, false), k8))) (S3 b s p) (S4 b s p) (S8 b s p) (p + 1) u5 h4 r5
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs (copyProgram sP) q4
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel ()) none none k4
    (none, (none, (none, ((false, false), k8)))) (S2 b s p) (S3 b s p) (S8 b s p)
    (2 * p + 2) u4 (f3 b s p) r4
  obtain ⟨v2, h2⟩ := f2 b s p
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs pop1 q3 ()
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none v2 k3
    (none, (none, (none, (none, ((false, false), k8))))) (S1 b s p) (S2 b s p) (S8 b s p)
    1 u3 h2 r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs (copyProgram sS) q2
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel ()) none none k2
    (none, (none, (none, (none, (none, ((false, false), k8)))))) (S0 b s p) (S1 b s p)
    (S8 b s p) (2 * s + 2) u2 (f1 b s p) r2
  refine ⟨u1, ?_, _, r1⟩
  unfold strideBound
  omega

#print axioms monus_run
#print axioms f7
#print axioms S8_eq
#print axioms stride_run

end
end EthInapproximability.CurrentPaper.EntryStride
