import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Unit 3, segment (1): a physical producer of the unary repetition factor
`r = ParameterizedCanonicalSource.rep L m = outerWidth L / sourceQ0 (Fin (4 width L)) (Fin m)`.

Bank `RK = Fin 13 ⊕ LS`, `LS = ETHParameterScaleMachineLogCopy.Stack` (one region for the admitted
Paper B copy-then-clog call). Inputs: `u s` (cell 0), `u q₂` (cell 1), `u m` (cell 2); everything
else blank.

ONE fixed program `repProg` (seven parts, production `BitMachineRawSequence` handoffs):
1. one step pushing twelve marks into cell 3 (`u 12`, a fixed constant of the machine);
2. the admitted `MatrixStage4ScalarPreparationOps.multiplyProgram` on (cell 3, cell 0) into cell 4:
   `u (12 * s)`;
3. the same admitted multiplier on (cell 4, cell 2) into the log region's source: `u (12 * s * m)`;
4. the admitted copy-then-clog `ETHParameterScaleMachineLogCopy.program` on the log region:
   `u (clog 2 (12 * s * m))` (source kept);
5. the admitted `MatrixStage4ScalarPreparationOps.unaryPowerProgram` reading its exponent from the
   log output cell (retained), writing `u (2 ^ clog 2 (12 * s * m))` into cell 9;
6. the admitted copy `MatrixStage4ScalarPreparationOps.copyProgram` of `u q₂` into cell 10;
7. the admitted `MatrixUnaryDivision.program` embedded on (10, 9, 6, 11, 12, 7): quotient
   `u (q₂ / 2 ^ clog 2 (12 * s * m))` in cell 12, remainder in cell 11, divisor kept in cell 9.

Every cell of `Fin 13` is stated exactly at the exit; the log region is the admitted machine's
`afterLog` bank with its existential configuration `c` (named residue) whose source and output
cells are stated. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.RepProducer

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

abbrev LS := ETHParameterScaleMachineLogCopy.Stack
abbrev RK := Fin 13 ⊕ LS

def u (n : ℕ) : List Bool := List.replicate n true

def sC : RK := .inl 0
def qC : RK := .inl 1
def mC : RK := .inl 2
def tC : RK := .inl 3
def wC : RK := .inl 4
def zC : RK := .inl 5
def a6 : RK := .inl 6
def a7 : RK := .inl 7
def a8 : RK := .inl 8
def pC : RK := .inl 9
def dC : RK := .inl 10
def remC : RK := .inl 11
def rC : RK := .inl 12
def srcL : RK := .inr (.inl 0)
def outL : RK := .inr (ETHParameterScaleMachineLogCopy.logStack
  ETHParameterScaleMachineLogCopy.logMachine.output)

def ιL : LS ↪ RK := ⟨Sum.inr, fun _ _ h => Sum.inr_injective h⟩

/-- Start bank: `u s`, `u q₂`, `u m` in cells 0, 1, 2; everything else blank. -/
def R0 (s q₂ m : ℕ) : RK → List Bool :=
  Sum.elim ![u s, u q₂, u m, [], [], [], [], [], [], [], [], [], []] (fun _ => [])

/-- The exact `Fin 13` part of the exit bank. -/
def fin1 (s q₂ m : ℕ) : Fin 13 → List Bool :=
  ![u s, u q₂, u m, u 12, u (12 * s), [], [], [], [],
    u (2 ^ Nat.clog 2 (12 * s * m)), [],
    u (q₂ % 2 ^ Nat.clog 2 (12 * s * m)), u (q₂ / 2 ^ Nat.clog 2 (12 * s * m))]

/-! ### Embeddings -/

def ιM1 : Fin 6 ↪ RK := ⟨![tC, sC, a6, a7, a8, wC], by
  intro x y h; fin_cases x <;> fin_cases y <;> simp_all [tC, sC, a6, a7, a8, wC]⟩
def ιM2 : Fin 6 ↪ RK := ⟨![wC, mC, a6, a7, a8, srcL], by
  intro x y h; fin_cases x <;> fin_cases y <;> simp_all [wC, mC, a6, a7, a8, srcL]⟩

def powF : MatrixUnaryPower.Stack → RK
  | .inl 0 => pC
  | .inl 1 => a6
  | .inl _ => a7
  | .inr () => outL

def ιP : MatrixUnaryPower.Stack ↪ RK := ⟨powF, by
  intro x y h
  rcases x with x | x <;> rcases y with y | y
  · fin_cases x <;> fin_cases y <;> simp_all [powF, pC, a6, a7]
  · cases y; fin_cases x <;> simp_all [powF, pC, a6, a7, outL]
  · cases x; fin_cases y <;> simp_all [powF, pC, a6, a7, outL]
  · cases x; cases y; rfl⟩

def ιC : Fin 3 ↪ RK := ⟨![qC, dC, zC], by
  intro x y h; fin_cases x <;> fin_cases y <;> simp_all [qC, dC, zC]⟩
def ιD : Fin 6 ↪ RK := ⟨![dC, pC, a6, remC, rC, a7], by
  intro x y h; fin_cases x <;> fin_cases y <;> simp_all [dC, pC, a6, remC, rC, a7]⟩

/-! ### The embedded division -/

def divProgram (ι : Fin 6 ↪ RK) :
    MatrixUnaryDivision.Label → TM2.Stmt (fun _ : RK => Bool) MatrixUnaryDivision.Label Bool :=
  fun l => stackStmt ι (MatrixUnaryDivision.program l)

theorem div_run (ι : Fin 6 ↪ RK) (S : RK → List Bool) (n m : ℕ) (hm : 0 < m)
    (h0 : S (ι 0) = u n) (h1 : S (ι 1) = u m) (h2 : S (ι 2) = []) (h3 : S (ι 3) = [])
    (h4 : S (ι 4) = []) (h5 : S (ι 5) = []) :
    ((advance (divProgram ι))^[MatrixUnaryDivision.exactTime n m])
        (⟨some .start, false, S⟩ : TM2.Cfg (fun _ : RK => Bool) MatrixUnaryDivision.Label Bool) =
      ⟨none, false, Function.update (Function.update (Function.update S (ι 0) []) (ι 3)
        (u (n % m))) (ι 4) (u (n / m))⟩ := by
  let c := MatrixUnaryDivision.cfg (some .start) false (u n) (u m) [] [] [] []
  have hstart : stackCfg ι S c =
      (⟨some .start, false, S⟩ : TM2.Cfg (fun _ : RK => Bool) MatrixUnaryDivision.Label Bool) := by
    dsimp [stackCfg, c, MatrixUnaryDivision.cfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [h0, h1, h2, h3, h4, h5]
  have hrun := BitMachineStackRun.run ι S MatrixUnaryDivision.program c
    (MatrixUnaryDivision.exactTime n m)
  rw [hstart] at hrun
  change _ = stackCfg ι S (MatrixUnaryDivision.run (MatrixUnaryDivision.exactTime n m) c) at hrun
  rw [show c = MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
      (List.replicate m true) [] [] [] [] from rfl, MatrixUnaryDivision.division_run n m hm] at hrun
  refine hrun.trans ?_
  dsimp [stackCfg, MatrixUnaryDivision.cfg]
  congr 1
  have hloc : (![[], List.replicate m true, [], List.replicate (n % m) true,
      List.replicate (n / m) true, []] : Fin 6 → List Bool) =
      Function.update (Function.update (Function.update (fun k : Fin 6 => S (ι k)) 0 []) 3
        (u (n % m))) 4 (u (n / m)) := by
    funext k
    fin_cases k <;> simp [h1, h2, h5, u]
  rw [hloc, bank_update, bank_update, bank_update, bank_restrict]

/-! ### The log region -/

def region (n : ℕ) : LS → List Bool := fun x => if x = .inl 0 then u n else []

theorem start_stk (q : List Bool) :
    (ETHParameterScaleMachineLogCopy.start q).stk = fun x => if x = .inl 0 then q else [] := by
  change BitMachineStackEmbedding.bank ETHParameterScaleMachineLogCopy.copyStack (fun _ => [])
    (BitMachineCopy.cfg (some .scan) none q [] []).stk = _
  funext k
  by_cases hk : ∃ p : Fin 3, ETHParameterScaleMachineLogCopy.copyStack p = k
  · obtain ⟨p, rfl⟩ := hk
    rw [BitMachineStackEmbedding.bank_at]
    fin_cases p <;> simp [ETHParameterScaleMachineLogCopy.copyStack, BitMachineCopy.cfg]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hk]
    have hne : k ≠ (.inl (0 : Fin 1) : LS) := by
      intro he
      exact hk ⟨0, by simpa [ETHParameterScaleMachineLogCopy.copyStack] using he.symm⟩
    simp [hne]

def logP := fun l => stackStmt ιL (ETHParameterScaleMachineLogCopy.program l)

abbrev logCtl := ETHParameterScaleMachineLogCopy.copyControl none

def logBd (n : ℕ) : ℕ := 2 * n + 2 + (UnaryBinaryEncoding.coefficient + 6) * (n + 1) ^ 2

theorem log_lift (W : RK → List Bool) (n : ℕ) (hW : ∀ x : LS, W (.inr x) = region n x) :
    ∃ t ≤ logBd n, ∃ c : ETHParameterScaleMachineLogCopy.logMachine.Config,
      ((advance logP)^[t])
          (⟨some (.inl .scan), logCtl, W⟩ : TM2.Cfg (fun _ : RK => Bool) _ _) =
        ⟨none, (none, c.var),
          bank ιL W (ETHParameterScaleMachineLogCopy.afterLog (u n) c).stk⟩ ∧
      (ETHParameterScaleMachineLogCopy.afterLog (u n) c).stk
          (ETHParameterScaleMachineLogCopy.logStack
            ETHParameterScaleMachineLogCopy.logMachine.output) = u (Nat.clog 2 n) ∧
      (ETHParameterScaleMachineLogCopy.afterLog (u n) c).stk (.inl 0) = u n := by
  obtain ⟨t, c, ht, hr, hh, ho⟩ := ETHParameterScaleMachineLogCopy.copied_log_run n
  have hs := BitMachineStackRun.run ιL W ETHParameterScaleMachineLogCopy.program
    (ETHParameterScaleMachineLogCopy.start (u n)) t
  change _ = stackCfg ιL W (ETHParameterScaleMachineLogCopy.run t _) at hs
  have hr' : ETHParameterScaleMachineLogCopy.run t (ETHParameterScaleMachineLogCopy.start (u n)) =
      ETHParameterScaleMachineLogCopy.afterLog (u n) c := hr
  rw [hr'] at hs
  have hb : bank ιL W (ETHParameterScaleMachineLogCopy.start (u n)).stk = W := by
    apply bank_eq_self
    intro x
    rw [start_stk]
    show (if x = .inl 0 then u n else []) = W (.inr x)
    rw [hW]
    rfl
  have hst : stackCfg ιL W (ETHParameterScaleMachineLogCopy.start (u n)) =
      (⟨some (.inl .scan), logCtl, W⟩ : TM2.Cfg (fun _ : RK => Bool) _ _) := by
    simp only [stackCfg]
    rw [hb]
    rfl
  rw [hst] at hs
  have hl : (ETHParameterScaleMachineLogCopy.afterLog (u n) c).l = none := by
    simp [ETHParameterScaleMachineLogCopy.afterLog, BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, hh]
  refine ⟨t, by unfold logBd; exact ht, c, ?_, ?_, ?_⟩
  · refine hs.trans ?_
    simp only [stackCfg]
    rw [hl]
    rfl
  · exact (ETHParameterScaleMachineLogCopy.afterLog_output n c).trans ho
  · exact ETHParameterScaleMachineLogCopy.afterLog_source n c

/-! ### The program -/

def push12 : Unit → TM2.Stmt (fun _ : RK => Bool) Unit Bool := fun _ =>
  TM2.Stmt.push tC (fun _ => true) <| TM2.Stmt.push tC (fun _ => true) <|
  TM2.Stmt.push tC (fun _ => true) <| TM2.Stmt.push tC (fun _ => true) <|
  TM2.Stmt.push tC (fun _ => true) <| TM2.Stmt.push tC (fun _ => true) <|
  TM2.Stmt.push tC (fun _ => true) <| TM2.Stmt.push tC (fun _ => true) <|
  TM2.Stmt.push tC (fun _ => true) <| TM2.Stmt.push tC (fun _ => true) <|
  TM2.Stmt.push tC (fun _ => true) <| TM2.Stmt.push tC (fun _ => true) <| TM2.Stmt.halt

theorem push12_run (S : RK → List Bool) (v : Bool) (h : S tC = []) :
    ((advance push12)^[1]) (⟨some (), v, S⟩ : TM2.Cfg (fun _ : RK => Bool) _ _) =
      ⟨none, v, Function.update S tC (u 12)⟩ := by
  show (⟨none, v, _⟩ : TM2.Cfg (fun _ : RK => Bool) Unit Bool) = _
  congr 1
  funext y
  by_cases hy : y = tC
  · subst hy
    simp [h, u, List.replicate]
  · simp [Function.update_of_ne hy]

def mul1 := MatrixStage4ScalarPreparationOps.multiplyProgram ιM1
def mul2 := MatrixStage4ScalarPreparationOps.multiplyProgram ιM2
def powP := MatrixStage4ScalarPreparationOps.unaryPowerProgram ιP
def cpQ := MatrixStage4ScalarPreparationOps.copyProgram ιC
def divP := divProgram ιD

abbrev powCtl : MatrixUnaryPower.Control := ((false, false), none)

def r1 := BitMachineRawSequence.program push12 mul1 MatrixAddressMachine.Label.outer false false
def k1 := (false, false)
def r2 := BitMachineRawSequence.program r1 mul2 MatrixAddressMachine.Label.outer k1 false
def k2 := (k1, false)
def r3 := BitMachineRawSequence.program r2 logP (.inl .scan) k2 logCtl
def k3 := (k2, logCtl)
def r4 := BitMachineRawSequence.program r3 powP (.inr false) k3 powCtl
def k4 := (k3, powCtl)
def r5 := BitMachineRawSequence.program r4 cpQ BitMachineCopy.Label.scan k4 (none : Option Bool)
def k5 := (k4, (none : Option Bool))
/-- The repetition-factor producer: ONE fixed program. -/
def repProg := BitMachineRawSequence.program r5 divP MatrixUnaryDivision.Label.start k5 false
def repCtl := (k5, false)
def labelOfP {L σ : Type*} {K : Type*} (_P : L → TM2.Stmt (fun _ : K => Bool) L σ)
    (l : L) : L := l
def repStart := labelOfP repProg (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
  (leftLabel ()))))))

end

end Paper2.RepProducer
