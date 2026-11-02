import EthInapproximability.CurrentPaper.G5eLevel0
import EthInapproximability.CurrentPaper.Emission

/-!
# Keeping the input `k` and emitting unary `y_k` (private lane owner:b-g5-5, segment 3, part a)

The admitted `Emission.emitProgram` subtracts a copy of master `K` (= `kValue M n`, dead scratch in the
k-input program) from consumer raw word 2 (unary `y_k + k`), so it is not reusable when `k` is an
input. Here the input `k` is KEPT: over the bank `H8 = KShell.H5 ⊕ Fin 3` (cells `zc 0` saved `k`,
`zc 1` blank copy temporary, `zc 2` output), ONE fixed program

1. copies the fuel cell (unary `k`, the input) into `zc 0` (charged copy, `2k + 2` steps);
2. runs an arbitrary program `K` over `H5` lifted to `H8` (the region lemma
   `WeightedRawWords.region_run`, admitted);
3. copies consumer raw word 2 into `zc 2` (charged copy);
4. pops `zc 0` and `zc 2` together until `zc 0` is empty (`k + 1` steps), leaving unary `y` in `zc 2`.

`yk_core_run` is generic in the lifted program `K` (hypothesis: `K` runs from the start bank to a bank
whose consumer raw word 2 is `replicate (y + k) true`). The instance with `K = G5cKInput.kProgram M c`
is in `G5eYk`.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5eYkCore

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

abbrev H8 := KShell.H5 ⊕ Fin 3

instance decH5' : DecidableEq KShell.H5 := inferInstance
instance decH8 : DecidableEq H8 := inferInstance

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Prep OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP StepP
open Level0Install
open KShell (H5 fuel ext5)

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000


def i8 : H5 ↪ H8 := ⟨Sum.inl, Sum.inl_injective⟩
def zc (i : Fin 3) : H8 := .inr i
def ext8 (Y : H5 → List Bool) (D : Fin 3 → List Bool) : H8 → List Bool := Sum.elim Y D

def lift8 {L V : Type} (P : L → TM2.Stmt (fun _ : H5 => Bool) L V) :
    L → TM2.Stmt (fun _ : H8 => Bool) L V :=
  fun l => stackStmt i8 (P l)

theorem bank_ext8 (X Y : H5 → List Bool) (D : Fin 3 → List Bool) :
    bank i8 (ext8 X D) Y = ext8 Y D := by
  funext x
  rcases x with x | x
  · exact bank_at i8 (ext8 X D) Y x
  · rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
    rfl

theorem lift8_run {L V : Type} (P : L → TM2.Stmt (fun _ : H5 => Bool) L V)
    (l l' : Option L) (v v' : V) (X Y : H5 → List Bool) (D : Fin 3 → List Bool) (t : ℕ)
    (h : ((advance P)^[t]) (⟨l, v, X⟩ : TM2.Cfg (fun _ : H5 => Bool) L V) = ⟨l', v', Y⟩) :
    ((advance (lift8 P))^[t]) (⟨l, v, ext8 X D⟩ : TM2.Cfg (fun _ : H8 => Bool) L V) =
      ⟨l', v', ext8 Y D⟩ := by
  have r := WeightedRawWords.region_run i8 P ⟨l, v, X⟩ ⟨l', v', Y⟩ t h (ext8 X D) (fun _ => rfl)
  dsimp only at r
  rw [bank_ext8] at r
  exact r

/-! ## Copies with the blank temporary `zc 1` -/

def sl8 (a b : H8) (h1 : a ≠ b) (h2 : a ≠ zc 1) (h3 : b ≠ zc 1) : Fin 3 ↪ H8 where
  toFun
    | 0 => a
    | 1 => b
    | 2 => zc 1
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all

def cp8 (a b : H8) (h1 : a ≠ b) (h2 : a ≠ zc 1) (h3 : b ≠ zc 1) :=
  MatrixStage4ScalarPreparationOps.copyProgram (sl8 a b h1 h2 h3)

theorem cp8_run (a b : H8) (h1 : a ≠ b) (h2 : a ≠ zc 1) (h3 : b ≠ zc 1)
    (S : H8 → List Bool) (hb : S b = []) (ht : S (zc 1) = []) :
    ((advance (cp8 a b h1 h2 h3))^[2 * (S a).length + 2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : H8 => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update S b (S a)⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run (sl8 a b h1 h2 h3) S ht
  have e0 : (sl8 a b h1 h2 h3) 0 = a := rfl
  have e1 : (sl8 a b h1 h2 h3) 1 = b := rfl
  rw [e0, e1, hb, List.append_nil] at h
  exact h

/-- The fuel cell (the input `k`). -/
abbrev fuel8 : H8 := .inl fuel
/-- Consumer raw word 2 (unary `y + k` at the exit of the shell). -/
abbrev raw2 : H8 := .inl (.inl (RoundInstall.consH (WeightedRawWords.consRaw 2)))

def cpFuel := cp8 fuel8 (zc 0) (by intro h; cases h) (by intro h; cases h)
  (by intro h; cases h)
def cpRaw2 := cp8 raw2 (zc 2) (by intro h; cases h) (by intro h; cases h)
  (by intro h; cases h)

/-! ## Charged subtraction of the kept `k` -/

def subP : Unit → TM2.Stmt (fun _ : H8 => Bool) Unit (Option Bool) :=
  fun _ => .pop (zc 0) (fun _ b => b)
    (.branch Option.isSome (.pop (zc 2) (fun v _ => v) (.goto (fun _ => ()))) .halt)

theorem z02 : zc 0 ≠ zc 2 := by intro h; cases h
theorem z20 : zc 2 ≠ zc 0 := by intro h; cases h

theorem sub_run : ∀ (m : ℕ) (Y : H8 → List Bool) (R : List Bool) (v : Option Bool),
    Y (zc 0) = List.replicate m true → Y (zc 2) = List.replicate m true ++ R →
    ((advance subP)^[m + 1]) (⟨some (), v, Y⟩ : TM2.Cfg (fun _ : H8 => Bool) Unit (Option Bool)) =
      ⟨none, none, Function.update (Function.update Y (zc 0) []) (zc 2) R⟩ := by
  intro m
  induction m with
  | zero =>
    intro Y R v h0 h2
    simp only [List.replicate_zero, List.nil_append] at h0 h2
    simp only [Nat.zero_add, Function.iterate_one]
    simp only [advance, TM2.step, subP, TM2.stepAux, h0, List.head?_nil, List.tail_nil,
      Option.isSome_none, cond_false, Option.getD_some]
    congr 1
    funext y
    simp only [Function.update_apply]
    split_ifs <;> simp_all [zc]
  | succ m ih =>
    intro Y R v h0 h2
    rw [Function.iterate_succ_apply]
    have hstep : advance subP (⟨some (), v, Y⟩ : TM2.Cfg (fun _ : H8 => Bool) Unit (Option Bool)) =
        ⟨some (), some true, Function.update (Function.update Y (zc 0) (List.replicate m true)) (zc 2)
          (List.replicate m true ++ R)⟩ := by
      simp only [advance, TM2.step, subP, TM2.stepAux, h0, List.replicate_succ, List.head?_cons,
        List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
      rw [Function.update_of_ne z20, h2]
      simp only [List.replicate_succ, List.cons_append, List.tail_cons]
    rw [hstep, ih _ R (some true) (by rw [Function.update_of_ne z02, Function.update_self])
      (by rw [Function.update_self])]
    congr 1
    funext y
    simp only [Function.update_apply]
    split_ifs <;> simp_all [zc]

/-! ## The program -/

/-- ONE fixed program around an arbitrary `H5` program `K` (start label `k0`, start control `v0`):
copy the fuel cell, run `K` lifted, copy raw word 2, subtract the kept `k`. -/
def ykProgram {LK VK : Type} (K : LK → TM2.Stmt (fun _ : H5 => Bool) LK VK) (k0 : LK) (v0 : VK) :=
  BitMachineRawSequence.program cpFuel
    (BitMachineRawSequence.program (lift8 K)
      (BitMachineRawSequence.program cpRaw2 subP () none none)
      (BitMachineRawSequence.leftLabel .scan) v0 (none, none))
    (BitMachineRawSequence.leftLabel k0) none (v0, (none, none))

/-- **Segment 3a (generic).** If `K` runs from `ext5 X (unary k)` to `ext5 Y []` with
`Y (consumer raw word 2) = unary (y + k)`, the fixed program `ykProgram K` runs from
`ext8 (ext5 X (unary k)) blank` to `ext8 (ext5 Y' []) ![[], [], unary y]` with `Y'` equal to `Y`
except raw word 2 (which the copy reads without consuming: it is unchanged), within
`(2k+2) + tK + (2(y+k)+2) + (k+1) + 3`. -/
theorem yk_core_run {LK VK : Type} (K : LK → TM2.Stmt (fun _ : H5 => Bool) LK VK) (k0 : LK)
    (v0 v1 : VK) (X Y : H4 → List Bool) (k y tK : ℕ)
    (hK : ((advance K)^[tK]) (⟨some k0, v0, ext5 X (List.replicate k true)⟩ :
        TM2.Cfg (fun _ : H5 => Bool) LK VK) = ⟨none, v1, ext5 Y []⟩)
    (hY : Y (RoundInstall.consH (WeightedRawWords.consRaw 2)) = List.replicate (y + k) true) :
    ∃ t ≤ (2 * k + 2) + tK + (2 * (y + k) + 2) + (k + 1) + 3,
      ((advance (ykProgram K k0 v0))^[t])
        ⟨some (BitMachineRawSequence.leftLabel .scan), (none, (v0, (none, none))),
          ext8 (ext5 X (List.replicate k true)) (fun _ => [])⟩ =
        ⟨none, (none, (v0, (none, none))),
          ext8 (ext5 Y []) ![[], [], List.replicate y true]⟩ := by
  -- 1. copy the fuel cell into zc 0
  have s1 := cp8_run fuel8 (zc 0) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (ext8 (ext5 X (List.replicate k true)) (fun _ => [])) rfl rfl
  have e1 : (ext8 (ext5 X (List.replicate k true)) (fun _ => [])) fuel8 = List.replicate k true := rfl
  rw [e1, List.length_replicate] at s1
  have b1 : Function.update (ext8 (ext5 X (List.replicate k true)) (fun _ => [])) (zc 0)
      (List.replicate k true) =
      ext8 (ext5 X (List.replicate k true)) ![List.replicate k true, [], []] := by
    funext x
    rcases x with x | x
    · rw [Function.update_of_ne (by intro h; cases h)]; rfl
    · fin_cases x <;> simp [ext8, zc]
  rw [b1] at s1
  -- 2. the lifted program
  have s2 := lift8_run K _ _ _ _ _ _ ![List.replicate k true, [], []] tK hK
  -- 3. copy raw word 2 into zc 2
  have s3 := cp8_run raw2 (zc 2) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (ext8 (ext5 Y []) ![List.replicate k true, [], []]) rfl rfl
  have e3 : (ext8 (ext5 Y []) ![List.replicate k true, [], []]) raw2 = List.replicate (y + k) true :=
    hY
  rw [e3, List.length_replicate] at s3
  have b3 : Function.update (ext8 (ext5 Y []) ![List.replicate k true, [], []]) (zc 2)
      (List.replicate (y + k) true) =
      ext8 (ext5 Y []) ![List.replicate k true, [], List.replicate (y + k) true] := by
    funext x
    rcases x with x | x
    · rw [Function.update_of_ne (by intro h; cases h)]; rfl
    · fin_cases x <;> simp [ext8, zc]
  rw [b3] at s3
  -- 4. subtract
  have s4 := sub_run k (ext8 (ext5 Y []) ![List.replicate k true, [], List.replicate (y + k) true])
    (List.replicate y true) none rfl
    (by show List.replicate (y + k) true = _; rw [Nat.add_comm, List.replicate_add])
  have b4a : Function.update
      (ext8 (ext5 Y []) ![List.replicate k true, [], List.replicate (y + k) true]) (zc 0) [] =
      ext8 (ext5 Y []) ![[], [], List.replicate (y + k) true] := by
    funext x
    rcases x with x | x
    · rw [Function.update_of_ne (by intro h; cases h)]; rfl
    · fin_cases x <;> simp [ext8, zc]
  have b4b : Function.update (ext8 (ext5 Y []) ![[], [], List.replicate (y + k) true]) (zc 2)
      (List.replicate y true) = ext8 (ext5 Y []) ![[], [], List.replicate y true] := by
    funext x
    rcases x with x | x
    · rw [Function.update_of_ne (by intro h; cases h)]; rfl
    · fin_cases x <;> simp [ext8, zc]
  have b4 : Function.update (Function.update
      (ext8 (ext5 Y []) ![List.replicate k true, [], List.replicate (y + k) true]) (zc 0) [])
      (zc 2) (List.replicate y true) =
      ext8 (ext5 Y []) ![[], [], List.replicate y true] := by
    rw [b4a, b4b]
  rw [b4] at s4
  -- compose (innermost first)
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs cpRaw2 subP .scan () none none none none
    _ _ _ _ _ s3 s4
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs (lift8 K) _ k0 _ v0 v1 _ _ _ _ _ _ _ s2 r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs cpFuel _ .scan _ none none _ _ _ _ _ _ _ s1 r2
  exact ⟨u1, by omega, r1⟩

#print axioms cp8_run
#print axioms sub_run
#print axioms yk_core_run

end EthInapproximability.CurrentPaper.G5eYkCore
