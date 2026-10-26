import EthInapproximability.CurrentPaper.BitMachineBinaryAddAny
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Binary schoolbook multiplication on fixed Boolean stacks

A physical MSB multiplier scan uses one source-preserving copy and one
unequal-width addition for each one bit. The accumulator is doubled by one
`push false` at its low-bit end. The exact run, arithmetic result, quadratic
bitword-length cost, and framed single-input packet theorem are proved below.
This is a multiplication primitive, not a complete modular Horner accessor.
-/

namespace EthInapproximability.CurrentPaper.BitMachineBinaryMultiply

set_option maxRecDepth 16384

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open BitMachineSubroutineRenaming

abbrev Stack := Fin 3 ⊕ Fin 3
abbrev Label := BitMachineBinaryAddAny.Label ⊕
  (BitMachineCopy.Label ⊕ Unit)
abbrev Control := BitMachineBinaryAddAny.Control × (Option Bool × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (BitMachineBinaryAddAny.initial, none, none)

def copyStackSwap : (Fin 3 ⊕ Fin 3) ≃ Stack where
  toFun := Sum.elim
    (fun i => if i = 0 then .inr 0 else if i = 1 then .inl 1 else .inr 2)
    (fun i => if i = 0 then .inl 0 else if i = 1 then .inl 2 else .inr 1)
  invFun := Sum.elim
    (fun i => if i = 0 then .inr 0 else if i = 1 then .inl 1 else .inr 1)
    (fun i => if i = 0 then .inl 0 else if i = 1 then .inr 2 else .inl 2)
  left_inv := by intro i; rcases i with i | i <;> fin_cases i <;> rfl
  right_inv := by intro i; rcases i with i | i <;> fin_cases i <;> rfl

def copyLabelSwap :
    (BitMachineCopy.Label ⊕ (BitMachineBinaryAddAny.Label ⊕ Unit)) ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inl l))
    (Sum.elim Sum.inl (fun u => .inr (.inr u)))
  invFun := Sum.elim (fun l => .inr (.inl l))
    (Sum.elim Sum.inl (fun u => .inr (.inr u)))
  left_inv := by intro l; rcases l with l | (l | l) <;> rfl
  right_inv := by intro l; rcases l with l | (l | l) <;> rfl

def copyControlSwap :
    (Option Bool × (BitMachineBinaryAddAny.Control × Option Bool)) ≃ Control where
  toFun := fun s => (s.2.1, s.1, s.2.2)
  invFun := fun s => (s.2.1, s.1, s.2.2)
  left_inv := by intro s; rfl
  right_inv := by intro s; rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inr ())) (BitMachineBinaryAddAny.program l)
  | .inr (.inl l) =>
      renameStmt copyStackSwap copyLabelSwap copyControlSwap
        (liftStmt (some (.inl .scan)) (BitMachineCopy.program l))
  | .inr (.inr ()) => pop (.inr 1) (fun _ bit => (BitMachineBinaryAddAny.initial, none, bit))
      (branch (fun s => s.2.2.isSome)
        (push (.inl 0) (fun _ => false)
          (branch (fun s => s.2.2.getD false)
            (load (fun s => (BitMachineBinaryAddAny.initial, none, s.2.2))
              (goto (fun _ => .inr (.inl .scan))))
            (load (fun _ => initial) (goto (fun _ => .inr (.inr ()))))))
        (load (fun _ => initial) halt))

def rightBank (multiplicand multiplier copyScratch : List Bool) : Fin 3 → List Bool :=
  fun i => if i = 0 then multiplicand else if i = 1 then multiplier else copyScratch

def cfg (l : Option Label) (s : Control)
    (acc operand addScratch multiplicand multiplier copyScratch : List Bool) : Config :=
  ⟨l, s, Sum.elim (BitMachineBinaryAddAny.bank acc operand addScratch)
    (rightBank multiplicand multiplier copyScratch)⟩

private theorem rightBank_one (a b c : List Bool) : rightBank a b c 1 = b := rfl

private theorem popMultiplier (A : Fin 3 → List Bool)
    (a b c : List Bool) :
    Function.update (Sum.elim A (rightBank a b c)) (.inr 1) [] =
      Sum.elim A (rightBank a [] c) := by
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [rightBank]

private theorem popMultiplier_cons (A : Fin 3 → List Bool)
    (a b c : List Bool) (bit : Bool) :
    Function.update (Sum.elim A (rightBank a (bit :: b) c)) (.inr 1) b =
      Sum.elim A (rightBank a b c) := by
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [rightBank]

private theorem pushAcc (a b c : List Bool) (R : Fin 3 → List Bool) :
    Function.update (Sum.elim (BitMachineBinaryAddAny.bank a b c) R)
      (.inl 0) (false :: a) =
    Sum.elim (BitMachineBinaryAddAny.bank (false :: a) b c) R := by
  funext k
  rcases k with k | k <;> fin_cases k <;>
    simp [BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank]

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem step_outer_one (s : Control) (bit : Bool)
    (acc operand addScratch multiplicand multiplier copyScratch : List Bool) :
    TM2.step program (cfg (some (.inr (.inr ()))) s
      acc operand addScratch multiplicand (bit :: multiplier) copyScratch) =
      some (cfg (some (if bit then .inr (.inl .scan) else .inr (.inr ())))
        (if bit then (BitMachineBinaryAddAny.initial, none, some bit) else initial)
        (false :: acc) operand addScratch multiplicand multiplier copyScratch) := by
  cases bit <;>
    simp only [TM2.step, TM2.stepAux, program, cfg, Sum.elim_inr]
  all_goals
    simp only [rightBank_one, List.head?_cons, Option.isSome_some,
      Option.getD_some, List.tail_cons, popMultiplier_cons,
      Bool.cond_true, Bool.cond_false, if_true, Sum.elim_inl,
      BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank]
  all_goals
    congr 1
    congr 1
    funext k
    rcases k with k | k <;> fin_cases k <;>
      simp [BitMachineBinaryAdd.bank, rightBank]

private theorem step_outer_nil (s : Control)
    (acc operand addScratch multiplicand copyScratch : List Bool) :
    TM2.step program (cfg (some (.inr (.inr ()))) s
      acc operand addScratch multiplicand [] copyScratch) =
      some (cfg none initial acc operand addScratch multiplicand [] copyScratch) := by
  simp only [TM2.step, TM2.stepAux, program, cfg, Sum.elim_inr]
  simp only [rightBank_one, List.head?_nil, Option.isSome_none,
    Bool.cond_false, List.tail_nil, popMultiplier]

private theorem copy_cfg (l : Option BitMachineCopy.Label)
    (v : Option Bool) (w : BitMachineBinaryAddAny.Control)
    (outer : Option Bool) (source target scratch acc addScratch multiplier : List Bool) :
    renameCfg copyStackSwap copyLabelSwap copyControlSwap
      (liftCfg (some (.inl .scan)) (w, outer)
        (fun i : Fin 3 => if i = 0 then acc else if i = 1 then addScratch else multiplier)
        (BitMachineCopy.cfg l v source target scratch)) =
      cfg (match l with
        | some x => some (.inr (.inl x))
        | none => some (.inl .scan)) (w, v, outer)
        acc target addScratch source multiplier scratch := by
  cases l with
  | none =>
      simp only [renameCfg, liftCfg, cfg, copyControlSwap, copyLabelSwap,
        copyStackSwap, BitMachineCopy.cfg]
      congr 1
      funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [BitMachineCopy.stackContents, rightBank,
          BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank]
  | some l =>
      simp only [renameCfg, liftCfg, cfg, copyControlSwap, copyLabelSwap,
        copyStackSwap, BitMachineCopy.cfg]
      congr 1
      funext k
      rcases k with k | k <;> fin_cases k <;>
        simp [BitMachineCopy.stackContents, rightBank,
          BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank]

theorem copy_call (acc source multiplier : List Bool) :
    ∃ n ≤ 2 * source.length + 2,
      run n (cfg (some (.inr (.inl .scan)))
        (BitMachineBinaryAddAny.initial, none, some true)
        acc [] [] source multiplier []) =
      cfg (some (.inl .scan))
        (BitMachineBinaryAddAny.initial, none, some true)
        acc source [] source multiplier [] := by
  have hQ : ∀ l, program (copyLabelSwap (.inl l)) =
      renameStmt copyStackSwap copyLabelSwap copyControlSwap
        (liftStmt (some (.inl .scan)) (BitMachineCopy.program l)) := by
    intro l
    rfl
  have hhalt : (((advance BitMachineCopy.program)^[2 * source.length + 2])
      (BitMachineCopy.cfg (some .scan) none source [] [])).l = none := by
    rw [show ((advance BitMachineCopy.program)^[2 * source.length + 2])
      (BitMachineCopy.cfg (some .scan) none source [] []) =
      BitMachineCopy.run (2 * source.length + 2)
        (BitMachineCopy.cfg (some .scan) none source [] []) from rfl,
      BitMachineCopy.run_correct]
    rfl
  obtain ⟨n, hn, hr⟩ := lift_outputs_renamed
    copyStackSwap copyLabelSwap copyControlSwap
    BitMachineCopy.program program (some (.inl .scan)) hQ
    (BitMachineBinaryAddAny.initial, some true)
    (fun i : Fin 3 => if i = 0 then acc else if i = 1 then ([] : List Bool)
      else multiplier)
    (BitMachineCopy.cfg (some .scan) none source [] [])
    (2 * source.length + 2) hhalt
  refine ⟨n, hn, ?_⟩
  rw [show run n _ = ((advance program)^[n]) _ from rfl]
  rw [← copy_cfg (some .scan) none BitMachineBinaryAddAny.initial (some true)
    source [] [] acc [] multiplier]
  rw [hr]
  have hc := BitMachineCopy.run_correct none source []
  change ((advance BitMachineCopy.program)^[2 * source.length + 2])
    (BitMachineCopy.cfg (some .scan) none source [] []) =
      BitMachineCopy.cfg none none source (source ++ []) [] at hc
  rw [hc]
  simpa only [List.append_nil] using
    copy_cfg none none BitMachineBinaryAddAny.initial (some true)
      source source [] acc [] multiplier

private theorem add_cfg (l : Option BitMachineBinaryAddAny.Label)
    (v : BitMachineBinaryAddAny.Control) (copyState outer : Option Bool)
    (acc operand saved source multiplier copyScratch : List Bool) :
    liftCfg (some (.inr ())) (copyState, outer)
      (rightBank source multiplier copyScratch)
      (BitMachineBinaryAddAny.cfg l v acc operand saved) =
    cfg (match l with
      | some x => some (.inl x)
      | none => some (.inr (.inr ())))
      (v, copyState, outer) acc operand saved source multiplier copyScratch := by
  cases l <;> rfl

theorem add_call (acc operand source multiplier : List Bool) (outer : Option Bool) :
    ∃ n ≤ 2 * max acc.length operand.length + 2,
      run n (cfg (some (.inl .scan))
        (BitMachineBinaryAddAny.initial, none, outer)
        acc operand [] source multiplier []) =
      cfg (some (.inr (.inr ())))
        (BitMachineBinaryAddAny.initial, none, outer)
        (BitMachineBinaryAddAny.addAny acc operand false) [] []
        source multiplier [] := by
  have hQ : ∀ l, program (.inl l) =
      liftStmt (some (.inr ())) (BitMachineBinaryAddAny.program l) := by
    intro l
    rfl
  have hhalt : (((advance BitMachineBinaryAddAny.program)^[
      2 * max acc.length operand.length + 2])
      (BitMachineBinaryAddAny.cfg (some .scan) BitMachineBinaryAddAny.initial
        acc operand [])).l = none := by
    rw [show ((advance BitMachineBinaryAddAny.program)^[
      2 * max acc.length operand.length + 2])
      (BitMachineBinaryAddAny.cfg (some .scan) BitMachineBinaryAddAny.initial
        acc operand []) =
      BitMachineBinaryAddAny.run (2 * max acc.length operand.length + 2)
        (BitMachineBinaryAddAny.cfg (some .scan) BitMachineBinaryAddAny.initial
          acc operand []) from rfl,
      BitMachineBinaryAddAny.run_correct]
    rfl
  obtain ⟨n, hn, hr⟩ := BitMachineSubroutine.lift_outputs
    BitMachineBinaryAddAny.program program (some (.inr ())) hQ
    (none, outer) (rightBank source multiplier [])
    (BitMachineBinaryAddAny.cfg (some .scan) BitMachineBinaryAddAny.initial
      acc operand []) (2 * max acc.length operand.length + 2) hhalt
  refine ⟨n, hn, ?_⟩
  change ((advance program)^[n]) _ = _
  have hs := add_cfg (some .scan) BitMachineBinaryAddAny.initial none outer
    acc operand [] source multiplier []
  change _ = cfg (some (.inl .scan))
    (BitMachineBinaryAddAny.initial, none, outer)
    acc operand [] source multiplier [] at hs
  rw [← hs, hr]
  have ha := BitMachineBinaryAddAny.run_correct acc operand
  change ((advance BitMachineBinaryAddAny.program)^[
    2 * max acc.length operand.length + 2])
    (BitMachineBinaryAddAny.cfg (some .scan) BitMachineBinaryAddAny.initial
      acc operand []) =
    BitMachineBinaryAddAny.cfg none BitMachineBinaryAddAny.initial
      (BitMachineBinaryAddAny.addAny acc operand false) [] [] at ha
  rw [ha]
  exact add_cfg none BitMachineBinaryAddAny.initial none outer
    (BitMachineBinaryAddAny.addAny acc operand false) [] [] source multiplier []

private theorem run_step {c d : Config} (h : TM2.step program c = some d)
    (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d)
    (u : ℕ) : run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def mulStep (acc source : List Bool) (bit : Bool) : List Bool :=
  if bit then BitMachineBinaryAddAny.addAny (false :: acc) source false
    else false :: acc

def stepBudget (acc source : List Bool) : ℕ :=
  1 + (2 * source.length + 2) +
    (2 * max (acc.length + 1) source.length + 2)

theorem oneStep (acc source tail : List Bool) (bit : Bool) (s : Control) :
    ∃ n ≤ stepBudget acc source,
      run n (cfg (some (.inr (.inr ()))) s
        acc [] [] source (bit :: tail) []) =
      cfg (some (.inr (.inr ())))
        (if bit then (BitMachineBinaryAddAny.initial, none, some true) else initial)
        (mulStep acc source bit) [] [] source tail [] := by
  cases bit with
  | false =>
      refine ⟨1, by unfold stepBudget; omega, ?_⟩
      have h := run_step (step_outer_one s false acc [] [] source tail []) 0
      simpa [mulStep] using h
  | true =>
      obtain ⟨nc, hnc, hc⟩ := copy_call (false :: acc) source tail
      obtain ⟨na, hna, ha⟩ := add_call (false :: acc) source source tail (some true)
      refine ⟨1 + nc + na, ?_, ?_⟩
      · unfold stepBudget
        simp only [List.length_cons] at hna
        omega
      · have hs := run_step (step_outer_one s true acc [] [] source tail [])
          (nc + na)
        have hca := (run_add hc na).trans ha
        rw [show 1 + nc + na = (nc + na) + 1 by omega]
        simpa [mulStep] using hs.trans hca

def multiplyFrom (acc source : List Bool) : List Bool → List Bool
  | [] => acc
  | bit :: tail => multiplyFrom (mulStep acc source bit) source tail

def totalBudget (acc source : List Bool) : List Bool → ℕ
  | [] => 1
  | bit :: tail => stepBudget acc source +
      totalBudget (mulStep acc source bit) source tail

theorem total_run (acc source bits : List Bool) (s : Control) :
    ∃ n ≤ totalBudget acc source bits,
      run n (cfg (some (.inr (.inr ()))) s
        acc [] [] source bits []) =
      cfg none initial (multiplyFrom acc source bits) [] [] source [] [] := by
  induction bits generalizing acc s with
  | nil =>
      refine ⟨1, by rfl, ?_⟩
      simpa [multiplyFrom] using
        run_step (step_outer_nil s acc [] [] source []) 0
  | cons bit tail ih =>
      obtain ⟨n, hn, hs⟩ := oneStep acc source tail bit s
      obtain ⟨m, hm, ht⟩ := ih (mulStep acc source bit)
        (if bit then (BitMachineBinaryAddAny.initial, none, some true) else initial)
      refine ⟨n + m, by simp only [totalBudget]; omega, ?_⟩
      simpa only [multiplyFrom] using (run_add hs m).trans ht

private theorem bitsValue_false_cons (bits : List Bool) :
    EncodedCommunication.bitsValue (false :: bits) =
      2 * EncodedCommunication.bitsValue bits := by
  simp [EncodedCommunication.bitsValue, Nat.bit_val]

theorem mulStep_value (acc source : List Bool) (bit : Bool) :
    EncodedCommunication.bitsValue (mulStep acc source bit) =
      2 * EncodedCommunication.bitsValue acc +
        bit.toNat * EncodedCommunication.bitsValue source := by
  cases bit
  · simp [mulStep, bitsValue_false_cons]
  · simp only [mulStep, ↓reduceIte,
      BitMachineBinaryAddAny.result_value, bitsValue_false_cons,
      Bool.toNat_true, one_mul]

def msbValue (bits : List Bool) : ℕ :=
  bits.foldl (fun n b => Nat.bit b n) 0

private def evalFrom (start : ℕ) (bits : List Bool) : ℕ :=
  bits.foldl (fun n b => Nat.bit b n) start

private theorem evalFrom_affine (start : ℕ) (bits : List Bool) :
    evalFrom start bits = 2 ^ bits.length * start + msbValue bits := by
  induction bits generalizing start with
  | nil => simp [evalFrom, msbValue]
  | cons bit tail ih =>
      rw [show evalFrom start (bit :: tail) =
          evalFrom (Nat.bit bit start) tail from rfl,
        ih]
      have hz := ih bit.toNat
      simp only [evalFrom, msbValue] at hz
      simp only [msbValue, List.foldl_cons,
        Nat.bit_val, Nat.mul_zero, Nat.zero_add] at ⊢
      simp only [Nat.bit_val] at hz
      rw [hz]
      simp only [List.length_cons, pow_succ]
      ring

theorem msbValue_cons (bit : Bool) (tail : List Bool) :
    msbValue (bit :: tail) =
      2 ^ tail.length * bit.toNat + msbValue tail := by
  have h := evalFrom_affine bit.toNat tail
  simpa only [msbValue, evalFrom, List.foldl_cons,
    Nat.bit_val, Nat.mul_zero, Nat.zero_add] using h

theorem multiplyFrom_value (acc source bits : List Bool) :
    EncodedCommunication.bitsValue (multiplyFrom acc source bits) =
      2 ^ bits.length * EncodedCommunication.bitsValue acc +
        EncodedCommunication.bitsValue source * msbValue bits := by
  induction bits generalizing acc with
  | nil => simp [multiplyFrom, msbValue]
  | cons bit tail ih =>
      rw [multiplyFrom, ih, mulStep_value, msbValue_cons]
      simp only [List.length_cons, pow_succ]
      ring

theorem standard_value (source multiplier : List Bool) :
    EncodedCommunication.bitsValue (multiplyFrom [] source multiplier) =
      EncodedCommunication.bitsValue source * msbValue multiplier := by
  simpa [EncodedCommunication.bitsValue] using
    multiplyFrom_value [] source multiplier

theorem mulStep_length_le (acc source : List Bool) (bit : Bool) :
    (mulStep acc source bit).length ≤ max acc.length source.length + 2 := by
  cases bit with
  | false => simp [mulStep]; omega
  | true =>
      simp only [mulStep, ↓reduceIte, BitMachineBinaryAddAny.addAny_length,
        List.length_cons]
      omega

theorem totalBudget_bound (acc source bits : List Bool) (M : ℕ)
    (hM : max acc.length source.length + 2 * bits.length ≤ M) :
    totalBudget acc source bits ≤ (bits.length + 1) * (4 * M + 7) := by
  induction bits generalizing acc with
  | nil => simp [totalBudget]
  | cons bit tail ih =>
      have hlen := mulStep_length_le acc source bit
      have hmax : max (mulStep acc source bit).length source.length ≤
          max acc.length source.length + 2 := by omega
      have htail : max (mulStep acc source bit).length source.length +
          2 * tail.length ≤ M := by
        simp only [List.length_cons] at hM
        omega
      have hb := ih (mulStep acc source bit) htail
      have hsrc : source.length ≤ M := by omega
      have hacc : acc.length ≤ M := by omega
      have hinner : max (acc.length + 1) source.length ≤ M + 1 := by omega
      have hstep : stepBudget acc source ≤ 4 * M + 7 := by
        unfold stepBudget
        omega
      simp only [totalBudget, List.length_cons]
      nlinarith

theorem standard_time_bound (source multiplier : List Bool) :
    totalBudget [] source multiplier ≤
      (multiplier.length + 1) *
        (4 * (source.length + 2 * multiplier.length) + 7) := by
  apply totalBudget_bound
  simp

theorem standard_run (source multiplier : List Bool) :
    ∃ n ≤ (multiplier.length + 1) *
        (4 * (source.length + 2 * multiplier.length) + 7),
      run n (cfg (some (.inr (.inr ()))) initial
        [] [] [] source multiplier []) =
      cfg none initial (multiplyFrom [] source multiplier) [] [] source [] [] := by
  obtain ⟨n, hn, hr⟩ := total_run [] source multiplier initial
  exact ⟨n, hn.trans (standard_time_bound source multiplier), hr⟩

theorem multiplyFrom_length_bound (acc source bits : List Bool) :
    max (multiplyFrom acc source bits).length source.length ≤
      max acc.length source.length + 2 * bits.length := by
  induction bits generalizing acc with
  | nil => simp [multiplyFrom]
  | cons bit tail ih =>
      have hs := mulStep_length_le acc source bit
      have ht := ih (mulStep acc source bit)
      simp only [multiplyFrom, List.length_cons]
      omega

def finStack : Stack ≃ Fin 6 := finSumFinEquiv

def finProgram : Label → TM2.Stmt (fun _ : Fin 6 => Bool) Label Control :=
  fun l => renameStmt finStack (Equiv.refl Label) (Equiv.refl Control) (program l)

def finBank (S : Stack → List Bool) : Fin 6 → List Bool :=
  fun k => S (finStack.symm k)

def initialBank (source multiplier : List Bool) : Fin 6 → List Bool :=
  finBank (cfg (some (.inr (.inr ()))) initial
    [] [] [] source multiplier []).stk

def finalBank (source multiplier : List Bool) : Fin 6 → List Bool :=
  finBank (cfg none initial
    (multiplyFrom [] source multiplier) [] [] source [] []).stk

theorem fin_run (source multiplier : List Bool) :
    ∃ n ≤ (multiplier.length + 1) *
        (4 * (source.length + 2 * multiplier.length) + 7),
      ((advance finProgram)^[n])
        (⟨some (.inr (.inr ())), initial, initialBank source multiplier⟩ :
          TM2.Cfg (fun _ : Fin 6 => Bool) Label Control) =
        ⟨none, initial, finalBank source multiplier⟩ := by
  obtain ⟨n, hn, hr⟩ := standard_run source multiplier
  have h := rename_run finStack (Equiv.refl Label) (Equiv.refl Control)
    program (cfg (some (.inr (.inr ()))) initial
      [] [] [] source multiplier []) n
  change ((advance finProgram)^[n])
      (⟨some (.inr (.inr ())), initial, initialBank source multiplier⟩ :
        TM2.Cfg (fun _ : Fin 6 => Bool) Label Control) =
      renameCfg finStack (Equiv.refl Label) (Equiv.refl Control)
        (run n (cfg (some (.inr (.inr ()))) initial
          [] [] [] source multiplier [])) at h
  rw [hr] at h
  exact ⟨n, hn, h⟩

def packedInput (source multiplier : List Bool) : List Bool :=
  BitMachineBankCodec.encode (initialBank source multiplier)

theorem initialBank_code_length (source multiplier : List Bool) :
    (packedInput source multiplier).length =
      2 * (source.length + multiplier.length) + 6 := by
  rw [packedInput, BitMachineBankCodec.encode_length]
  simp [initialBank, finBank, finStack, cfg, rightBank,
    BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank,
    Fin.sum_univ_succ, finSumFinEquiv, Fin.addCases]

theorem finalBank_code_length_le (source multiplier : List Bool) :
    (BitMachineBankCodec.encode (finalBank source multiplier)).length ≤
      4 * (source.length + multiplier.length) + 6 := by
  have hl := multiplyFrom_length_bound [] source multiplier
  rw [BitMachineBankCodec.encode_length]
  simp [finalBank, finBank, finStack, cfg, rightBank,
    BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank,
    Fin.sum_univ_succ, finSumFinEquiv, Fin.addCases] at hl ⊢
  omega

theorem packed_run (source multiplier : List Bool) :
    ∃ (u : ℕ) (S' : Fin 6 → List Bool),
      u ≤ 100 * ((packedInput source multiplier).length + 1) ^ 2 ∧
      BitMachineBankWrapper.run finProgram (.inr (.inr ())) initial u
        (BitMachineBankWrapper.cfg
          (some (.inr (.parse (.scan 0)))) (initial, none)
          (fun _ : Fin 6 => []) (packedInput source multiplier) [] []) =
        BitMachineBankWrapper.cfg none (initial, none) S' [] []
          (BitMachineBankCodec.encode (finalBank source multiplier)) := by
  have hd : BitMachineBankCodec.decode 6 (packedInput source multiplier) =
      some (initialBank source multiplier) := by simp [packedInput]
  obtain ⟨n, hn, hr⟩ := fin_run source multiplier
  let c : TM2.Cfg (fun _ : Fin 6 => Bool) Label Control :=
    ⟨none, initial, finalBank source multiplier⟩
  have hc : ((advance finProgram)^[n])
      (⟨some (.inr (.inr ())), initial, initialBank source multiplier⟩ :
        TM2.Cfg (fun _ : Fin 6 => Bool) Label Control) = c := hr
  have hhalt : c.l = none := rfl
  obtain ⟨u, S', hu, hrun⟩ := BitMachineBankWrapper.packed_run
    finProgram (.inr (.inr ())) initial (packedInput source multiplier)
    (initialBank source multiplier) hd n c hc hhalt
  have he : BitMachineBankSerialize.encode (List.ofFn (finalBank source multiplier)) =
      BitMachineBankCodec.encode (finalBank source multiplier) := by
    rw [BitMachineBankCodec.encode_eq_list]
    rfl
  rw [he] at hu hrun
  refine ⟨u, S', ?_, hrun⟩
  have hi := initialBank_code_length source multiplier
  have ho := finalBank_code_length_le source multiplier
  have hmul : (multiplier.length + 1) *
      (4 * (source.length + 2 * multiplier.length) + 7) ≤
      (source.length + multiplier.length + 1) *
        (8 * (source.length + multiplier.length) + 7) := by
    have hleft : multiplier.length + 1 ≤
        source.length + multiplier.length + 1 := by omega
    have hright : 4 * (source.length + 2 * multiplier.length) + 7 ≤
        8 * (source.length + multiplier.length) + 7 := by omega
    exact (Nat.mul_le_mul hleft hright)
  have hn' := hn.trans hmul
  simp only [packedInput] at hi hu ⊢
  rw [hi] at hu ⊢
  nlinarith

noncomputable def packedMachine : BitMachine.Machine :=
  BitMachineBankWrapper.machine finProgram (.inr (.inr ())) initial

theorem packed_outputs (source multiplier : List Bool) :
    packedMachine.OutputsWithin (packedInput source multiplier)
      (BitMachineBankCodec.encode (finalBank source multiplier))
      (100 * ((packedInput source multiplier).length + 1) ^ 2) := by
  obtain ⟨u, S', hu, hr⟩ := packed_run source multiplier
  change (BitMachineBankWrapper.machine finProgram (.inr (.inr ())) initial).OutputsWithin
    (packedInput source multiplier)
    (BitMachineBankCodec.encode (finalBank source multiplier))
    (100 * ((packedInput source multiplier).length + 1) ^ 2)
  apply outputsWithin_of_raw_run (.inr 0) (.inr 2)
    (.inr (.parse (.scan 0))) (initial, none)
    (BitMachineBankWrapper.program finProgram (.inr (.inr ())) initial)
    (packedInput source multiplier)
    (BitMachineBankCodec.encode (finalBank source multiplier)) u _ hu
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run finProgram (.inr (.inr ())) initial u _).l = none
    rw [hr]
    rfl
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run finProgram (.inr (.inr ())) initial u _).stk (.inr 2) = _
    rw [hr]
    rfl

end EthInapproximability.CurrentPaper.BitMachineBinaryMultiply
