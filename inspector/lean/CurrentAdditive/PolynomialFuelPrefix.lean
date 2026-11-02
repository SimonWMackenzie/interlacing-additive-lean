import EthInapproximability.CurrentPaper.SourceInputLengthUnary
import EthInapproximability.CurrentPaper.MatrixWeightedPower
import EthInapproximability.CurrentPaper.CutoffProbePreparation

/-!
A literal fixed twelfth-power unary clock writer.  The input is on bank zero.
The length, power, and packing routines are all physical finite-stack TM2
programs; the intermediate clock is never inserted by host-level `init`.
-/
namespace CurrentAdditive.PolynomialFuelPrefix

set_option maxRecDepth 10000
set_option maxHeartbeats 0

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

abbrev Stack := Fin 11

inductive Label where
  | count : SourceInputLengthUnary.Label → Label
  | seedAcc | seedBase₁ | seedBase₂
  | seedExponent : Fin 12 → Label
  | power : MatrixWeightedPower.Label → Label
  | pack : CutoffProbePreparation.Label → Label
  | done
  deriving DecidableEq, Fintype

abbrev Control := SourceInputLengthUnary.Control ×
  MatrixWeightedPower.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def countEmbed : SourceInputLengthUnary.Stack ↪ Stack where
  toFun k := ⟨k.val, by omega⟩
  inj' := by intro i j h; exact Fin.ext (Fin.mk.inj h)

def powerKey : MatrixWeightedPower.Stack → Stack
  | .inl i => match i.val with
      | 0 => 4 | 1 => 3 | 2 => 5 | 3 => 6 | 4 => 7 | _ => 8
  | .inr _ => 9

def powerEmbed : MatrixWeightedPower.Stack ↪ Stack where
  toFun := powerKey
  inj' := by
    intro i j h
    rcases i with i | i <;> rcases j with j | j
    · fin_cases i <;> fin_cases j <;> simp_all [powerKey]
    · fin_cases i <;> fin_cases j <;> simp_all [powerKey]
    · fin_cases i <;> fin_cases j <;> simp_all [powerKey]
    · fin_cases i <;> fin_cases j <;> simp_all [powerKey]

def packKey : Fin 5 → Stack
  | 0 => 0 | 1 => 4 | 2 => 10 | 3 => 1 | _ => 2

def packEmbed : Fin 5 ↪ Stack where
  toFun := packKey
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all [packKey]

def embedCount (v : SourceInputLengthUnary.Control) : Control :=
  (v, (false, false), none)
def readCount (v : Control) : SourceInputLengthUnary.Control := v.1
def embedPower (v : MatrixWeightedPower.Control) : Control :=
  ((none, none), v, none)
def readPower (v : Control) : MatrixWeightedPower.Control := v.2.1
def embedPack (v : Option Bool) : Control :=
  ((none, none), (false, false), v)
def readPack (v : Control) : Option Bool := v.2.2

def nextExponent (i : Fin 12) : Label :=
  if h : i.val + 1 < 12 then .seedExponent ⟨i.val + 1, h⟩
  else .power (.inr .test)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .count l => stmt countEmbed Label.count embedCount readCount
      (some .seedAcc) (SourceInputLengthUnary.program l)
  | .seedAcc => push 4 (fun _ => true) (goto (fun _ => .seedBase₁))
  | .seedBase₁ => push 3 (fun _ => true) (goto (fun _ => .seedBase₂))
  | .seedBase₂ => push 3 (fun _ => true)
      (goto (fun _ => .seedExponent 0))
  | .seedExponent i => push 9 (fun _ => true)
      (goto (fun _ => nextExponent i))
  | .power l => stmt powerEmbed Label.power embedPower readPower
      (some (.pack .scanBits)) (MatrixWeightedPower.program l)
  | .pack l => stmt packEmbed Label.pack embedPack readPack
      (some .done) (CutoffProbePreparation.program l)
  | .done => halt

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

theorem run_add (t u : ℕ) (c : Config) :
    run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance program) u t c

def init (bits : List Bool) : Config :=
  ⟨some (.count (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
    embedCount (none, none),
    fun i => if i = 0 then bits else []⟩

def banks (bits unary acc fuel packed cap : List Bool) : Stack → List Bool :=
  ![bits, packed, cap, unary, acc, [], [], [], [], fuel, []]

theorem count_phase (bits : List Bool) :
    ∃ t ≤ 3 * bits.length + 4,
      run t (init bits) =
        ⟨some .seedAcc, embedCount (none, none),
          banks bits (List.replicate bits.length true) [] [] [] []⟩ := by
  let c : SourceInputLengthUnary.Config :=
    ⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
      (none, none), SourceInputLengthUnary.contents bits [] [] []⟩
  obtain ⟨t, ht, hr⟩ := SourceInputLengthUnary.length_run bits
  have hh : (((advance SourceInputLengthUnary.program)^[t]) c).l = none := by
    rw [hr]
  have he := BitMachineStackEmbedding.outputs countEmbed (banks bits [] [] [] [] [])
    Label.count embedCount readCount (by intro x; rfl) (some .seedAcc)
    SourceInputLengthUnary.program program (by intro l; rfl) c t hh
  obtain ⟨u, hu, he⟩ := he
  refine ⟨u, hu.trans ht, ?_⟩
  have hi : BitMachineStackEmbedding.cfg countEmbed
      (banks bits [] [] [] [] []) Label.count embedCount (some .seedAcc) c =
      init bits := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, c, init]
    congr 1
    have hbank : bank countEmbed (banks bits [] [] [] [] [])
        (SourceInputLengthUnary.contents bits [] [] []) = banks bits [] [] [] [] [] := by
      apply bank_eq_self
      intro k
      fin_cases k <;> rfl
    rw [hbank]
    funext k
    fin_cases k <;> rfl
  rw [hi] at he
  rw [hr] at he
  have hf : BitMachineStackEmbedding.cfg countEmbed
      (banks bits [] [] [] [] []) Label.count embedCount (some .seedAcc)
      ⟨none, (none, none),
        SourceInputLengthUnary.contents bits [] [] (List.replicate bits.length true)⟩ =
      ⟨some .seedAcc, embedCount (none, none),
        banks bits (List.replicate bits.length true) [] [] [] []⟩ := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg]
    congr 1
    funext k
    fin_cases k
    all_goals first
      | simpa [banks, SourceInputLengthUnary.contents] using
          (bank_at countEmbed (banks bits [] [] [] [] [])
            (SourceInputLengthUnary.contents bits [] [] (List.replicate bits.length true)) 0)
      | simpa [banks, SourceInputLengthUnary.contents] using
          (bank_at countEmbed (banks bits [] [] [] [] [])
            (SourceInputLengthUnary.contents bits [] [] (List.replicate bits.length true)) 1)
      | simpa [banks, SourceInputLengthUnary.contents] using
          (bank_at countEmbed (banks bits [] [] [] [] [])
            (SourceInputLengthUnary.contents bits [] [] (List.replicate bits.length true)) 2)
      | simpa [banks, SourceInputLengthUnary.contents] using
          (bank_at countEmbed (banks bits [] [] [] [] [])
            (SourceInputLengthUnary.contents bits [] [] (List.replicate bits.length true)) 3)
      | rw [bank_outside countEmbed (banks bits [] [] [] [] [])
          (SourceInputLengthUnary.contents bits [] [] (List.replicate bits.length true))
          _ (by intro ⟨j, hj⟩; fin_cases j <;> simp [countEmbed] at hj)]
        rfl
  exact he.trans hf

def exponentLabel (k : ℕ) : Label :=
  if h : k < 12 then .seedExponent ⟨k, h⟩ else .power (.inr .test)

theorem exponent_step (bits base : List Bool) (k : ℕ) (hk : k < 12) :
    advance program
      ⟨some (exponentLabel k), embedCount (none, none),
        banks bits base [true] (List.replicate k true) [] []⟩ =
      ⟨some (exponentLabel (k+1)), embedCount (none, none),
        banks bits base [true] (List.replicate (k+1) true) [] []⟩ := by
  simp only [exponentLabel, dif_pos hk]
  simp [advance, TM2.step, TM2.stepAux, program, nextExponent,
    banks, List.replicate_succ]
  funext i
  fin_cases i <;> simp [Function.update]

theorem exponent_run (bits base : List Bool) (k : ℕ) (hk : k ≤ 12) :
    run k
      ⟨some (exponentLabel 0), embedCount (none, none),
        banks bits base [true] [] [] []⟩ =
      ⟨some (exponentLabel k), embedCount (none, none),
        banks bits base [true] (List.replicate k true) [] []⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk' : k ≤ 12 := by omega
      have hlt : k < 12 := by omega
      rw [show k + 1 = Nat.succ k by rfl]
      unfold run
      rw [Function.iterate_succ_apply', ← run, ih hk', exponent_step bits base k hlt]

theorem seed_phase (bits : List Bool) :
    run 15
      ⟨some .seedAcc, embedCount (none, none),
        banks bits (List.replicate bits.length true) [] [] [] []⟩ =
      ⟨some (.power (.inr .test)), embedCount (none, none),
        banks bits (List.replicate (bits.length + 2) true)
          [true] (List.replicate 12 true) [] []⟩ := by
  have hfirst : run 3
      ⟨some .seedAcc, embedCount (none, none),
        banks bits (List.replicate bits.length true) [] [] [] []⟩ =
      ⟨some (exponentLabel 0), embedCount (none, none),
        banks bits (true :: true :: List.replicate bits.length true)
          [true] [] [] []⟩ := by
    simp [run, Function.iterate_succ_apply', advance, TM2.step, TM2.stepAux,
      program, exponentLabel, banks, Function.update]
    funext i
    fin_cases i <;> simp [Function.update]
  have hrest := exponent_run bits
    (true :: true :: List.replicate bits.length true) 12 (by omega)
  have hraw : run 15
      ⟨some .seedAcc, embedCount (none, none),
        banks bits (List.replicate bits.length true) [] [] [] []⟩ =
      ⟨some (.power (.inr .test)), embedCount (none, none),
        banks bits (true :: true :: List.replicate bits.length true)
          [true] (List.replicate 12 true) [] []⟩ := by
    rw [show 15 = 3 + 12 by omega, run_add, hfirst, hrest]
    simp [exponentLabel]
  convert hraw using 1

def baseLength (bits : List Bool) : ℕ := bits.length + 2
def clockLength (bits : List Bool) : ℕ := (baseLength bits)^12

def beforePower (bits : List Bool) : Stack → List Bool :=
  banks bits (List.replicate (baseLength bits) true)
    [true] (List.replicate 12 true) [] []

noncomputable def afterPower (bits : List Bool) : Stack → List Bool :=
  bank powerEmbed (beforePower bits)
    (MatrixWeightedPower.cfg none (false,false)
      (List.replicate (clockLength bits) true)
      (List.replicate (baseLength bits) true) [] []).stk

theorem power_phase (bits : List Bool) :
    ∃ t ≤ MatrixWeightedPower.powerBound (baseLength bits) 12,
      run t
        ⟨some (.power (.inr .test)), embedPower (false,false),
          beforePower bits⟩ =
      ⟨some (.pack .scanBits), embedPower (false,false), afterPower bits⟩ := by
  let c := MatrixWeightedPower.cfg (some (.inr .test)) (false,false)
    [true] (List.replicate (baseLength bits) true) [] (List.replicate 12 true)
  obtain ⟨t, ht, hr⟩ := MatrixWeightedPower.power_run (baseLength bits) 12
  have hr' : ((advance MatrixWeightedPower.program)^[t]) c =
      MatrixWeightedPower.cfg none (false,false)
        (List.replicate (clockLength bits) true)
        (List.replicate (baseLength bits) true) [] [] := by
    simpa only [MatrixWeightedPower.run, List.replicate_one, clockLength] using hr
  have hh : (((advance MatrixWeightedPower.program)^[t]) c).l = none := by
    rw [hr']
    rfl
  have he := BitMachineStackEmbedding.outputs powerEmbed (beforePower bits)
    Label.power embedPower readPower (by intro x; rfl) (some (.pack .scanBits))
    MatrixWeightedPower.program program (by intro l; rfl) c t hh
  obtain ⟨u, hu, he⟩ := he
  refine ⟨u, hu.trans ht, ?_⟩
  have hi : BitMachineStackEmbedding.cfg powerEmbed (beforePower bits)
      Label.power embedPower (some (.pack .scanBits)) c =
      ⟨some (.power (.inr .test)), embedPower (false,false), beforePower bits⟩ := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, c]
    congr 1
    apply bank_eq_self
    intro k
    rcases k with k | k <;> fin_cases k <;>
      rfl
  rw [hi, hr'] at he
  exact he

theorem afterPower_outside (bits : List Bool) (i : Stack)
    (h : ¬ ∃ k, powerEmbed k = i) :
    afterPower bits i = beforePower bits i := by
  exact bank_outside powerEmbed (beforePower bits)
    (MatrixWeightedPower.cfg none (false,false)
      (List.replicate (clockLength bits) true)
      (List.replicate (baseLength bits) true) [] []).stk i h

theorem afterPower_at_zero (bits : List Bool) : afterPower bits 0 = bits := by
  rw [afterPower_outside bits 0 (by
    intro ⟨k, hk⟩
    rcases k with k | k <;> fin_cases k <;>
      simp [powerEmbed, powerKey] at hk)]
  rfl

theorem afterPower_at_one (bits : List Bool) : afterPower bits 1 = [] := by
  rw [afterPower_outside bits 1 (by
    intro ⟨k, hk⟩
    rcases k with k | k <;> fin_cases k <;>
      simp [powerEmbed, powerKey] at hk)]
  rfl

theorem afterPower_at_two (bits : List Bool) : afterPower bits 2 = [] := by
  rw [afterPower_outside bits 2 (by
    intro ⟨k, hk⟩
    rcases k with k | k <;> fin_cases k <;>
      simp [powerEmbed, powerKey] at hk)]
  rfl

theorem afterPower_at_ten (bits : List Bool) : afterPower bits 10 = [] := by
  rw [afterPower_outside bits 10 (by
    intro ⟨k, hk⟩
    rcases k with k | k <;> fin_cases k <;>
      simp [powerEmbed, powerKey] at hk)]
  rfl

theorem afterPower_at_four (bits : List Bool) :
    afterPower bits 4 = List.replicate (clockLength bits) true := by
  have h := bank_at powerEmbed (beforePower bits)
    (MatrixWeightedPower.cfg none (false,false)
      (List.replicate (clockLength bits) true)
      (List.replicate (baseLength bits) true) [] []).stk (.inl 0)
  simpa only [afterPower, powerEmbed, powerKey, MatrixWeightedPower.cfg,
    MatrixWeightedPower.bank, Matrix.cons_val_zero, Sum.elim_inl] using h

noncomputable def afterPack (bits : List Bool) : Stack → List Bool :=
  bank packEmbed (afterPower bits)
    (CutoffProbePreparation.cfg none none bits
      (List.replicate (clockLength bits) true) []
      (BoundedBitMachine.packed (clockLength bits) bits)
      (List.replicate (clockLength bits) true)).stk

theorem pack_phase (bits : List Bool) :
    ∃ t ≤ 2 * bits.length + 2 * clockLength bits + 5,
      run t
        ⟨some (.pack .scanBits), embedPack none, afterPower bits⟩ =
      ⟨none, embedPack none, afterPack bits⟩ := by
  let budget := List.replicate (clockLength bits) true
  let c := CutoffProbePreparation.cfg (some .scanBits) none bits budget [] [] []
  let t := 2*bits.length + 2*budget.length + 4
  have hr : ((advance CutoffProbePreparation.program)^[t]) c =
      CutoffProbePreparation.cfg none none bits budget []
        (BoundedBitMachine.packed (clockLength bits) bits)
        (List.replicate (clockLength bits) true) := by
    simpa only [t, c, budget, CutoffProbePreparation.run, List.length_replicate] using
      CutoffProbePreparation.run_correct bits budget
  have hh : (((advance CutoffProbePreparation.program)^[t]) c).l = none := by
    rw [hr]
    rfl
  have he := BitMachineStackEmbedding.outputs packEmbed (afterPower bits)
    Label.pack embedPack readPack (by intro x; rfl) (some .done)
    CutoffProbePreparation.program program (by intro l; rfl) c t hh
  obtain ⟨u, hu, he⟩ := he
  have hi : BitMachineStackEmbedding.cfg packEmbed (afterPower bits)
      Label.pack embedPack (some .done) c =
      ⟨some (.pack .scanBits), embedPack none, afterPower bits⟩ := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, c]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k
    · simpa only [CutoffProbePreparation.cfg, Matrix.cons_val_zero,
        packEmbed, packKey] using (afterPower_at_zero bits).symm
    · simpa only [CutoffProbePreparation.cfg, Matrix.cons_val_one,
        packEmbed, packKey, budget] using (afterPower_at_four bits).symm
    · simpa only [CutoffProbePreparation.cfg, Matrix.cons_val_two,
        packEmbed, packKey] using (afterPower_at_ten bits).symm
    · simpa only [CutoffProbePreparation.cfg, Matrix.cons_val_three,
        packEmbed, packKey] using (afterPower_at_one bits).symm
    · simpa only [CutoffProbePreparation.cfg, Matrix.cons_val_four,
        packEmbed, packKey] using (afterPower_at_two bits).symm
  rw [hi, hr] at he
  have hf : BitMachineStackEmbedding.cfg packEmbed (afterPower bits)
      Label.pack embedPack (some .done)
      (CutoffProbePreparation.cfg none none bits budget []
        (BoundedBitMachine.packed (clockLength bits) bits)
        (List.replicate (clockLength bits) true)) =
      ⟨some .done, embedPack none, afterPack bits⟩ := by
    rfl
  rw [hf] at he
  refine ⟨u+1, ?_, ?_⟩
  · simp only [t, budget, List.length_replicate] at hu
    omega
  · rw [run_add, show run u _ = _ from he]
    rfl

theorem afterPack_output (bits : List Bool) :
    afterPack bits 1 = BoundedBitMachine.packed (clockLength bits) bits := by
  have h := bank_at packEmbed (afterPower bits)
    (CutoffProbePreparation.cfg none none bits
      (List.replicate (clockLength bits) true) []
      (BoundedBitMachine.packed (clockLength bits) bits)
      (List.replicate (clockLength bits) true)).stk 3
  simpa only [afterPack, packEmbed, packKey, CutoffProbePreparation.cfg,
    Matrix.cons_val_three] using h

def rawTime (bits : List Bool) : ℕ :=
  (3*bits.length+4) + 15 + MatrixWeightedPower.powerBound (baseLength bits) 12 +
    (2*bits.length+2*clockLength bits+5)

theorem complete_run (bits : List Bool) :
    ∃ t ≤ rawTime bits,
      run t (init bits) = ⟨none, embedPack none, afterPack bits⟩ := by
  obtain ⟨t₁, ht₁, h₁⟩ := count_phase bits
  have h₂ := seed_phase bits
  obtain ⟨t₃, ht₃, h₃⟩ := power_phase bits
  obtain ⟨t₄, ht₄, h₄⟩ := pack_phase bits
  refine ⟨t₁+15+t₃+t₄, ?_, ?_⟩
  · dsimp [rawTime]
    omega
  · rw [show t₁+15+t₃+t₄ = ((t₁+15)+t₃)+t₄ by omega,
      run_add, run_add, run_add, h₁, h₂]
    change run t₄ (run t₃
      ⟨some (.power (.inr .test)), embedPower (false,false),
        beforePower bits⟩) = _
    rw [h₃]
    exact h₄

noncomputable def machine : BitMachine.Machine :=
  BitMachineEncoding.ofFinite (0 : Stack) (1 : Stack)
    (.count (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (embedCount (none,none)) program

theorem outputsWithin_raw (bits : List Bool) :
    machine.OutputsWithin bits
      (BoundedBitMachine.packed (clockLength bits) bits) (rawTime bits) := by
  obtain ⟨t, ht, hr⟩ := complete_run bits
  apply BitMachineEncoding.outputsWithin_of_raw_run
    (0 : Stack) (1 : Stack)
    (.count (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (embedCount (none,none)) program bits
    (BoundedBitMachine.packed (clockLength bits) bits) t (rawTime bits) ht
  · change (run t (init bits)).l = none
    rw [hr]
  · change (run t (init bits)).stk 1 =
      BoundedBitMachine.packed (clockLength bits) bits
    rw [hr]
    exact afterPack_output bits

end CurrentAdditive.PolynomialFuelPrefix
