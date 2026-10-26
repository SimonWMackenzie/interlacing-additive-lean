import EthInapproximability.CurrentPaper.SmallArm
import EthInapproximability.CurrentPaper.CNFValidatorRuntime
import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# The all-input front of the ETH SAT machine (unit 4, B4-S7 part F: F0 + F1)

Source: frozen v8 `06-eth.tex:238-242`. The front routes every bitstring:

* malformed words reject by the fixed convention (validator output `[false]`);
* valid words with fewer than `N` variables are decided by the small-input scanner
  (`SmallArm`, B4-S2);
* valid words with at least `N` variables are handed, unchanged, to the main arm.

To avoid embedding two machines, the routing stage `scan` emits a *fixed* canonical formula
word `phi b` (a valid formula with exactly `N` variables and exact SAT answer `b`) in the
malformed and small cases, and the word itself in the large case. The main arm then runs on its
own validated domain in every case. `front N Mmain` is ONE fixed machine:
`composition CNFValidator.machine (composition (scan N) Mmain)`, built by the admitted
`BitMachineComposition.composition` (every handoff charged by `composition_outputsWithin`).
The main arm enters as an explicit hypothesis on valid formulas with at least `N` variables.
-/

namespace EthInapproximability.CurrentPaper.Front

open Turing BitMachineEncoding EncodedCNF SmallArm

variable {N : ℕ}

/-- The fixed canonical witnesses: `phi true` = no clauses, `phi false` = `x0 ∧ ¬x0` (as two
three-literal clauses), both with exactly `N` variables. -/
def phiFormula (N : ℕ) : Bool → Formula
  | true => ⟨N, []⟩
  | false => ⟨N, [⟨⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩⟩, ⟨⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩⟩]⟩

theorem phiFormula_valid (hN : 1 ≤ N) (b : Bool) : (phiFormula N b).Valid := by
  cases b
  · intro c hc
    simp only [phiFormula, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl <;>
      exact ⟨by simp [phiFormula]; omega, by simp [phiFormula]; omega, by simp [phiFormula]; omega⟩
  · intro c hc
    simp [phiFormula] at hc

theorem phiFormula_sat (b : Bool) : (Satisfiable (phiFormula N b) ↔ b = true) := by
  cases b
  · simp only [Bool.false_eq_true, iff_false]
    rintro ⟨a, _, ha⟩
    simp only [phiFormula, Formula.eval, List.all_cons, List.all_nil, Clause.eval,
      Literal.eval, Bool.and_true, ↓reduceIte, Bool.or_self, Bool.false_eq_true] at ha
    cases h : a.getD 0 false <;> simp [h] at ha
  · simp only [iff_true]
    exact empty_satisfiable N

def phi (N : ℕ) (b : Bool) : List Bool := encode (phiFormula N b)

theorem satAnswer_phi (hN : 1 ≤ N) (b : Bool) :
    EncodedETHTail.satAnswer (phi N b) = b := by
  unfold EncodedETHTail.satAnswer phi
  have h := encode_mem_iff (phiFormula N b) (phiFormula_valid hN b)
  cases b
  · exact @decide_eq_false _ (Classical.propDecidable _)
      (fun hm => by simpa using (phiFormula_sat (N := N) false).mp (h.mp hm))
  · exact @decide_eq_true _ (Classical.propDecidable _) (h.mpr ((phiFormula_sat true).mpr rfl))

/-! ## The routing scanner -/

abbrev Stack := Fin 3

inductive Label where
  | flag | scan | move
  deriving DecidableEq, Fintype

abbrev Ctl (N : ℕ) := St N × Fin (N + 1) × Option Bool

def cntUpd (x : St N) (cnt : Fin (N + 1)) : Option Bool → Fin (N + 1)
  | some true => if x.ph = .unary then capN (cnt.val + 1) else cnt
  | _ => cnt

def pushAll (k : Stack) : List Bool → TM2.Stmt (fun _ : Stack => Bool) Label (Ctl N) →
    TM2.Stmt (fun _ : Stack => Bool) Label (Ctl N)
  | [], q => q
  | b :: bs, q => pushAll k bs (.push k (fun _ => b) q)

theorem stepAux_pushAll (k : Stack) (l : List Bool)
    (q : TM2.Stmt (fun _ : Stack => Bool) Label (Ctl N)) (v : Ctl N)
    (S : Stack → List Bool) :
    TM2.stepAux (pushAll k l q) v S = TM2.stepAux q v (Function.update S k (l ++ S k)) := by
  induction l generalizing q S with
  | nil => simp [pushAll]
  | cons b bs ih =>
      simp only [pushAll]
      rw [ih]
      simp [TM2.stepAux, Function.update_idem]

/-- Emit `phi N b` on the (empty) output stack and halt. -/
def emit (N : ℕ) (b : Bool) : TM2.Stmt (fun _ : Stack => Bool) Label (Ctl N) :=
  pushAll 1 (phi N b) .halt

def program (N : ℕ) : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Ctl N)
  | .flag => .pop 0 (fun v b => (v.1, v.2.1, b))
      (.branch (fun v => v.2.2 == some true) (.goto (fun _ => .scan)) (emit N false))
  | .scan => .pop 0 (fun v b => (delta v.1 b, cntUpd v.1 v.2.1 b, b))
      (.branch (fun v => isDone v.1)
        (.branch (fun v => decide (v.2.1.val < N))
          (.branch (fun v => answer v.1) (emit N true) (emit N false))
          (.goto (fun _ => .move)))
        (.push 2 (fun v => v.2.2.getD false) (.goto (fun _ => .scan))))
  | .move => .pop 2 (fun v b => (v.1, v.2.1, b))
      (.branch (fun v => v.2.2.isSome)
        (.push 1 (fun v => v.2.2.getD false) (.goto (fun _ => .move))) .halt)

def initCtl (N : ℕ) : Ctl N := (init (N := N), capN 0, none)

noncomputable def scanMachine (N : ℕ) : BitMachine.Machine :=
  ofFinite (0 : Stack) 1 Label.flag (initCtl N) (program N)

abbrev Config (N : ℕ) := TM2.Cfg (fun _ : Stack => Bool) Label (Ctl N)

def cstep (p : St N × Fin (N + 1)) (b : Bool) : St N × Fin (N + 1) :=
  (delta p.1 (some b), cntUpd p.1 p.2 (some b))

theorem scan_run (bits : List Bool) (x : St N) (cnt : Fin (N + 1)) (o : Option Bool)
    (hx : isDone x = false) (S : Stack → List Bool) (hS : S 0 = bits) :
    ∃ o' : Option Bool, ((advance (program N))^[bits.length])
        (⟨some .scan, (x, cnt, o), S⟩ : Config N) =
      ⟨some .scan, ((bits.foldl cstep (x, cnt)).1, (bits.foldl cstep (x, cnt)).2, o'),
        fun k => if k = 0 then [] else if k = 2 then bits.reverse ++ S 2 else S k⟩ ∧
    isDone (bits.foldl cstep (x, cnt)).1 = false := by
  induction bits generalizing x cnt o S with
  | nil =>
      refine ⟨o, ?_, hx⟩
      simp only [List.length_nil, Function.iterate_zero, id_eq, List.foldl_nil,
        List.reverse_nil, List.nil_append]
      congr 1
      funext k
      fin_cases k <;> simp [hS]
  | cons b xs ih =>
      have hd := delta_some_not_done x hx b
      have hstep : advance (program N) (⟨some .scan, (x, cnt, o), S⟩ : Config N) =
          ⟨some .scan, (delta x (some b), cntUpd x cnt (some b), some b),
            Function.update (Function.update S 0 xs) 2 (b :: S 2)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, hS, hd]
      rw [List.length_cons, Function.iterate_succ_apply, hstep]
      have hS2 : (Function.update (Function.update S 0 xs) 2 (b :: S 2)) 0 = xs := by
        simp [Function.update_apply]
      obtain ⟨o', h1, h2⟩ := ih (delta x (some b)) (cntUpd x cnt (some b)) (some b) hd _ hS2
      refine ⟨o', ?_, h2⟩
      rw [h1]
      simp only [List.foldl_cons, cstep]
      congr 1
      funext k
      fin_cases k <;> simp [Function.update_apply]

theorem move_run (buf out : List Bool) (v : Ctl N) (S : Stack → List Bool)
    (hb : S 2 = buf) (ho : S 1 = out) :
    ∃ v' : Ctl N, ((advance (program N))^[buf.length + 1])
        (⟨some .move, v, S⟩ : Config N) =
      ⟨none, v', fun k => if k = 2 then [] else if k = 1 then buf.reverse ++ out else S k⟩ := by
  induction buf generalizing v S out with
  | nil =>
      refine ⟨(v.1, v.2.1, none), ?_⟩
      simp only [List.length_nil, zero_add, Function.iterate_one, List.reverse_nil,
        List.nil_append]
      have hs : advance (program N) (⟨some .move, v, S⟩ : Config N) =
          ⟨none, (v.1, v.2.1, none), Function.update S 2 []⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, hb]
      rw [hs]
      congr 1
      funext k
      fin_cases k <;> simp [Function.update_apply, hb, ho]
  | cons b bs ih =>
      have hstep : advance (program N) (⟨some .move, v, S⟩ : Config N) =
          ⟨some .move, (v.1, v.2.1, some b),
            Function.update (Function.update S 2 bs) 1 (b :: out)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, hb, ho]
      rw [List.length_cons, Function.iterate_succ_apply, hstep]
      obtain ⟨v', hv'⟩ := ih (b :: out) (v.1, v.2.1, some b)
        (Function.update (Function.update S 2 bs) 1 (b :: out))
        (by simp [Function.update_apply]) (by simp [Function.update_apply])
      refine ⟨v', ?_⟩
      rw [hv']
      congr 1
      funext k
      fin_cases k <;> simp [Function.update_apply]

end EthInapproximability.CurrentPaper.Front
