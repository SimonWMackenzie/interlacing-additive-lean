import EthInapproximability.CurrentPaper.SamplerMachineAccumulate
import EthInapproximability.CurrentPaper.SamplerMachineShift
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import EthInapproximability.CurrentPaper.SamplerHorner
import EthInapproximability.CurrentPaper.SamplerPolynomialProduct

/-!
# A uniform coefficient-word multiplication controller

Source: v8 `E-exact-details.tex`, polynomial-basis arithmetic in
`lem:exact-families`. The controller reads multiplier bits from high to low,
shifts the stored accumulator modulo the stored polynomial, then adds the
selected multiplicand. Local routines preserve all foreign stacks.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineProduct

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open ExecutableSmallBiasSampler SamplerMachine

abbrev Stack := Fin 4 ⊕ Fin 2
abbrev Label := SamplerMachineAccumulate.Label ⊕ (SamplerMachineShift.Label ⊕ Unit)
abbrev Control := SamplerMachineAccumulate.Control × (SamplerMachineShift.Control × Unit)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

/-- Shift's local bank is `(modulus, accumulator, scratch)`; the foreign
bank is `(multiplicand, remaining multiplier, second scratch)`. -/
def shiftStackSwap : (Fin 3 ⊕ Fin 3) ≃ Stack where
  toFun := Sum.elim
    (fun i => if i = 0 then .inr 0 else if i = 1 then .inl 0 else .inl 2)
    (fun i => if i = 0 then .inl 1 else if i = 1 then .inr 1 else .inl 3)
  invFun := Sum.elim
    (fun i => if i = 0 then .inl 1 else if i = 1 then .inr 0
      else if i = 2 then .inl 2 else .inr 2)
    (fun i => if i = 0 then .inl 0 else .inr 1)
  left_inv := by intro i; rcases i with i | i <;> fin_cases i <;> rfl
  right_inv := by intro i; rcases i with i | i <;> fin_cases i <;> rfl

def shiftLabelSwap :
    (SamplerMachineShift.Label ⊕ (SamplerMachineAccumulate.Label ⊕ Unit)) ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inl l)) (Sum.elim Sum.inl (fun u => .inr (.inr u)))
  invFun := Sum.elim (fun l => .inr (.inl l)) (Sum.elim Sum.inl (fun u => .inr (.inr u)))
  left_inv := by intro l; rcases l with l | (l | l) <;> rfl
  right_inv := by intro l; rcases l with l | (l | l) <;> rfl

def shiftControlSwap :
    (SamplerMachineShift.Control × (SamplerMachineAccumulate.Control × Unit)) ≃ Control where
  toFun := fun s => (s.2.1, s.1, s.2.2)
  invFun := fun s => (s.2.1, s.1, s.2.2)
  left_inv := by intro s; rfl
  right_inv := by intro s; rfl

def initial : Control := ((false, none, none), SamplerMachineShift.initial, ())

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inr ())) (SamplerMachineAccumulate.program l)
  | .inr (.inl l) => renameStmt shiftStackSwap shiftLabelSwap shiftControlSwap
      (liftStmt (some (.inl .scan)) (SamplerMachineShift.program l))
  | .inr (.inr ()) => pop (.inr 1) (fun s b => ((false, b, none), s.2))
      (branch (fun s => s.1.2.1.isSome)
        (load (fun s => ((s.1.2.1.getD false, none, none), SamplerMachineShift.initial, ()))
          (goto (fun _ => .inr (.inl .scan))))
        (load (fun _ => initial) halt))

def foreign (c v : List Bool) : Fin 2 → List Bool :=
  fun i => if i = 0 then c else v

def cfg (l : Option Label) (s : Control)
    (a u sa su c v : List Bool) : Config :=
  ⟨l, s, Sum.elim (SamplerMachineAccumulate.stackContents a u sa su) (foreign c v)⟩

def run (n : ℕ) (q : Config) := ((advance program)^[n]) q

private theorem renameStmt_inverse
    {K K' L L' V V' : Type*} (ek : K ≃ K') (el : L ≃ L') (ev : V ≃ V')
    (q : TM2.Stmt (fun _ : K => Bool) L V) :
    renameStmt ek.symm el.symm ev.symm (renameStmt ek el ev q) = q := by
  induction q <;> simp_all [renameStmt]

private theorem renameCfg_inverse
    {K K' L L' V V' : Type*} (ek : K ≃ K') (el : L ≃ L') (ev : V ≃ V')
    (q : TM2.Cfg (fun _ : K => Bool) L V) :
    renameCfg ek.symm el.symm ev.symm (renameCfg ek el ev q) = q := by
  rcases q with ⟨l, v, s⟩
  simp [renameCfg]

/-- The same global finite program, expressed in Shift's stack/control order. -/
def shiftView :
    (SamplerMachineShift.Label ⊕ (SamplerMachineAccumulate.Label ⊕ Unit)) →
      TM2.Stmt (fun _ : Fin 3 ⊕ Fin 3 => Bool)
        (SamplerMachineShift.Label ⊕ (SamplerMachineAccumulate.Label ⊕ Unit))
        (SamplerMachineShift.Control × (SamplerMachineAccumulate.Control × Unit)) :=
  fun l => renameStmt shiftStackSwap.symm shiftLabelSwap.symm shiftControlSwap.symm
    (program (shiftLabelSwap l))

theorem shiftView_local (l : SamplerMachineShift.Label) :
    shiftView (.inl l) = liftStmt (some (.inl .scan)) (SamplerMachineShift.program l) := by
  exact renameStmt_inverse shiftStackSwap shiftLabelSwap shiftControlSwap _

theorem shiftView_run (q : TM2.Cfg (fun _ : Fin 3 ⊕ Fin 3 => Bool)
    (SamplerMachineShift.Label ⊕ (SamplerMachineAccumulate.Label ⊕ Unit))
    (SamplerMachineShift.Control × (SamplerMachineAccumulate.Control × Unit))) (t : ℕ) :
    run t (renameCfg shiftStackSwap shiftLabelSwap shiftControlSwap q) =
      renameCfg shiftStackSwap shiftLabelSwap shiftControlSwap (((advance shiftView)^[t]) q) := by
  have hp : (fun l => renameStmt shiftStackSwap shiftLabelSwap shiftControlSwap
      (shiftView (shiftLabelSwap.symm l))) = program := by
    funext l
    simp only [shiftView, Equiv.apply_symm_apply]
    exact renameStmt_inverse shiftStackSwap.symm shiftLabelSwap.symm shiftControlSwap.symm _
  have h := rename_run shiftStackSwap shiftLabelSwap shiftControlSwap shiftView q t
  rw [hp] at h
  exact h

def shiftForeign (u v : List Bool) : Fin 3 → List Bool :=
  fun i => if i = 0 then u else if i = 1 then v else []

theorem shiftCfg_eq (l : Option SamplerMachineShift.Label)
    (s : SamplerMachineShift.Control) (b : Bool) (a u c v : List Bool) :
    renameCfg shiftStackSwap shiftLabelSwap shiftControlSwap
      (liftCfg (some (.inl SamplerMachineAccumulate.Label.scan)) ((b, none, none), ())
        (shiftForeign u v) (SamplerMachineShift.cfg l s c a [])) =
      cfg (match l with | none => some (.inl .scan) | some k => some (.inr (.inl k)))
        ((b, none, none), s, ()) a u [] [] c v := by
  cases l <;>
    simp only [renameCfg, liftCfg, SamplerMachineShift.cfg, cfg, Option.map_some]
  all_goals
    congr 1
    funext k
    rcases k with k | k <;> fin_cases k <;> rfl

theorem accumulateCfg_eq (l : Option SamplerMachineAccumulate.Label)
    (b : Bool) (p q : Option Bool) (a u c v : List Bool) :
    liftCfg (some (.inr ())) (SamplerMachineShift.initial, ()) (foreign c v)
      (SamplerMachineAccumulate.cfg l (b, p, q) a u [] []) =
      cfg (match l with | none => some (.inr (.inr ())) | some k => some (.inl k))
        ((b, p, q), SamplerMachineShift.initial, ()) a u [] [] c v := by
  cases l <;> rfl

theorem accumulate_call {n : ℕ} (c : BinaryWord n) (b : ZMod 2) (a u : BinaryWord n) (v : List Bool) :
    ∃ t ≤ 2 * n + 2,
      run t (cfg (some (.inl .scan))
        ((encodeBit b, none, none), SamplerMachineShift.initial, ())
        (encodeWord a) (encodeWord u) [] [] (encodeWord c) v) =
      cfg (some (.inr (.inr ())))
        ((encodeBit b, none, none), SamplerMachineShift.initial, ())
        (encodeWord (wordAdd a (wordScale b u))) (encodeWord u) [] []
        (encodeWord c) v := by
  have hl := SamplerMachineAccumulate.run_wordAddScale b a u
  obtain ⟨t, ht, hr⟩ := BitMachineSubroutine.lift_outputs
    SamplerMachineAccumulate.program program (some (.inr ())) (fun _ => rfl)
    (SamplerMachineShift.initial, ()) (foreign (encodeWord c) v)
    (SamplerMachineAccumulate.cfg (some .scan) (encodeBit b, none, none)
      (encodeWord a) (encodeWord u) [] []) (2 * n + 2) (by rw [← SamplerMachineAccumulate.run, hl]; rfl)
  refine ⟨t, ht, ?_⟩
  rw [← SamplerMachineAccumulate.run, hl, accumulateCfg_eq, accumulateCfg_eq] at hr
  exact hr

theorem shift_call {n : ℕ} (c : BinaryWord n) (b : Bool) (a u : BinaryWord n) (v : List Bool) :
    ∃ t ≤ 2 * n + 2,
      run t (cfg (some (.inr (.inl .scan)))
        ((b, none, none), SamplerMachineShift.initial, ())
        (encodeWord a) (encodeWord u) [] [] (encodeWord c) v) =
      cfg (some (.inl .scan)) ((b, none, none), SamplerMachineShift.initial, ())
        (encodeWord (SamplerMachineShift.shiftWith c a)) (encodeWord u) [] [] (encodeWord c) v := by
  have hl := SamplerMachineShift.run_wordShiftWith c a
  obtain ⟨t, ht, hr⟩ := BitMachineSubroutine.lift_outputs
    SamplerMachineShift.program shiftView (some (.inl SamplerMachineAccumulate.Label.scan))
    shiftView_local ((b, none, none), ()) (shiftForeign (encodeWord u) v)
    (SamplerMachineShift.cfg (some .scan) SamplerMachineShift.initial
      (encodeWord c) (encodeWord a) []) (2 * n + 2) (by
        rw [← SamplerMachineShift.run, hl]; rfl)
  refine ⟨t, ht, ?_⟩
  have hh := congrArg (renameCfg shiftStackSwap shiftLabelSwap shiftControlSwap) hr
  rw [← shiftView_run, ← SamplerMachineShift.run, hl, shiftCfg_eq, shiftCfg_eq] at hh
  exact hh

def decodeBit (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] theorem encode_decodeBit (b : Bool) : encodeBit (decodeBit b) = b := by
  cases b <;> decide

private theorem step_loop_cons {n : ℕ} (c : BinaryWord n) (s : Control)
    (a u : BinaryWord n) (b : Bool) (v : List Bool) :
    advance program (cfg (some (.inr (.inr ()))) s
      (encodeWord a) (encodeWord u) [] [] (encodeWord c) (b :: v)) =
      cfg (some (.inr (.inl .scan))) ((b, none, none), SamplerMachineShift.initial, ())
        (encodeWord a) (encodeWord u) [] [] (encodeWord c) v := by
  dsimp only [advance, TM2.step, TM2.stepAux, program, cfg, foreign, Sum.elim_inr]
  simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, List.head?_cons,
    List.tail_cons, Option.isSome_some, Option.getD_some, Bool.cond_true]
  congr 1
  funext k
  rcases k with k | k
  · simp
  · fin_cases k <;> rfl

private theorem step_loop_nil {n : ℕ} (c : BinaryWord n) (s : Control) (a u : BinaryWord n) :
    advance program (cfg (some (.inr (.inr ()))) s
      (encodeWord a) (encodeWord u) [] [] (encodeWord c) []) =
      cfg none initial (encodeWord a) (encodeWord u) [] [] (encodeWord c) [] := by
  dsimp only [advance, TM2.step, TM2.stepAux, program, cfg, foreign, Sum.elim_inr]
  simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, List.head?_nil,
    List.tail_nil, Option.isSome_none, Option.getD_some, Bool.cond_false]
  congr 1
  funext k
  rcases k with k | k
  · simp
  · fin_cases k <;> rfl

/-- The semantic update executed by one pass through the actual controller. -/
def hornerStep {n : ℕ} (c u a : BinaryWord n) (b : Bool) : BinaryWord n :=
  wordAdd (SamplerMachineShift.shiftWith c a) (wordScale (decodeBit b) u)

theorem iteration {n : ℕ} (c : BinaryWord n) (s : Control) (a u : BinaryWord n) (b : Bool) (v : List Bool) :
    ∃ t ≤ 4 * n + 5,
      run t (cfg (some (.inr (.inr ()))) s
        (encodeWord a) (encodeWord u) [] [] (encodeWord c) (b :: v)) =
      cfg (some (.inr (.inr ())))
        ((b, none, none), SamplerMachineShift.initial, ())
        (encodeWord (hornerStep c u a b)) (encodeWord u) [] [] (encodeWord c) v := by
  obtain ⟨ts, hts, hs⟩ := shift_call c b a u v
  obtain ⟨ta, hta, ha⟩ := accumulate_call c (decodeBit b) (SamplerMachineShift.shiftWith c a) u v
  simp only [encode_decodeBit] at ha
  refine ⟨ta + ts + 1, by omega, ?_⟩
  simp only [run, Function.iterate_succ_apply, step_loop_cons]
  rw [Function.iterate_add_apply]
  change run ta (run ts _) = _
  rw [hs, ha]
  rfl

/-- Actual bounded execution of the finite controller for any stored list
of multiplier bits. The modulus, multiplicand, and cleared work stacks
are retained in the complete terminal configuration. -/
theorem run_horner {n : ℕ} (c : BinaryWord n) (s : Control) (a u : BinaryWord n) (v : List Bool) :
    ∃ t ≤ v.length * (4 * n + 5) + 1,
      run t (cfg (some (.inr (.inr ()))) s
        (encodeWord a) (encodeWord u) [] [] (encodeWord c) v) =
      cfg none initial (encodeWord (v.foldl (hornerStep c u) a)) (encodeWord u)
        [] [] (encodeWord c) [] := by
  induction v generalizing s a with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      exact step_loop_nil c s a u
  | cons b v ih =>
      obtain ⟨ti, hti, hi⟩ := iteration c s a u b v
      obtain ⟨tr, htr, hr⟩ := ih ((b, none, none), SamplerMachineShift.initial, ())
        (hornerStep c u a b)
      refine ⟨tr + ti, ?_, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · simp only [run, Function.iterate_add_apply]
        change run tr (run ti _) = _
        rw [hi, hr]
        rfl

/-- The uniform six-stack program implements multiplication in the exact
selected polynomial basis. The modulus and multiplicand are preserved,
and the work stacks are empty at exit. This component starts with the
modulus, zero accumulator, and reversed multiplier already stored; producing
those inputs is charged by the enclosing sampler controller. -/
theorem run_wordMul {n : ℕ} (u v : BinaryWord n) :
    ∃ t ≤ n * (4 * n + 5) + 1,
      run t (cfg (some (.inr (.inr ()))) initial
        (encodeWord (fun _ : Fin n => (0 : ZMod 2))) (encodeWord u) [] []
        (encodeWord (chosenWord n)) (encodeWord v).reverse) =
      cfg none initial (encodeWord (wordMul n u v)) (encodeWord u) [] []
        (encodeWord (chosenWord n)) [] := by
  have heq : (encodeWord v).reverse.foldl (hornerStep (chosenWord n) u)
      (fun _ => 0) = wordMul n u v := by
    have hstep : hornerStep (chosenWord n) u =
        fun a b => wordAdd (wordShift n a) (wordScale (SamplerHorner.decodeBit b) u) := by
      funext a b
      simp [hornerStep, SamplerMachineShift.shiftWith_chosenWord,
        SamplerHorner.decodeBit, decodeBit]
    rw [hstep]
    exact SamplerHorner.horner_encodeWord_reverse u v
  simpa only [List.length_reverse, encodeWord_length, heq] using
    run_horner (chosenWord n) initial (fun _ => 0) u (encodeWord v).reverse

/-- The same literal program computes a trial monic polynomial product
before an irreducible polynomial has been selected. The supplied modulus
has zero lower coefficients; all degree-`n` output coefficients fit in
width `n+1`, so no product information is discarded. -/
theorem run_monicProduct {n k : ℕ} (hk : k ≤ n)
    (u : BinaryWord k) (v : BinaryWord (n - k)) :
    ∃ t ≤ (n + 1) * (4 * (n + 1) + 5) + 1,
      run t (cfg (some (.inr (.inr ()))) initial
        (encodeWord (fun _ : Fin (n + 1) => (0 : ZMod 2)))
        (encodeWord (fun i : Fin (n + 1) => monicCoeff k u i.val)) [] []
        (encodeWord (fun _ : Fin (n + 1) => (0 : ZMod 2)))
        (encodeWord (fun i : Fin (n + 1) => monicCoeff (n - k) v i.val)).reverse) =
      cfg none initial
        (encodeWord (fun i : Fin (n + 1) => productCoeff k (n - k) u v i.val))
        (encodeWord (fun i : Fin (n + 1) => monicCoeff k u i.val)) [] []
        (encodeWord (fun _ : Fin (n + 1) => (0 : ZMod 2))) [] := by
  have heq :
      (encodeWord (fun i : Fin (n + 1) => monicCoeff (n - k) v i.val)).reverse.foldl
        (hornerStep (fun _ : Fin (n + 1) => 0)
          (fun i : Fin (n + 1) => monicCoeff k u i.val)) (fun _ => 0) =
        fun i : Fin (n + 1) => productCoeff k (n - k) u v i.val := by
    have hstep : hornerStep (fun _ : Fin (n + 1) => 0)
          (fun i : Fin (n + 1) => monicCoeff k u i.val) =
        fun a b => wordAdd (SamplerMachineShift.shiftWith (fun _ => 0) a)
          (wordScale (SamplerHorner.decodeBit b)
            (fun i : Fin (n + 1) => monicCoeff k u i.val)) := by
      funext a b
      rfl
    rw [hstep]
    exact SamplerPolynomialProduct.hornerWith_zero_monicProduct hk u v
  simpa only [List.length_reverse, encodeWord_length, heq] using
    run_horner (fun _ : Fin (n + 1) => 0) initial (fun _ => 0)
      (fun i : Fin (n + 1) => monicCoeff k u i.val)
      (encodeWord (fun i : Fin (n + 1) => monicCoeff (n - k) v i.val)).reverse

end EthInapproximability.CurrentPaper.SamplerMachineProduct
