import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic

/-!
# Composition of finite Boolean-stack machines

Source: v8 `06-eth.tex`, the fixed deterministic bit-machine convention.
The intermediate output is moved twice, one Boolean stack cell per transition.
The control registers and instruction labels remain finite throughout.
-/

namespace EthInapproximability.CurrentPaper.BitMachineComposition

open Turing
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic

variable {K J L I V W : Type*}

/-- Put a program in the left stack bank, preserving the other registers. -/
def liftStmt (halt : Option I) :
    TM2.Stmt (fun _ : K => Bool) L V →
      TM2.Stmt (fun _ : K ⊕ J => Bool) (L ⊕ I) (V × W)
  | .push k b q => .push (.inl k) (fun v => b v.1) (liftStmt halt q)
  | .peek k f q => .peek (.inl k) (fun v b => (f v.1 b, v.2)) (liftStmt halt q)
  | .pop k f q => .pop (.inl k) (fun v b => (f v.1 b, v.2)) (liftStmt halt q)
  | .load f q => .load (fun v => (f v.1, v.2)) (liftStmt halt q)
  | .branch f q r => .branch (fun v => f v.1) (liftStmt halt q) (liftStmt halt r)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => match halt with | none => .halt | some i => .goto (fun _ => .inr i)

def liftCfg (halt : Option I) (w : W) (foreign : J → List Bool)
    (c : TM2.Cfg (fun _ : K => Bool) L V) :
    TM2.Cfg (fun _ : K ⊕ J => Bool) (L ⊕ I) (V × W) :=
  ⟨match c.l with | none => halt.map Sum.inr | some l => some (.inl l),
    (c.var, w), Sum.elim c.stk foreign⟩

theorem sum_update [DecidableEq K] [DecidableEq J]
    (S : K → List Bool) (T : J → List Bool) (k : K) (bits : List Bool) :
    Function.update (Sum.elim S T) (.inl k) bits =
      Sum.elim (Function.update S k bits) T := by
  funext j
  cases j with
  | inl j =>
      by_cases h : j = k
      · subst j; simp
      · simp [h]
  | inr j => simp

theorem lift_stepAux [DecidableEq K] [DecidableEq J] (halt : Option I)
    (q : TM2.Stmt (fun _ : K => Bool) L V) (v : V) (w : W)
    (S : K → List Bool) (T : J → List Bool) :
    TM2.stepAux (liftStmt halt q) (v, w) (Sum.elim S T) =
      liftCfg halt w T (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simpa only [liftStmt, TM2.stepAux, Sum.elim_inl, sum_update] using ih _ _
  | peek k f q ih => simpa only [liftStmt, TM2.stepAux, Sum.elim_inl] using ih _ _
  | pop k f q ih => simpa only [liftStmt, TM2.stepAux, Sum.elim_inl, sum_update] using ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr => cases h : f v <;> simp [liftStmt, TM2.stepAux, h, ihq, ihr]
  | goto f => rfl
  | halt => cases halt <;> rfl

variable (A B : Machine)

abbrev Stack := Fin A.stackCount ⊕ (Fin B.stackCount ⊕ Unit)
abbrev Label := Fin A.labelCount ⊕ (Fin B.labelCount ⊕ Bool)
abbrev Control := Fin A.controlCount × (Fin B.controlCount × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack A B => Bool) (Label A B) (Control A B)

def stackSwap : (Fin B.stackCount ⊕ (Fin A.stackCount ⊕ Unit)) ≃ Stack A B where
  toFun := Sum.elim (fun k => .inr (.inl k)) (Sum.elim Sum.inl (fun u => .inr (.inr u)))
  invFun := Sum.elim (fun k => .inr (.inl k)) (Sum.elim Sum.inl (fun u => .inr (.inr u)))
  left_inv := by intro k; rcases k with k | (k | k) <;> rfl
  right_inv := by intro k; rcases k with k | (k | k) <;> rfl

def labelSwap : (Fin B.labelCount ⊕ (Fin A.labelCount ⊕ Bool)) ≃ Label A B where
  toFun := Sum.elim (fun k => .inr (.inl k)) (Sum.elim Sum.inl (fun u => .inr (.inr u)))
  invFun := Sum.elim (fun k => .inr (.inl k)) (Sum.elim Sum.inl (fun u => .inr (.inr u)))
  left_inv := by intro k; rcases k with k | (k | k) <;> rfl
  right_inv := by intro k; rcases k with k | (k | k) <;> rfl

def controlSwap : (Fin B.controlCount × (Fin A.controlCount × Option Bool)) ≃ Control A B where
  toFun := fun v => (v.2.1, v.1, v.2.2)
  invFun := fun v => (v.2.1, v.1, v.2.2)
  left_inv := by intro v; rfl
  right_inv := by intro v; rfl

def leftCfg (c : A.Config) : Config A B :=
  liftCfg (some (.inr false)) (B.initial, none) (fun _ => []) c

def rightCfg (v : Fin A.controlCount) (S : Fin A.stackCount → List Bool)
    (c : B.Config) : Config A B :=
  renameCfg (stackSwap A B) (labelSwap A B) (controlSwap A B)
    (liftCfg none (v, none) (Sum.elim S (fun _ => [])) c)

/-- A transfer loop records only one popped Boolean in finite control. -/
def move (source target : Stack A B) (again next : Label A B) :
    TM2.Stmt (fun _ : Stack A B => Bool) (Label A B) (Control A B) :=
  .pop source (fun v b => (v.1, v.2.1, b))
    (.branch (fun v => v.2.2.isSome)
      (.push target (fun v => v.2.2.getD false)
        (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => again))))
      (.load (fun v => (v.1, v.2.1, none)) (.goto (fun _ => next))))

def program : Label A B → TM2.Stmt (fun _ : Stack A B => Bool) (Label A B) (Control A B)
  | .inl l => liftStmt (some (.inr false)) (A.program l)
  | .inr (.inl l) => renameStmt (stackSwap A B) (labelSwap A B) (controlSwap A B)
      (liftStmt none (B.program l))
  | .inr (.inr false) => move A B (.inl A.output) (.inr (.inr ()))
      (.inr (.inr false)) (.inr (.inr true))
  | .inr (.inr true) => move A B (.inr (.inr ())) (.inr (.inl B.input))
      (.inr (.inr true)) (.inr (.inl B.start))

noncomputable def composition : Machine :=
  ofFinite (.inl A.input) (.inr (.inl B.output)) (.inl A.start)
    (A.initial, B.initial, none) (program A B)

theorem left_step (c : A.Config) (h : c.l ≠ none) :
    advance (program A B) (leftCfg A B c) = leftCfg A B (A.step c) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => exact (h rfl).elim
  | some l =>
      simpa only [advance, leftCfg, liftCfg, TM2.step, program,
        Option.getD_some, Machine.step] using
        lift_stepAux (some (Sum.inr false)) (A.program l) v (B.initial, none) S (fun _ => [])

theorem left_run (c : A.Config) (n : ℕ)
    (h : ∀ k < n, (A.run k c).l ≠ none) :
    ((advance (program A B))^[n]) (leftCfg A B c) = leftCfg A B (A.run n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (fun k hk => h k (by omega)),
        left_step A B _ (h n (by omega)), run_succ]

theorem right_step (v : Fin A.controlCount) (S : Fin A.stackCount → List Bool)
    (c : B.Config) :
    advance (program A B) (rightCfg A B v S c) = rightCfg A B v S (B.step c) := by
  rcases c with ⟨l, w, T⟩
  cases l with
  | none => rfl
  | some l =>
      have hr := rename_stepAux (stackSwap A B) (labelSwap A B) (controlSwap A B)
        (liftStmt (K := Fin B.stackCount) (J := Fin A.stackCount ⊕ Unit)
          (I := Fin A.labelCount ⊕ Bool) none (B.program l))
        (w, v, none) (Sum.elim T (Sum.elim S (fun _ => [])))
      rw [lift_stepAux] at hr
      exact hr

theorem right_run (v : Fin A.controlCount) (S : Fin A.stackCount → List Bool)
    (c : B.Config) (n : ℕ) :
    ((advance (program A B))^[n]) (rightCfg A B v S c) =
      rightCfg A B v S (B.run n c) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, right_step, run_succ]

theorem move_empty
    (P : Label A B → TM2.Stmt (fun _ : Stack A B => Bool) (Label A B) (Control A B))
    (source target : Stack A B) (again next : Label A B)
    (hp : P again = move A B source target again next)
    (v : Fin A.controlCount) (w : Fin B.controlCount) (S : Stack A B → List Bool)
    (hs : S source = []) :
    advance P ⟨some again, (v, w, none), S⟩ = ⟨some next, (v, w, none), S⟩ := by
  have hu : Function.update S source [] = S := Function.update_eq_self_iff.mpr hs.symm
  simp [advance, TM2.step, hp, move, TM2.stepAux, hs, hu]

theorem move_cons
    (P : Label A B → TM2.Stmt (fun _ : Stack A B => Bool) (Label A B) (Control A B))
    (source target : Stack A B) (again next : Label A B)
    (hp : P again = move A B source target again next) (hne : target ≠ source)
    (v : Fin A.controlCount) (w : Fin B.controlCount) (S : Stack A B → List Bool)
    (b : Bool) (bits : List Bool) (hs : S source = b :: bits) :
    advance P ⟨some again, (v, w, none), S⟩ =
      ⟨some again, (v, w, none), Function.update (Function.update S source bits)
        target (b :: S target)⟩ := by
  simp [advance, TM2.step, hp, move, TM2.stepAux, hs, hne]

theorem move_run
    (P : Label A B → TM2.Stmt (fun _ : Stack A B => Bool) (Label A B) (Control A B))
    (source target : Stack A B) (again next : Label A B)
    (hp : P again = move A B source target again next) (hne : target ≠ source)
    (v : Fin A.controlCount) (w : Fin B.controlCount)
    (bits : List Bool) (S : Stack A B → List Bool) (hs : S source = bits) :
    ((advance P)^[bits.length + 1]) ⟨some again, (v, w, none), S⟩ =
      ⟨some next, (v, w, none), Function.update (Function.update S source [])
        target (bits.reverse ++ S target)⟩ := by
  induction bits generalizing S with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, List.reverse_nil,
        List.nil_append]
      rw [move_empty A B P source target again next hp v w S hs]
      have hu : Function.update S source [] = S := Function.update_eq_self_iff.mpr hs.symm
      simp [hu]
  | cons b bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      rw [move_cons A B P source target again next hp hne v w S b bits hs]
      rw [ih _ (by simp [Ne.symm hne])]
      congr 1
      funext k
      by_cases ht : k = target
      · subst k; simp [List.reverse_cons, List.append_assoc]
      · by_cases hs' : k = source
        · subst k; simp [Ne.symm hne]
        · simp [ht, hs']

theorem transfer_run (c : A.Config) (hc : c.l = none) :
    ((advance (program A B))^[(c.stk A.output).length + 1 +
      ((c.stk A.output).length + 1)]) (leftCfg A B c) =
    rightCfg A B c.var (Function.update c.stk A.output [])
      (B.init (c.stk A.output)) := by
  let S : Stack A B → List Bool := Sum.elim c.stk (fun _ => [])
  let T := Function.update (Function.update S (.inl A.output) [])
    (.inr (.inr ())) ((c.stk A.output).reverse ++ S (.inr (.inr ())))
  have hfirst := move_run A B (program A B) (.inl A.output) (.inr (.inr ()))
    (.inr (.inr false)) (.inr (.inr true)) rfl (by simp)
    c.var B.initial (c.stk A.output) S rfl
  have hsecond := move_run A B (program A B) (.inr (.inr ())) (.inr (.inl B.input))
    (.inr (.inr true)) (.inr (.inl B.start)) rfl (by simp)
    c.var B.initial (c.stk A.output).reverse T (by
      simp only [T, Function.update_self, S, Sum.elim_inr, List.append_nil])
  have hleft : leftCfg A B c = ⟨some (.inr (.inr false)), (c.var, B.initial, none), S⟩ := by
    simp [leftCfg, liftCfg, hc, S]
  rw [Function.iterate_add_apply, hleft, hfirst]
  change ((advance (program A B))^[(c.stk A.output).length + 1])
    ⟨some (.inr (.inr true)), (c.var, B.initial, none), T⟩ = _
  simp only [List.length_reverse] at hsecond
  rw [hsecond]
  unfold rightCfg renameCfg liftCfg Machine.init
  congr 1
  funext k
  rcases k with k | (k | k)
  · change _ = (Function.update c.stk A.output []) k
    simp only [T, S, Function.update_apply, Sum.elim_inl, Sum.elim_inr,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      ↓reduceIte]
  · change _ = if k = B.input then c.stk A.output else []
    simp only [T, S, Function.update_apply, Sum.elim_inr,
      Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      List.reverse_reverse, List.append_nil, ↓reduceIte]
  · change _ = []
    simp only [T, S, Function.update_apply, Sum.elim_inr,
      Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
      ↓reduceIte]

theorem rawInit_eq_left (input : List Bool) :
    rawInit (Sum.inl A.input) (Sum.inl A.start) (A.initial, B.initial, none) input =
      leftCfg A B (A.init input) := by
  unfold rawInit leftCfg liftCfg Machine.init
  congr 1
  funext k
  rcases k with k | (k | k) <;> simp

/-- Sequential execution costs exactly the two machine executions plus two
linear stack reversals and their empty-stack tests. -/
theorem composition_outputsWithin {input middle output : List Bool} {ta tb : ℕ}
    (ha : A.OutputsWithin input middle ta) (hb : B.OutputsWithin middle output tb) :
    (composition A B).OutputsWithin input output (ta + 2 * middle.length + 2 + tb) := by
  obtain ⟨a, ha_le, ha_halt, ha_out, ha_first⟩ := first_halt A ha
  obtain ⟨b, hb_le, hb_halt, hb_out⟩ := hb
  let c := A.run a (A.init input)
  have hrun : ((advance (program A B))^[b + (middle.length + 1 +
      (middle.length + 1) + a)])
      (rawInit (Sum.inl A.input) (Sum.inl A.start) (A.initial, B.initial, none) input) =
      rightCfg A B c.var (Function.update c.stk A.output [])
        (B.run b (B.init middle)) := by
    rw [rawInit_eq_left, Function.iterate_add_apply,
      Function.iterate_add_apply, left_run A B _ a ha_first]
    have hc : (c.stk A.output).length = middle.length := congrArg List.length ha_out
    rw [← hc, transfer_run A B c ha_halt, ha_out, right_run]
  apply outputsWithin_of_raw_run (Sum.inl A.input) (Sum.inr (Sum.inl B.output))
    (Sum.inl A.start) (A.initial, B.initial, none) (program A B)
    input output (b + (middle.length + 1 + (middle.length + 1) + a))
      (ta + 2 * middle.length + 2 + tb) (by omega)
  · rw [hrun]
    simp only [rightCfg, renameCfg, liftCfg, hb_halt, Option.map_none]
  · rw [hrun]
    exact hb_out

/-- Polynomial time is closed under composition in the concrete finite
Boolean-stack model; no closure axiom or abstract computation oracle is used. -/
theorem polytime_comp {f g : List Bool → List Bool} (hf : Polytime f) (hg : Polytime g) :
    Polytime (g ∘ f) := by
  obtain ⟨A, cf, df, hf⟩ := hf
  obtain ⟨B, cg, dg, hg⟩ := hg
  apply polytime_of_composition_bound A (composition A B) f g cf df cg dg hf
  intro input
  exact composition_outputsWithin A B (hf input) (hg (f input))

end EthInapproximability.CurrentPaper.BitMachineComposition
