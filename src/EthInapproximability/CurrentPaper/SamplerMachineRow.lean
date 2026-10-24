import EthInapproximability.CurrentPaper.SamplerMachineCoordinate
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Writing all coordinates for one field-pair seed

Source: locked v8 Appendix E, `lem:exact-families`. Two saved coefficient
words specify a seed. A physical unary counter specifies how many sampler
coordinates to write. Each round copies the seed and the current unary
index into the implemented coordinate evaluator, appends its bit to the
output stack, and advances the index. Source copies, index maintenance,
arithmetic, and cleanup are all literal finite-stack computation.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineRow

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open ExecutableSmallBiasSampler SamplerMachine

inductive Admin where
  | loop | copy (i : Fin 3) (l : BitMachineCopy.Label) | call | emit | clear
  deriving DecidableEq, Fintype

abbrev Stack := SamplerMachineCoordinate.Stack ⊕ Fin 6
abbrev Label := SamplerMachineCoordinate.Label ⊕ Admin
abbrev Control := SamplerMachineCoordinate.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (SamplerMachineCoordinate.initial, none)

def copySource (i : Fin 3) : Stack := .inr ⟨i.val, by omega⟩
def copyTarget (i : Fin 3) : Stack := .inl
  (if i = 0 then .inl (.inl (.inl 0))
   else if i = 1 then .inl (.inl (.inl 1)) else .inl (.inr ()))

def copyRegister (i : Fin 3) : Fin 3 ↪ Stack where
  toFun := fun k => if k = 0 then copySource i else if k = 1 then copyTarget i else .inr 5
  inj' := by
    intro a b h
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp_all [copySource, copyTarget]

def copyNext (i : Fin 3) : Label :=
  if h : i.val + 1 < 3 then .inr (.copy ⟨i.val + 1, h⟩ .scan) else .inr .call

def copyEmbed (b : Option Bool) : Control := (SamplerMachineCoordinate.initial, b)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some .emit) (SamplerMachineCoordinate.program l)
  | .inr .loop => pop (.inr 3) (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (load (fun _ => initial) (goto (fun _ => .inr (.copy 0 .scan))))
        (goto (fun _ => .inr .clear)))
  | .inr (.copy i l) => BitMachineStackEmbedding.stmt (copyRegister i)
      (fun l => .inr (.copy i l)) copyEmbed Prod.snd (some (copyNext i)) (BitMachineCopy.program l)
  | .inr .call => load (fun _ => initial) (goto (fun _ => .inl (.inl (.inr .loop))))
  | .inr .emit => push (.inr 4) (fun s => SamplerMachineCoordinate.result s.1)
      (push (.inr 2) (fun _ => true)
        (load (fun _ => initial) (goto (fun _ => .inr .loop))))
  | .inr .clear => pop (.inr 2) (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (goto (fun _ => .inr .clear))
        (load (fun _ => initial) halt))

def foreign (x y index budget out work : List Bool) : Fin 6 → List Bool :=
  fun i => if i = 0 then x else if i = 1 then y else if i = 2 then index
    else if i = 3 then budget else if i = 4 then out else work

def cfg (l : Option Label) (s : Control) (a u c fuel : List Bool)
    (x y index budget out work : List Bool) : Config :=
  ⟨l, s, Sum.elim (SamplerMachineCoordinate.cfg none s.1 a u c fuel []).stk
    (foreign x y index budget out work)⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_add (t s : ℕ) (q : Config) : run (t + s) q = run t (run s q) :=
  Function.iterate_add_apply _ _ _ _

private theorem run_zero (q : Config) : run 0 q = q := rfl

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

theorem copy_bank_initial (i : Fin 3) (S : Stack → List Bool) (q : List Bool)
    (hs : S (copySource i) = q) (ht : S (copyTarget i) = []) (hw : S (.inr 5) = []) :
    BitMachineStackEmbedding.bank (copyRegister i) S (BitMachineCopy.stackContents q [] []) = S := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;> simp only [copyRegister, BitMachineCopy.stackContents] <;> simp [hs, ht, hw]

theorem copy_bank_final (i : Fin 3) (S : Stack → List Bool) (q : List Bool)
    (hs : S (copySource i) = q) (hw : S (.inr 5) = []) :
    BitMachineStackEmbedding.bank (copyRegister i) S (BitMachineCopy.stackContents q q []) =
      Function.update S (copyTarget i) q := by
  classical
  funext k
  by_cases hk : ∃ j, copyRegister i j = k
  · obtain ⟨j, rfl⟩ := hk
    rw [BitMachineStackEmbedding.bank_at]
    fin_cases i <;> fin_cases j <;>
      simp_all [copyRegister, copySource, copyTarget, BitMachineCopy.stackContents]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hk, Function.update_of_ne]
    intro he
    exact hk ⟨1, he.symm⟩

/-- A literal source-preserving copy into one empty local argument bank. -/
theorem copy_call (i : Fin 3) (S : Stack → List Bool) (q : List Bool)
    (hs : S (copySource i) = q) (ht : S (copyTarget i) = []) (hw : S (.inr 5) = []) :
    ∃ t ≤ 2 * q.length + 2,
      run t ⟨some (.inr (.copy i .scan)), initial, S⟩ =
        ⟨some (copyNext i), initial, Function.update S (copyTarget i) q⟩ := by
  have hr := BitMachineCopy.run_correct none q []
  simp only [List.append_nil] at hr
  have hh : (BitMachineCopy.run (2 * q.length + 2)
      (BitMachineCopy.cfg (some .scan) none q [] [])).l = none := by rw [hr]; rfl
  obtain ⟨t, ht', hrun⟩ := BitMachineStackEmbedding.outputs (copyRegister i) S
    (fun l => .inr (.copy i l)) copyEmbed Prod.snd (fun _ => rfl) (some (copyNext i))
    BitMachineCopy.program program (fun _ => rfl)
    (BitMachineCopy.cfg (some .scan) none q [] []) (2 * q.length + 2) hh
  dsimp only [BitMachineCopy.run] at hr
  rw [hr] at hrun
  dsimp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, BitMachineCopy.cfg, Option.map_some] at hrun
  rw [copy_bank_initial i S q hs ht hw, copy_bank_final i S q hs hw] at hrun
  exact ⟨t, ht', hrun⟩

theorem prepare_run (x y index c budget out : List Bool) :
    ∃ t ≤ 2 * x.length + 2 * y.length + 2 * index.length + 6,
      run t (cfg (some (.inr (.copy 0 .scan))) initial [] [] c [] x y index budget out []) =
        cfg (some (.inr .call)) initial x y c index x y index budget out [] := by
  obtain ⟨tx, htx, hx⟩ := copy_call 0
    (cfg none initial [] [] c [] x y index budget out []).stk x rfl rfl rfl
  obtain ⟨ty, hty, hy⟩ := copy_call 1
    (cfg none initial x [] c [] x y index budget out []).stk y rfl rfl rfl
  obtain ⟨ti, hti, hi⟩ := copy_call 2
    (cfg none initial x y c [] x y index budget out []).stk index rfl rfl rfl
  have update_x : Function.update (cfg none initial [] [] c [] x y index budget out []).stk
      (copyTarget 0) x = (cfg none initial x [] c [] x y index budget out []).stk := by
    funext k
    rcases k with (((k | k) | k) | k) | k <;> (try fin_cases k) <;> rfl
  have update_y : Function.update (cfg none initial x [] c [] x y index budget out []).stk
      (copyTarget 1) y = (cfg none initial x y c [] x y index budget out []).stk := by
    funext k
    rcases k with (((k | k) | k) | k) | k <;> (try fin_cases k) <;> rfl
  have update_i : Function.update (cfg none initial x y c [] x y index budget out []).stk
      (copyTarget 2) index = (cfg none initial x y c index x y index budget out []).stk := by
    funext k
    rcases k with (((k | k) | k) | k) | k <;> (try fin_cases k) <;> rfl
  rw [update_x] at hx
  rw [update_y] at hy
  rw [update_i] at hi
  change run tx (cfg (some (.inr (.copy 0 .scan))) initial [] [] c [] x y index budget out []) =
    cfg (some (.inr (.copy 1 .scan))) initial x [] c [] x y index budget out [] at hx
  change run ty (cfg (some (.inr (.copy 1 .scan))) initial x [] c [] x y index budget out []) =
    cfg (some (.inr (.copy 2 .scan))) initial x y c [] x y index budget out [] at hy
  change run ti (cfg (some (.inr (.copy 2 .scan))) initial x y c [] x y index budget out []) =
    cfg (some (.inr .call)) initial x y c index x y index budget out [] at hi
  exact ⟨ti + (ty + tx), by omega, by rw [run_add ti (ty + tx), run_add ty tx, hx, hy, hi]⟩

private theorem step_loop_cons (c x y index budget out : List Bool) (b : Bool) :
    TM2.step program (cfg (some (.inr .loop)) initial [] [] c [] x y index (b :: budget) out []) =
      some (cfg (some (.inr (.copy 0 .scan))) initial [] [] c [] x y index budget out []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign, Sum.elim_inr]
  simp only [show (3 : Fin 6) ≠ 0 by decide, show (3 : Fin 6) ≠ 1 by decide,
    show (3 : Fin 6) ≠ 2 by decide, ↓reduceIte, List.head?_cons, List.tail_cons,
    Option.isSome_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rfl
  · fin_cases k <;> rfl

private theorem step_loop_nil (c x y index out : List Bool) :
    TM2.step program (cfg (some (.inr .loop)) initial [] [] c [] x y index [] out []) =
      some (cfg (some (.inr .clear)) initial [] [] c [] x y index [] out []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign, Sum.elim_inr]
  simp only [show (3 : Fin 6) ≠ 0 by decide, show (3 : Fin 6) ≠ 1 by decide,
    show (3 : Fin 6) ≠ 2 by decide, ↓reduceIte, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rfl
  · fin_cases k <;> rfl

private theorem step_call (a u c fuel x y index budget out : List Bool) :
    TM2.step program (cfg (some (.inr .call)) initial a u c fuel x y index budget out []) =
      some (cfg (some (.inl (.inl (.inr .loop)))) initial a u c fuel x y index budget out []) := rfl

def coordinateControl (bit : Bool) : SamplerMachineCoordinate.Control :=
  (SamplerMachinePower.initial, SamplerMachineTrace.initial, bit, none)

private theorem step_emit (bit : Bool) (c x y index budget out : List Bool) :
    TM2.step program (cfg (some (.inr .emit)) (coordinateControl bit, none)
      [] [] c [] x y index budget out []) =
      some (cfg (some (.inr .loop)) initial [] [] c [] x y (true :: index) budget (bit :: out) []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign, Sum.elim_inr,
    SamplerMachineCoordinate.result, SamplerMachineTraceBit.result, coordinateControl]
  simp only [show (4 : Fin 6) ≠ 0 by decide, show (4 : Fin 6) ≠ 1 by decide,
    show (4 : Fin 6) ≠ 2 by decide, show (4 : Fin 6) ≠ 3 by decide,
    show (2 : Fin 6) ≠ 0 by decide, show (2 : Fin 6) ≠ 1 by decide,
    ↓reduceIte, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rfl
  · fin_cases k <;> rfl

theorem coordinate_cfg (l : Option SamplerMachineCoordinate.Label)
    (s : SamplerMachineCoordinate.Control) (a u c fuel x y index budget out : List Bool) :
    liftCfg (some .emit) (none : Option Bool) (foreign x y index budget out [])
      (SamplerMachineCoordinate.cfg l s a u c fuel []) =
      cfg (match l with | none => some (.inr .emit) | some l => some (.inl l))
        (s, none) a u c fuel x y index budget out [] := by cases l <;> rfl

def bitAt (n : ℕ) (x y : BinaryWord n) (i : ℕ) : Bool :=
  encodeBit (traceBit n (wordMul n x (wordPow n y i)))

theorem coordinate_call (n : ℕ) (x y : BinaryWord n) (index budget out : List Bool) :
    ∃ t ≤ SamplerMachineCoordinate.timeBound n index.length,
      run t (cfg (some (.inl (.inl (.inr .loop)))) initial
        (encodeWord x) (encodeWord y) (encodeWord (chosenWord n)) index
        (encodeWord x) (encodeWord y) index budget out []) =
      cfg (some (.inr .emit)) (coordinateControl (bitAt n x y index.length), none)
        [] [] (encodeWord (chosenWord n)) [] (encodeWord x) (encodeWord y) index budget out [] := by
  obtain ⟨t, ht, hr⟩ := SamplerMachineCoordinate.run_coordinate n x y index
  have hh : (SamplerMachineCoordinate.run t
      (SamplerMachineCoordinate.cfg (some (.inl (.inr .loop))) SamplerMachineCoordinate.initial
        (encodeWord x) (encodeWord y) (encodeWord (chosenWord n)) index [])).l = none := by
    rw [hr]; rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs SamplerMachineCoordinate.program
    program (some .emit) (fun _ => rfl) (none : Option Bool)
    (foreign (encodeWord x) (encodeWord y) index budget out [])
    (SamplerMachineCoordinate.cfg (some (.inl (.inr .loop))) SamplerMachineCoordinate.initial
      (encodeWord x) (encodeWord y) (encodeWord (chosenWord n)) index []) t hh
  dsimp only [SamplerMachineCoordinate.run] at hr
  rw [hr, coordinate_cfg, coordinate_cfg] at hrun
  exact ⟨t', ht'.trans ht, hrun⟩

theorem round_run (n : ℕ) (x y : BinaryWord n) (index budget out : List Bool) (b : Bool) :
    ∃ t ≤ SamplerMachineCoordinate.timeBound n index.length + 4 * n + 2 * index.length + 9,
      run t (cfg (some (.inr .loop)) initial [] [] (encodeWord (chosenWord n)) []
        (encodeWord x) (encodeWord y) index (b :: budget) out []) =
      cfg (some (.inr .loop)) initial [] [] (encodeWord (chosenWord n)) []
        (encodeWord x) (encodeWord y) (true :: index) budget (bitAt n x y index.length :: out) [] := by
  obtain ⟨tp, htp, hp⟩ := prepare_run (encodeWord x) (encodeWord y) index
    (encodeWord (chosenWord n)) budget out
  simp only [encodeWord_length] at htp
  obtain ⟨tc, htc, hc⟩ := coordinate_call n x y index budget out
  have hl := run_succ (step_loop_cons (encodeWord (chosenWord n)) (encodeWord x)
    (encodeWord y) index budget out b) 0
  have hs := run_succ (step_call (encodeWord x) (encodeWord y) (encodeWord (chosenWord n)) index
    (encodeWord x) (encodeWord y) index budget out) 0
  have he := run_succ (step_emit (bitAt n x y index.length) (encodeWord (chosenWord n))
    (encodeWord x) (encodeWord y) index budget out) 0
  simp only [run_zero, Nat.zero_add] at hl hs he
  refine ⟨1 + (tc + (1 + (tp + 1))), by omega, ?_⟩
  rw [run_add 1 (tc + (1 + (tp + 1))), run_add tc (1 + (tp + 1)),
    run_add 1 (tp + 1), run_add tp 1, hl, hp, hs, hc, he]

private theorem step_clear_cons (s : Control) (b : Bool) (c x y index out : List Bool) :
    TM2.step program (cfg (some (.inr .clear)) s [] [] c [] x y (b :: index) [] out []) =
      some (cfg (some (.inr .clear)) (s.1, some b) [] [] c [] x y index [] out []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign, Sum.elim_inr]
  simp only [show (2 : Fin 6) ≠ 0 by decide, show (2 : Fin 6) ≠ 1 by decide,
    ↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rfl
  · fin_cases k <;> rfl

private theorem step_clear_nil (s : Control) (c x y out : List Bool) :
    TM2.step program (cfg (some (.inr .clear)) s [] [] c [] x y [] [] out []) =
      some (cfg none initial [] [] c [] x y [] [] out []) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg, foreign, Sum.elim_inr]
  simp only [show (2 : Fin 6) ≠ 0 by decide, show (2 : Fin 6) ≠ 1 by decide,
    ↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k
  · rfl
  · fin_cases k <;> rfl

theorem clear_run (s : Control) (c x y index out : List Bool) :
    run (index.length + 1) (cfg (some (.inr .clear)) s [] [] c [] x y index [] out []) =
      cfg none initial [] [] c [] x y [] [] out [] := by
  induction index generalizing s with
  | nil => simpa using run_succ (step_clear_nil s c x y out) 0
  | cons b index ih =>
      rw [List.length_cons, run_succ (step_clear_cons s b c x y index out)]
      exact ih (s.1, some b)

def rowBits (n : ℕ) (x y : BinaryWord n) (start : ℕ) : ℕ → List Bool
  | 0 => []
  | L + 1 => bitAt n x y start :: rowBits n x y (start + 1) L

def roundBound (n R : ℕ) : ℕ := 32 * (R + 1) * (n + 1) ^ 3 + 4 * n + 2 * R + 9

/-- Literal coordinate loop, with the output in stack order. The arbitrary
old output suffix is preserved, so rows can be streamed into a whole table. -/
theorem run_row (n : ℕ) (x y : BinaryWord n) (index budget out : List Bool) (R : ℕ)
    (hR : index.length + budget.length ≤ R) :
    ∃ t ≤ budget.length * roundBound n R + R + 2,
      run t (cfg (some (.inr .loop)) initial [] [] (encodeWord (chosenWord n)) []
        (encodeWord x) (encodeWord y) index budget out []) =
      cfg none initial [] [] (encodeWord (chosenWord n)) [] (encodeWord x) (encodeWord y) [] []
        ((rowBits n x y index.length budget.length).reverse ++ out) [] := by
  induction budget generalizing index out with
  | nil =>
      refine ⟨index.length + 2, by simp only [List.length_nil, zero_mul] at *; omega, ?_⟩
      rw [show index.length + 2 = (index.length + 1) + 1 by omega,
        run_succ (step_loop_nil (encodeWord (chosenWord n)) (encodeWord x) (encodeWord y) index out),
        clear_run]
      rfl
  | cons b budget ih =>
      obtain ⟨ts, hts, hs⟩ := round_run n x y index budget out b
      obtain ⟨tr, htr, hr⟩ := ih (true :: index) (bitAt n x y index.length :: out) (by
        simp only [List.length_cons] at hR ⊢; omega)
      have hstep : ts ≤ roundBound n R := by
        have hc := SamplerMachineCoordinate.timeBound_polynomial n index.length
        have hi : index.length ≤ R := by simp only [List.length_cons] at hR; omega
        have hm : 32 * (index.length + 1) * (n + 1) ^ 3 ≤ 32 * (R + 1) * (n + 1) ^ 3 := by gcongr
        unfold roundBound
        omega
      refine ⟨tr + ts, ?_, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · rw [run_add tr ts, hs, hr]
        simp only [List.length_cons, rowBits, List.reverse_cons, List.append_assoc,
          List.singleton_append]

theorem rowBits_eq_ofFn (n : ℕ) (x y : BinaryWord n) (start L : ℕ) :
    rowBits n x y start L = List.ofFn (fun j : Fin L => bitAt n x y (start + j.val)) := by
  induction L generalizing start with
  | zero => simp [rowBits]
  | succ L ih =>
      rw [rowBits, ih, List.ofFn_succ]
      simp only [Nat.add_zero, Fin.val_succ]
      congr 2
      funext j
      congr 1
      omega

/-- A complete seed row in the exact executable coordinate order. -/
theorem run_executableRow (n L : ℕ) (x y : BinaryWord n) (out : List Bool) :
    ∃ t ≤ L * roundBound n L + L + 2,
      run t (cfg (some (.inr .loop)) initial [] [] (encodeWord (chosenWord n)) []
        (encodeWord x) (encodeWord y) [] (List.replicate L true) out []) =
      cfg none initial [] [] (encodeWord (chosenWord n)) [] (encodeWord x) (encodeWord y) [] []
        ((List.ofFn (fun j : Fin L => encodeBit (executableTraceBits n L (x, y) j))).reverse ++ out) [] := by
  obtain ⟨t, ht, hr⟩ := run_row n x y [] (List.replicate L true) out L (by simp)
  simp only [List.length_nil, List.length_replicate, rowBits_eq_ofFn, zero_add] at ht hr
  exact ⟨t, ht, hr⟩

end EthInapproximability.CurrentPaper.SamplerMachineRow
