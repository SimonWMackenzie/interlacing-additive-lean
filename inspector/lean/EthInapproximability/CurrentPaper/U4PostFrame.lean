import EthInapproximability.CurrentPaper.U4PostLocal
import EthInapproximability.CurrentPaper.BitMachineBankWrapper
import EthInapproximability.CurrentPaper.SignedMidpointApproxCanonical

/-!
# Unit 4 (Paper B), segment B4-S5 (part 1): width-changing framing primitives

Lane owner:b-unit4-shell-3 (private, 26 September 2026).

The post machine will be `composition Pre (composition Wrapper Drop)`:

* `Pre a` (new, one stack): prepends `a` literal `false` bits, i.e. `a` empty bank fields
  (`field [] = [false]`), turning the six-field H-B2 word into a `(a + 6)`-field word whose
  last six fields are H-B2's; `a + 1` transitions.
* the admitted `BitMachineBankWrapper` at width `W + 25` (`W = M.stackCount + 4`) around the
  embedded local program `U4PostLocal.Local.program` (part 2);
* `Drop c` (new, three stacks): deletes the last `c` bits (the trailing `c` empty fields),
  `2|x| + 2c + 3` transitions.

This module proves the two new machines and the exact field-encoding identities; the
wrapper instance and PostBody are part 2.
-/

namespace EthInapproximability.CurrentPaper.Unit4Post

open Turing Turing.TM2.Stmt BitMachineEncoding

namespace Pre

def program (a : ℕ) : Fin (a + 1) → TM2.Stmt (fun _ : Unit => Bool) (Fin (a + 1)) Unit :=
  fun i => if h : i.val < a then
      push () (fun _ => false) (goto (fun _ => ⟨i.val + 1, by omega⟩))
    else halt

abbrev Config (a : ℕ) := TM2.Cfg (fun _ : Unit => Bool) (Fin (a + 1)) Unit

theorem step_lt (a i : ℕ) (hi : i < a) (w : List Bool) :
    advance (program a) (⟨some ⟨i, by omega⟩, (), fun _ => List.replicate i false ++ w⟩ :
      Config a) =
    ⟨some ⟨i + 1, by omega⟩, (), fun _ => List.replicate (i + 1) false ++ w⟩ := by
  have hp : program a ⟨i, by omega⟩ =
      push () (fun _ => false) (goto (fun _ => ⟨i + 1, by omega⟩)) := by
    simp [program, hi]
  simp only [advance, TM2.step, hp, TM2.stepAux, Option.getD_some]
  congr 1

theorem step_end (a : ℕ) (S : Unit → List Bool) :
    advance (program a) (⟨some ⟨a, by omega⟩, (), S⟩ : Config a) = ⟨none, (), S⟩ := by
  have hp : program a ⟨a, by omega⟩ = halt := by simp [program]
  simp only [advance, TM2.step, hp, TM2.stepAux, Option.getD_some]

theorem steps (a : ℕ) (w : List Bool) :
    ∀ j i (h : i + j = a),
      ((advance (program a))^[j])
        (⟨some ⟨i, by omega⟩, (), fun _ => List.replicate i false ++ w⟩ : Config a) =
      ⟨some ⟨a, by omega⟩, (), fun _ => List.replicate a false ++ w⟩ := by
  intro j
  induction j with
  | zero => intro i h; subst h; rfl
  | succ j ih =>
      intro i h
      rw [Function.iterate_succ_apply, step_lt a i (by omega) w]
      exact ih (i + 1) (by omega)

noncomputable def machine (a : ℕ) : BitMachine.Machine :=
  ofFinite () () (0 : Fin (a + 1)) () (program a)

theorem outputs (a : ℕ) (w : List Bool) :
    (machine a).OutputsWithin w (List.replicate a false ++ w) (a + 1) := by
  have hi : rawInit () (0 : Fin (a + 1)) () w =
      (⟨some ⟨0, by omega⟩, (), fun _ => List.replicate 0 false ++ w⟩ : Config a) := by
    unfold rawInit
    congr 1
  have hr : ((advance (program a))^[a + 1]) (rawInit () (0 : Fin (a + 1)) () w) =
      ⟨none, (), fun _ => List.replicate a false ++ w⟩ := by
    rw [hi, Function.iterate_succ_apply', steps a w a 0 (by omega), step_end]
  apply outputsWithin_of_raw_run () () (0 : Fin (a + 1)) () (program a) w
    (List.replicate a false ++ w) (a + 1) (a + 1) le_rfl
  · rw [hr]
  · rw [hr]

end Pre

namespace Drop

abbrev Label (c : ℕ) := Bool ⊕ Fin (c + 1)
abbrev Config (c : ℕ) := TM2.Cfg (fun _ : Fin 3 => Bool) (Label c) (Option Bool)

/-- `inl false` scan (reverse the input onto stack 1), `inr i` drop counter, `inl true` emit
(reverse stack 1 onto the output stack 2). -/
def program (c : ℕ) : Label c → TM2.Stmt (fun _ : Fin 3 => Bool) (Label c) (Option Bool)
  | .inl false => pop 0 (fun _ b => b)
      (branch (fun v => v.isSome)
        (push 1 (fun v => v.getD false) (goto (fun _ => .inl false)))
        (goto (fun _ => .inr 0)))
  | .inr i => if h : i.val < c then
        pop 1 (fun v _ => v) (goto (fun _ => .inr ⟨i.val + 1, by omega⟩))
      else goto (fun _ => .inl true)
  | .inl true => pop 1 (fun _ b => b)
      (branch (fun v => v.isSome)
        (push 2 (fun v => v.getD false) (goto (fun _ => .inl true)))
        halt)

def cfg (c : ℕ) (l : Option (Label c)) (v : Option Bool) (a b d : List Bool) : Config c :=
  ⟨l, v, ![a, b, d]⟩

theorem scan_cons (c : ℕ) (v : Option Bool) (x : Bool) (w t : List Bool) :
    advance (program c) (cfg c (some (.inl false)) v (x :: w) t []) =
      cfg c (some (.inl false)) (some x) w (x :: t) [] := by
  apply congrArg (fun S => (⟨some (.inl false), some x, S⟩ : Config c))
  funext k
  fin_cases k <;> rfl

theorem scan_nil (c : ℕ) (v : Option Bool) (t : List Bool) :
    advance (program c) (cfg c (some (.inl false)) v [] t []) =
      cfg c (some (.inr 0)) none [] t [] := by
  apply congrArg (fun S => (⟨some (.inr 0), none, S⟩ : Config c))
  funext k
  fin_cases k <;> rfl

theorem scan_run (c : ℕ) (w : List Bool) :
    ∀ (t : List Bool) (v : Option Bool),
      ((advance (program c))^[w.length + 1]) (cfg c (some (.inl false)) v w t []) =
        cfg c (some (.inr 0)) none [] (w.reverse ++ t) [] := by
  induction w with
  | nil => intro t v; simpa using scan_nil c v t
  | cons x w ih =>
      intro t v
      rw [List.length_cons, Function.iterate_succ_apply, scan_cons, ih]
      simp

theorem drop_step (c i : ℕ) (hi : i < c) (v : Option Bool) (u : List Bool) :
    advance (program c) (cfg c (some (.inr ⟨i, by omega⟩)) v [] u []) =
      cfg c (some (.inr ⟨i + 1, by omega⟩)) v [] u.tail [] := by
  have hp : program c (.inr ⟨i, by omega⟩) =
      pop 1 (fun v _ => v) (goto (fun _ => .inr ⟨i + 1, by omega⟩)) := by
    simp [program, hi]
  simp only [advance, TM2.step, hp, TM2.stepAux, Option.getD_some, cfg]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem drop_end (c : ℕ) (v : Option Bool) (u : List Bool) :
    advance (program c) (cfg c (some (.inr ⟨c, by omega⟩)) v [] u []) =
      cfg c (some (.inl true)) v [] u [] := by
  have hp : program c (.inr ⟨c, by omega⟩) = goto (fun _ => .inl true) := by
    simp [program]
  simp only [advance, TM2.step, hp, TM2.stepAux, Option.getD_some, cfg]

theorem drop_steps (c : ℕ) (v : Option Bool) :
    ∀ j i (h : i + j = c) (u : List Bool),
      ((advance (program c))^[j]) (cfg c (some (.inr ⟨i, by omega⟩)) v [] u []) =
        cfg c (some (.inr ⟨c, by omega⟩)) v [] (u.drop j) [] := by
  intro j
  induction j with
  | zero => intro i h u; subst h; rfl
  | succ j ih =>
      intro i h u
      rw [Function.iterate_succ_apply, drop_step c i (by omega) v u, ih (i + 1) (by omega)]
      cases u <;> simp

theorem emit_cons (c : ℕ) (v : Option Bool) (x : Bool) (u o : List Bool) :
    advance (program c) (cfg c (some (.inl true)) v [] (x :: u) o) =
      cfg c (some (.inl true)) (some x) [] u (x :: o) := by
  apply congrArg (fun S => (⟨some (.inl true), some x, S⟩ : Config c))
  funext k
  fin_cases k <;> rfl

theorem emit_nil (c : ℕ) (v : Option Bool) (o : List Bool) :
    advance (program c) (cfg c (some (.inl true)) v [] [] o) = cfg c none none [] [] o := by
  apply congrArg (fun S => (⟨none, none, S⟩ : Config c))
  funext k
  fin_cases k <;> rfl

theorem emit_run (c : ℕ) (u : List Bool) :
    ∀ (o : List Bool) (v : Option Bool),
      ((advance (program c))^[u.length + 1]) (cfg c (some (.inl true)) v [] u o) =
        cfg c none none [] [] (u.reverse ++ o) := by
  induction u with
  | nil => intro o v; simpa using emit_nil c v o
  | cons x u ih =>
      intro o v
      rw [List.length_cons, Function.iterate_succ_apply, emit_cons, ih]
      simp

noncomputable def machine (c : ℕ) : BitMachine.Machine :=
  ofFinite (0 : Fin 3) (2 : Fin 3) (.inl false : Label c) (none : Option Bool) (program c)

/-- `Drop c` deletes exactly the last `c` bits of `x ++ replicate c false`. -/
theorem outputs (c : ℕ) (x : List Bool) :
    (machine c).OutputsWithin (x ++ List.replicate c false) x (2 * x.length + 2 * c + 3) := by
  have hi : rawInit (0 : Fin 3) (.inl false : Label c) (none : Option Bool)
      (x ++ List.replicate c false) =
      cfg c (some (.inl false)) none (x ++ List.replicate c false) [] [] := by
    unfold rawInit cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have h1 := scan_run c (x ++ List.replicate c false) [] none
  have h2 := drop_steps c none c 0 (by omega)
    ((x ++ List.replicate c false).reverse ++ [])
  have h3 := drop_end c none (List.drop c ((x ++ List.replicate c false).reverse ++ []))
  have hd : List.drop c ((x ++ List.replicate c false).reverse ++ []) = x.reverse := by
    simp [List.reverse_append, List.drop_left']
  rw [hd] at h3
  have h4 := emit_run c x.reverse [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at h4
  have hl : (x ++ List.replicate c false).length = x.length + c := by simp
  have hr : ((advance (program c))^[(x.length + 1) + (1 + (c +
      ((x ++ List.replicate c false).length + 1)))])
      (rawInit (0 : Fin 3) (.inl false : Label c) (none : Option Bool)
        (x ++ List.replicate c false)) = cfg c none none [] [] x := by
    rw [hi, Function.iterate_add_apply (advance (program c)) (x.length + 1),
      Function.iterate_add_apply (advance (program c)) 1,
      Function.iterate_add_apply (advance (program c)) c, h1]
    change ((advance (program c))^[x.length + 1])
      (advance (program c) (((advance (program c))^[c])
        (cfg c (some (.inr ⟨0, by omega⟩)) none [] _ []))) = _
    rw [h2, hd, h3, h4]
  apply outputsWithin_of_raw_run (0 : Fin 3) (2 : Fin 3) (.inl false : Label c)
    (none : Option Bool) (program c) (x ++ List.replicate c false) x
    ((x.length + 1) + (1 + (c + ((x ++ List.replicate c false).length + 1)))) _ (by omega)
  · rw [hr]; rfl
  · rw [hr]; rfl

end Drop

/-! ## Field-encoding identities -/

theorem encode_split (a b : ℕ) (B : Fin (a + b) → List Bool) :
    BitMachineBankCodec.encode B =
      BitMachineBankCodec.encode (fun i : Fin a => B (i.castLE (Nat.le_add_right a b))) ++
        BitMachineBankCodec.encode (fun j : Fin b => B (j.natAdd a)) := by
  rw [BitMachineBankCodec.encode_eq_list, BitMachineBankCodec.encode_eq_list,
    BitMachineBankCodec.encode_eq_list, List.ofFn_add, List.flatMap_append]

theorem encode_cast {N N' : ℕ} (h : N = N') (B : Fin N → List Bool) :
    BitMachineBankCodec.encode B =
      BitMachineBankCodec.encode (fun i : Fin N' => B (Fin.cast h.symm i)) := by
  subst h
  rfl

theorem encode_nil (a : ℕ) :
    BitMachineBankCodec.encode (fun _ : Fin a => ([] : List Bool)) = List.replicate a false := by
  rw [BitMachineBankCodec.encode_eq_list, List.ofFn_const]
  induction a with
  | zero => rfl
  | succ a ih =>
      rw [List.replicate_succ, List.flatMap_cons, ih]
      rfl

end EthInapproximability.CurrentPaper.Unit4Post
