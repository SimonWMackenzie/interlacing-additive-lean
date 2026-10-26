import Paper2.A4Loops
import EthInapproximability.CurrentPaper.EncodedComplexity

/-!
# WP-NP (lane `owner:a-np-1`, private, 26 September 2026): extra generic stack loops

Fixed finite statements over an arbitrary stack type `K`, label type `Λ` and control
`Option Bool × W`, in the style of the admitted `Paper2.Unit4Shell.Loops`, with exact
iterated-step lemmas. The admitted `parseStmt` is re-analysed on EVERY word (not only on
`field x ++ t`), through the total semantic function `parseAll`.

* `parse_any`: `parseStmt` on an arbitrary word `xs` ends with payload `(parseAll xs).1`
  (reversed) and remaining suffix `(parseAll xs).2`, within `|xs| + 1` steps.
* `popBranchStmt`: pop one cell and branch on emptiness (one step).
* `moveCountStmt a b u`: move `a` onto `b` (reversing) and push one `true` onto `u` per bit.
* `cutStmt u m o`: while `u` and `m` are nonempty, pop one cell of `u` and move one bit of
  `m` onto `o`: leaves `take B t` (reversed) on `o` and `drop B t` on `m`.

**No ledger row is closed.**
-/

namespace NPOwner1

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell.Loops

/-- The literal behaviour of `parseStmt` on every word. -/
def parseAll : List Bool → List Bool × List Bool
  | [] => ([], [])
  | false :: r => ([], r)
  | [true] => ([false], [])
  | true :: b :: r => (b :: (parseAll r).1, (parseAll r).2)

theorem parseAll_field (x t : List Bool) :
    parseAll (EncodedCommunication.field x ++ t) = (x, t) := by
  induction x with
  | nil => simp [EncodedCommunication.field, parseAll]
  | cons b x ih => simp [EncodedCommunication.field, parseAll, ih]

theorem parseAll_pair (x t : List Bool) :
    parseAll (EncodedComplexity.pair x t) = (x, t) :=
  parseAll_field x t

theorem parseAll_length : ∀ xs : List Bool,
    (parseAll xs).1.length ≤ xs.length ∧ (parseAll xs).2.length ≤ xs.length
  | [] => by simp [parseAll]
  | false :: r => by simp [parseAll]
  | [true] => by simp [parseAll]
  | true :: b :: r => by
      have := parseAll_length r
      simp only [parseAll, List.length_cons]
      omega

variable {K Λ W : Type*} [DecidableEq K]

def popBranchStmt (a : K) (yes no : Λ) : TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W) :=
  .pop a setBit (.branch (fun v => v.1.isSome) (.goto fun _ => yes) (.goto fun _ => no))

def moveCountStmt (a b u : K) (here next : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W) :=
  .pop a setBit (.branch (fun v => v.1.isSome)
    (.push b (fun v => v.1.getD false) (.push u (fun _ => true) (.goto fun _ => here)))
    (.goto fun _ => next))

def cutStmt (u m o : K) (here next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W) :=
  .pop u setBit (.branch (fun v => v.1.isSome)
    (.pop m setBit (.branch (fun v => v.1.isSome)
      (.push o (fun v => v.1.getD false) (.goto fun _ => here))
      (.goto fun _ => next)))
    (.goto fun _ => next))

variable (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W))

theorem parse_any (a b : K) (here next : Λ) (hab : a ≠ b)
    (hP : P here = parseStmt a b here next) :
    ∀ (xs : List Bool) (S : K → List Bool) (o : Option Bool) (w : W), S a = xs →
      ∃ n o', n ≤ xs.length + 1 ∧ (advance P)^[n] ⟨some here, (o, w), S⟩ =
        ⟨some next, (o', w),
          Function.update (Function.update S b ((parseAll xs).1.reverse ++ S b)) a
            (parseAll xs).2⟩
  | [], S, o, w, hS => ⟨1, none, by simp, by
      simp [advance, TM2.step, TM2.stepAux, hP, parseStmt, setBit, hS, parseAll]⟩
  | false :: r, S, o, w, hS => ⟨1, some false, by simp, by
      simp [advance, TM2.step, TM2.stepAux, hP, parseStmt, setBit, hS, parseAll]⟩
  | [true], S, o, w, hS => ⟨2, none, by simp, by
      have h1 : advance P ⟨some here, (o, w), S⟩ =
          ⟨some here, (none, w), Function.update (Function.update S a []) b (false :: S b)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, hP, parseStmt, setBit, hS,
          Function.update_of_ne hab.symm]
      have h2 : advance P ⟨some here, (none, w),
          Function.update (Function.update S a []) b (false :: S b)⟩ =
          ⟨some next, (none, w), Function.update (Function.update S a []) b (false :: S b)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, hP, parseStmt, setBit,
          Function.update_of_ne hab]
      rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply, h1,
        Function.iterate_one, h2]
      simp only [parseAll, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append]
      rw [Function.update_comm hab.symm]⟩
  | true :: x :: r, S, o, w, hS => by
      have h1 : advance P ⟨some here, (o, w), S⟩ =
          ⟨some here, (some x, w), Function.update (Function.update S a r) b (x :: S b)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, hP, parseStmt, setBit, hS,
          Function.update_of_ne hab.symm]
      obtain ⟨n, o', hn, he⟩ := parse_any a b here next hab hP r
        (Function.update (Function.update S a r) b (x :: S b)) (some x) w
        (by rw [Function.update_of_ne hab, Function.update_self])
      refine ⟨n + 1, o', by simp only [List.length_cons]; omega, ?_⟩
      rw [Function.iterate_succ_apply, h1, he]
      simp only [parseAll, List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [Function.update_self, Function.update_idem, Function.update_comm hab,
        Function.update_idem]

theorem popBranch_cons (a : K) (here yes no : Λ) (hP : P here = popBranchStmt a yes no)
    (x : Bool) (r : List Bool) (S : K → List Bool) (o : Option Bool) (w : W)
    (hS : S a = x :: r) :
    advance P ⟨some here, (o, w), S⟩ = ⟨some yes, (some x, w), Function.update S a r⟩ := by
  simp [advance, TM2.step, TM2.stepAux, hP, popBranchStmt, setBit, hS]

theorem popBranch_nil (a : K) (here yes no : Λ) (hP : P here = popBranchStmt a yes no)
    (S : K → List Bool) (o : Option Bool) (w : W) (hS : S a = []) :
    advance P ⟨some here, (o, w), S⟩ = ⟨some no, (none, w), S⟩ := by
  simp [advance, TM2.step, TM2.stepAux, hP, popBranchStmt, setBit, hS]

theorem moveCount_loop (a b u : K) (here next : Λ) (hab : a ≠ b) (hau : a ≠ u) (hbu : b ≠ u)
    (hP : P here = moveCountStmt a b u here next) :
    ∀ (xs : List Bool) (S : K → List Bool) (o : Option Bool) (w : W), S a = xs →
      (advance P)^[xs.length + 1] ⟨some here, (o, w), S⟩ =
        ⟨some next, (none, w),
          Function.update (Function.update (Function.update S b (xs.reverse ++ S b)) u
            (List.replicate xs.length true ++ S u)) a []⟩ := by
  intro xs
  induction xs with
  | nil =>
      intro S o w hS
      simp only [List.length_nil, zero_add, Function.iterate_one, List.reverse_nil,
        List.nil_append, List.replicate_zero, Function.update_eq_self]
      simp [advance, TM2.step, TM2.stepAux, hP, moveCountStmt, setBit, hS]
  | cons x xs ih =>
      intro S o w hS
      have h1 : advance P ⟨some here, (o, w), S⟩ =
          ⟨some here, (some x, w),
            Function.update (Function.update (Function.update S a xs) b (x :: S b)) u
              (true :: S u)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, hP, moveCountStmt, setBit, hS,
          Function.update_of_ne hab.symm, Function.update_of_ne hau.symm,
          Function.update_of_ne hbu.symm]
      rw [List.length_cons, Function.iterate_succ_apply, h1,
        ih _ _ _ (by rw [Function.update_of_ne hau, Function.update_of_ne hab,
          Function.update_self])]
      congr 1
      funext k
      simp only [Function.update_apply]
      by_cases hka : k = a
      · subst hka; simp
      · by_cases hkb : k = b
        · subst hkb; simp [hka, hbu, List.reverse_cons]
        · by_cases hku : k = u
          · subst hku; simp [hka, List.replicate_succ']
          · simp [hka, hkb, hku]

theorem cut_loop (u m o : K) (here next : Λ) (hum : u ≠ m) (huo : u ≠ o) (hmo : m ≠ o)
    (hP : P here = cutStmt u m o here next) :
    ∀ (B : ℕ) (t : List Bool) (S : K → List Bool) (ov : Option Bool) (w : W),
      S u = List.replicate B true → S m = t →
      ∃ n ov' U', n ≤ B + 1 ∧ (advance P)^[n] ⟨some here, (ov, w), S⟩ =
        ⟨some next, (ov', w),
          Function.update (Function.update (Function.update S o ((t.take B).reverse ++ S o)) m
            (t.drop B)) u U'⟩ := by
  intro B
  induction B with
  | zero =>
      intro t S ov w hu hm
      refine ⟨1, none, [], by omega, ?_⟩
      simp only [List.replicate_zero] at hu
      simp only [List.take_zero, List.reverse_nil, List.nil_append, List.drop_zero,
        Function.update_eq_self, Function.iterate_one]
      rw [← hm, Function.update_eq_self, ← hu, Function.update_eq_self]
      simp [advance, TM2.step, TM2.stepAux, hP, cutStmt, setBit, hu]
  | succ B ih =>
      intro t S ov w hu hm
      cases t with
      | nil =>
          refine ⟨1, none, List.replicate B true, by omega, ?_⟩
          simp only [List.take_nil, List.reverse_nil, List.nil_append, List.drop_nil,
            Function.update_eq_self, Function.iterate_one]
          rw [← hm, Function.update_eq_self]
          simp [advance, TM2.step, TM2.stepAux, hP, cutStmt, setBit, hu, List.replicate_succ,
            Function.update_of_ne hum.symm, hm]
      | cons x t =>
          have h1 : advance P ⟨some here, (ov, w), S⟩ =
              ⟨some here, (some x, w),
                Function.update (Function.update (Function.update S u (List.replicate B true))
                  m t) o (x :: S o)⟩ := by
            simp [advance, TM2.step, TM2.stepAux, hP, cutStmt, setBit, hu, List.replicate_succ,
              Function.update_of_ne hum.symm, hm, Function.update_of_ne huo.symm,
              Function.update_of_ne hmo.symm]
          obtain ⟨n, ov', U', hn, he⟩ := ih t
            (Function.update (Function.update (Function.update S u (List.replicate B true))
              m t) o (x :: S o)) (some x) w
            (by rw [Function.update_of_ne huo, Function.update_of_ne hum, Function.update_self])
            (by rw [Function.update_of_ne hmo, Function.update_self])
          refine ⟨n + 1, ov', U', by omega, ?_⟩
          rw [Function.iterate_succ_apply, h1, he]
          congr 1
          funext k
          simp only [Function.update_apply]
          by_cases hku : k = u
          · subst hku; simp
          · by_cases hkm : k = m
            · subst hkm; simp [hku]
            · by_cases hko : k = o
              · subst hko; simp [hku, hkm, List.take_succ_cons, List.reverse_cons]
              · simp [hku, hkm, hko]

end NPOwner1
