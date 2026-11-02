import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

/-!
One physical reversal pass on two distinct Boolean stacks. Every input bit is
popped and pushed in one TM2 transition. This is used when changing between
the Code D little-endian numerator and the division machine's MSB dividend.
-/
namespace CurrentAdditive.RawRatReverseTransfer

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

variable {K : Type*} [DecidableEq K]

inductive Label where
  | move
  deriving DecidableEq, Fintype

def program (source target : K) : Label →
    TM2.Stmt (fun _ : K => Bool) Label (Option Bool)
  | .move => pop source (fun _ b => b)
      (branch Option.isSome
        (push target (fun b => b.getD false) (goto (fun _ => .move)))
        halt)

def cfg (l : Option Label) (v : Option Bool) (S : K → List Bool) :
    TM2.Cfg (fun _ : K => Bool) Label (Option Bool) := ⟨l, v, S⟩

def run (source target : K) (t : Nat)
    (c : TM2.Cfg (fun _ : K => Bool) Label (Option Bool)) :=
  ((advance (program source target))^[t]) c

theorem step_cons (source target : K) (hne : source ≠ target)
    (S : K → List Bool) (b : Bool) (bs : List Bool) (v : Option Bool)
    (hsrc : S source = b :: bs) :
    advance (program source target) (cfg (some .move) v S) =
      cfg (some .move) (some b)
        (Function.update (Function.update S source bs)
          target (b :: S target)) := by
  simp [advance, TM2.step, program, cfg, TM2.stepAux, hsrc,
    Function.update_of_ne (Ne.symm hne)]

theorem step_nil (source target : K) (S : K → List Bool) (v : Option Bool)
    (hsrc : S source = []) :
    advance (program source target) (cfg (some .move) v S) =
      cfg none none S := by
  simp [advance, TM2.step, program, cfg, TM2.stepAux, hsrc]

theorem run_correct (source target : K) (hne : source ≠ target)
    (S : K → List Bool) (v : Option Bool) :
    run source target ((S source).length + 1) (cfg (some .move) v S) =
      cfg none none
        (Function.update (Function.update S source []) target
          ((S source).reverse ++ S target)) := by
  generalize hs : S source = bits
  induction bits generalizing S v with
  | nil =>
      simp only [hs, List.length_nil, Nat.zero_add, List.reverse_nil,
        List.nil_append, run, Function.iterate_one]
      rw [step_nil source target S v hs]
      congr 1
      funext k
      by_cases hk : k = source <;> by_cases ht : k = target <;>
        simp_all [Function.update_apply]
  | cons b bs ih =>
      rw [show (b :: bs).length + 1 = (bs.length + 1) + 1 by simp]
      unfold run
      rw [Function.iterate_succ_apply]
      rw [step_cons source target hne S b bs v hs]
      have hnext :
          (Function.update (Function.update S source bs) target (b :: S target)) source = bs := by
        simp [hne]
      have hi := ih (Function.update (Function.update S source bs) target (b :: S target))
        (some b) hnext
      rw [show ((advance (program source target))^[bs.length + 1])
          (cfg (some .move) (some b)
            (Function.update (Function.update S source bs) target (b :: S target))) =
          cfg none none
            (Function.update
              (Function.update (Function.update (Function.update S source bs)
                target (b :: S target)) source []) target
              (bs.reverse ++ (Function.update (Function.update S source bs)
                target (b :: S target)) target)) from hi]
      congr 1
      funext k
      by_cases hk1 : k = source
      · subst k; simp [hne]
      · by_cases hk2 : k = target
        · subst k; simp [hne, List.reverse_cons, List.append_assoc]
        · simp [hk1, hk2]

end CurrentAdditive.RawRatReverseTransfer
