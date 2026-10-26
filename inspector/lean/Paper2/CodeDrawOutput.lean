import Paper2.GeneratorExecution
import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

namespace Paper2.CodeDrawOutput

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.RecursiveLabelCodecScratch

inductive Label where
  | ticket | bitStart | bitDrain
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Fin 2 => Bool) Label (Option Bool)

def bank (input output : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then input else output

def cfg (l : Option Label) (v : Option Bool) (input output : List Bool) : Config :=
  ⟨l,v,bank input output⟩

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label (Option Bool)
  | .ticket => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun v => v.getD false) (goto (fun _ => .ticket)))
        (load (fun _ => none) halt))
  | .bitStart => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun v => v.getD false) (goto (fun _ => .bitDrain)))
        (load (fun _ => none) halt))
  | .bitDrain => pop 0 (fun _ b => b)
      (branch Option.isSome (goto (fun _ => .bitDrain))
        (load (fun _ => none) halt))

theorem ticket_cons (b : Bool) (bs out : List Bool) (v : Option Bool) :
    advance program (cfg (some .ticket) v (b::bs) out) =
      cfg (some .ticket) (some b) bs (b::out) := by
  change (⟨some .ticket, some b,
    Function.update (Function.update (bank (b::bs) out) 0 bs) 1 (b::out)⟩ : Config) = _
  congr 1
  funext k
  fin_cases k <;> rfl

theorem ticket_nil (out : List Bool) (v : Option Bool) :
    advance program (cfg (some .ticket) v [] out) = cfg none none [] out := by
  change (⟨none, none, Function.update (bank [] out) 0 []⟩ : Config) = _
  congr 1
  funext k
  fin_cases k <;> rfl

theorem ticket_word (input out : List Bool) (v : Option Bool) :
    ((advance program)^[input.length+1]) (cfg (some .ticket) v input out) =
      cfg none none [] (input.reverse ++ out) := by
  induction input generalizing out v with
  | nil => simpa using ticket_nil out v
  | cons b bs ih =>
      rw [show (b::bs).length+1 = (bs.length+1)+1 by simp,
        Function.iterate_add_apply, Function.iterate_one, ticket_cons, ih]
      simp [List.reverse_cons, List.append_assoc]

theorem bit_drain (input out : List Bool) (v : Option Bool) :
    ((advance program)^[input.length+1]) (cfg (some .bitDrain) v input out) =
      cfg none none [] out := by
  induction input generalizing v with
  | nil =>
      change (⟨none, none, Function.update (bank [] out) 0 []⟩ : Config) = _
      congr 1
      funext k
      fin_cases k <;> rfl
  | cons b bs ih =>
      have hs : advance program (cfg (some .bitDrain) v (b::bs) out) =
          cfg (some .bitDrain) (some b) bs out := by
        change (⟨some .bitDrain, some b,
          Function.update (bank (b::bs) out) 0 bs⟩ : Config) = _
        congr 1
        funext k
        fin_cases k <;> rfl
      rw [show (b::bs).length+1 = (bs.length+1)+1 by simp,
        Function.iterate_add_apply, Function.iterate_one, hs, ih]

theorem bit_word (b : Bool) (tail out : List Bool) (v : Option Bool) :
    ((advance program)^[tail.length+2]) (cfg (some .bitStart) v (b::tail) out) =
      cfg none none [] (b::out) := by
  have hs : advance program (cfg (some .bitStart) v (b::tail) out) =
      cfg (some .bitDrain) (some b) tail (b::out) := by
    change (⟨some .bitDrain, some b,
      Function.update (Function.update (bank (b::tail) out) 0 tail) 1 (b::out)⟩ : Config) = _
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [show tail.length+2 = (tail.length+1)+1 by omega,
    Function.iterate_add_apply, Function.iterate_one, hs, bit_drain]

theorem ticket_codec {D : Nat} (i : Fin D) (out : List Bool) :
    ((advance program)^[i.val+2])
      (cfg (some .ticket) none ((finCodec D).encode i) out) =
      cfg none none [] (((finCodec D).encode i).reverse ++ out) := by
  simpa [finCodec] using ticket_word ((finCodec D).encode i) out none

theorem bit_codec (i : Fin 2) (out : List Bool) :
    ((advance program)^[i.val+2])
      (cfg (some .bitStart) none ((finCodec 2).encode i) out) =
      cfg none none [] (decide (i.val=1)::out) := by
  fin_cases i
  · simpa [finCodec] using bit_word false [] out none
  · simpa [finCodec] using bit_word true [false] out none

/-- Exact byte identity with the source's accepted-ticket state transition.
Only the two output banks are handled here; code/tape framing comes later. -/
theorem source_ticket (n : Nat) (cs : List GeneratorCode.Code)
    (out : List Bool) (i : Fin (n+1)) :
    ((advance program)^[i.val+2])
      (cfg (some .ticket) none ((finCodec (n+1)).encode i) out.reverse) =
      cfg none none []
        (GeneratorCode.advance ⟨.ticket (n+1)::cs,out⟩ i.val).output.reverse := by
  simpa [GeneratorCode.advance, finCodec, List.reverse_append] using
    ticket_codec i out.reverse

theorem source_bit (cs : List GeneratorCode.Code) (out : List Bool) (i : Fin 2) :
    ((advance program)^[i.val+2])
      (cfg (some .bitStart) none ((finCodec 2).encode i) out.reverse) =
      cfg none none []
        (GeneratorCode.advance ⟨.bit::cs,out⟩ i.val).output.reverse := by
  simpa [GeneratorCode.advance, List.reverse_append] using bit_codec i out.reverse

theorem ticket_clock_le {D : Nat} (i : Fin D) : i.val+2 ≤ D+1 := by
  omega

theorem bit_clock_le (i : Fin 2) : i.val+2 ≤ 3 := by
  omega

#print axioms ticket_word
#print axioms source_ticket
#print axioms source_bit

end Paper2.CodeDrawOutput
