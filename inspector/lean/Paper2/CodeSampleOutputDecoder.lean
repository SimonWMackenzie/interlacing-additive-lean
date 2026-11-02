import Paper2.CodeTableFallback
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineInline
import Mathlib.Tactic

/-! A physical, source-preserving orientation of the successful sampled-label
word, plus its exact columns-first product/tuple codec layout. -/

namespace Paper2.CodeSampleOutputDecoder

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineInline
open Paper2.RecursiveLabelCodecScratch

noncomputable section

theorem columns_first_layout {X Y : Type} (col : PrefixCodec Y)
    (row : PrefixCodec X) (mY mX : Nat)
    (ys : Fin mY → Y) (xs : Fin mX → X) :
    (prodCodec (piCodec col mY) (piCodec row mX)).encode (ys,xs) =
      (piCodec col mY).encode ys ++ (piCodec row mX).encode xs := rfl

def tupleWord {A : Type} (ca : PrefixCodec A) :
    (n : Nat) → (Fin n → A) → List Bool
  | 0, _ => []
  | n+1, f => ca.encode (f 0) ++ tupleWord ca n (Fin.tail f)

theorem piCodec_encode_tupleWord {A : Type} (ca : PrefixCodec A)
    (n : Nat) (f : Fin n → A) :
    (piCodec ca n).encode f = tupleWord ca n f := by
  induction n with
  | zero =>
      simp [piCodec,tupleWord,emptyPiCodec]
  | succ n ih =>
      simp [tupleWord, piCodec, transportCodec, prodCodec, ih]

inductive Label where
  | copy (l : BitMachineCopy.Label) | reverse
  deriving DecidableEq, Fintype

abbrev Stack := Fin 3
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copy l => BitMachineInline.stmt Label.copy id id
      (some .reverse) (BitMachineCopy.program l)
  | .reverse => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun b => b.getD false) (goto (fun _ => .reverse))) halt)

def cfg (l : Option Label) (v : Control)
    (reversed work forward : List Bool) : Config :=
  ⟨l,v,BitMachineCopy.stackContents reversed work forward⟩

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_add (a b : Nat) (c : Config) :
    run (a+b) c = run b (run a c) := by
  unfold run
  rw [Nat.add_comm a b,Function.iterate_add_apply]

private theorem reverse_cons (v : Control) (source : List Bool)
    (b : Bool) (bits forward : List Bool) :
    run 1 (cfg (some .reverse) v source (b::bits) forward) =
      cfg (some .reverse) (some b) source bits (b::forward) := by
  simp [run,cfg,program,advance,TM2.step,TM2.stepAux,
    BitMachineCopy.stackContents]
  funext k
  fin_cases k <;> rfl

private theorem reverse_nil (v : Control) (source forward : List Bool) :
    run 1 (cfg (some .reverse) v source [] forward) =
      cfg none none source [] forward := by
  simp [run,cfg,program,advance,TM2.step,TM2.stepAux,
    BitMachineCopy.stackContents]

theorem reverse_run (v : Control) (source bits forward : List Bool) :
    run (bits.length+1) (cfg (some .reverse) v source bits forward) =
      cfg none none source [] (bits.reverse ++ forward) := by
  induction bits generalizing v forward with
  | nil => simpa using reverse_nil v source forward
  | cons b bits ih =>
      rw [List.length_cons,show (bits.length+1)+1 = 1+(bits.length+1) by omega,
        run_add,reverse_cons,ih]
      simp [List.reverse_cons,List.append_assoc]

theorem orient_run (reversed : List Bool) :
    ∃ t ≤ 3*reversed.length+3,
      run t (cfg (some (.copy .scan)) none reversed [] []) =
        cfg none none reversed [] reversed.reverse := by
  have hcopy := BitMachineCopy.run_correct none reversed []
  have hh : ((BitMachineCopy.run (2*reversed.length+2)
      (BitMachineCopy.cfg (some .scan) none reversed [] [])).l) = none := by
    rw [hcopy]; rfl
  obtain ⟨t,ht,hr⟩ := BitMachineInline.outputs Label.copy id id
    (by intro v; rfl) (some .reverse) BitMachineCopy.program
    program (by intro l; rfl)
    (BitMachineCopy.cfg (some .scan) none reversed [] [])
    (2*reversed.length+2) hh
  unfold BitMachineCopy.run at hcopy
  rw [hcopy] at hr
  simp only [List.append_nil] at hr
  change run t (cfg (some (.copy .scan)) none reversed [] []) =
    cfg (some .reverse) none reversed reversed [] at hr
  have hrev := reverse_run none reversed reversed []
  refine ⟨t+(reversed.length+1),by omega,?_⟩
  rw [run_add,hr,hrev,List.append_nil]

#print axioms columns_first_layout
#print axioms piCodec_encode_tupleWord
#print axioms orient_run

end
end Paper2.CodeSampleOutputDecoder
