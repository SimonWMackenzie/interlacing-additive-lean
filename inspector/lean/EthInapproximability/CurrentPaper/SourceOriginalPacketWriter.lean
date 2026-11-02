import EthInapproximability.CurrentPaper.SourceOriginalBranchPackets
import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# One physical original-size-bearing branch packet

This fixed five-stack program retains the unary original count, consumes one
branch word, and writes their exact two-field bank packet. It is an inner
subroutine of the source-list packetizer, not a substitute for that loop.
-/

namespace EthInapproximability.CurrentPaper.SourceOriginalPacketWriter

open Turing Turing.TM2.Stmt BitMachineEncoding EncodedCommunication

inductive Label where
  | scanN | restoreN | scanWord | reverse
  deriving DecidableEq, Fintype

abbrev Stack := Fin 5
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .scanN => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 2 (fun v => v.getD false)
          (push 3 (fun _ => true)
            (push 3 (fun v => v.getD false) (goto (fun _ => .scanN)))))
        (push 3 (fun _ => false) (goto (fun _ => .restoreN))))
  | .restoreN => pop 2 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun v => v.getD false) (goto (fun _ => .restoreN)))
        (goto (fun _ => .scanWord)))
  | .scanWord => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 3 (fun _ => true)
          (push 3 (fun v => v.getD false) (goto (fun _ => .scanWord))))
        (push 3 (fun _ => false) (goto (fun _ => .reverse))))
  | .reverse => pop 3 (fun _ b => b)
      (branch Option.isSome
        (push 4 (fun v => v.getD false) (goto (fun _ => .reverse)))
        (load (fun _ => none) halt))

def cfg (l : Option Label) (v : Control)
    (n word scratch reversed output : List Bool) : Config :=
  ⟨l, v, ![n, word, scratch, reversed, output]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_succ (t : ℕ) (c : Config) :
    run (t+1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

private theorem run_add (t u : ℕ) (c : Config) :
    run (t+u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance program) u t c

private theorem scanN_cons (v : Control) (b : Bool)
    (n word scratch reversed output : List Bool) :
    advance program (cfg (some .scanN) v (b::n) word scratch reversed output) =
      cfg (some .scanN) (some b) n word (b::scratch)
        (b::true::reversed) output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext i
  fin_cases i <;> rfl

private theorem scanN_nil (v : Control)
    (word scratch reversed output : List Bool) :
    advance program (cfg (some .scanN) v [] word scratch reversed output) =
      cfg (some .restoreN) none [] word scratch (false::reversed) output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext i
  fin_cases i <;> rfl

private theorem restoreN_cons (v : Control) (b : Bool)
    (n word scratch reversed output : List Bool) :
    advance program (cfg (some .restoreN) v n word (b::scratch) reversed output) =
      cfg (some .restoreN) (some b) (b::n) word scratch reversed output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext i
  fin_cases i <;> rfl

private theorem restoreN_nil (v : Control)
    (n word reversed output : List Bool) :
    advance program (cfg (some .restoreN) v n word [] reversed output) =
      cfg (some .scanWord) none n word [] reversed output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

private theorem scanWord_cons (v : Control) (b : Bool)
    (n word reversed output : List Bool) :
    advance program (cfg (some .scanWord) v n (b::word) [] reversed output) =
      cfg (some .scanWord) (some b) n word [] (b::true::reversed) output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext i
  fin_cases i <;> rfl

private theorem scanWord_nil (v : Control)
    (n reversed output : List Bool) :
    advance program (cfg (some .scanWord) v n [] [] reversed output) =
      cfg (some .reverse) none n [] [] (false::reversed) output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext i
  fin_cases i <;> rfl

private theorem reverse_cons (v : Control) (b : Bool)
    (n reversed output : List Bool) :
    advance program (cfg (some .reverse) v n [] [] (b::reversed) output) =
      cfg (some .reverse) (some b) n [] [] reversed (b::output) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext i
  fin_cases i <;> rfl

private theorem reverse_nil (v : Control) (n output : List Bool) :
    advance program (cfg (some .reverse) v n [] [] [] output) =
      cfg none none n [] [] [] output := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem scanN_run (n word scratch reversed output : List Bool) (v : Control) :
    run (n.length+1) (cfg (some .scanN) v n word scratch reversed output) =
      cfg (some .restoreN) none [] word (n.reverse++scratch)
        ((field n).reverse++reversed) output := by
  induction n generalizing v scratch reversed with
  | nil =>
      change run 1 (cfg (some .scanN) v [] word scratch reversed output) = _
      rw [run_succ, scanN_nil]
      rfl
  | cons b n ih =>
      rw [List.length_cons, run_succ, scanN_cons]
      simpa [field, List.reverse_cons, List.append_assoc] using
        ih (b::scratch) (b::true::reversed) (some b)

theorem restoreN_run (scratch n word reversed output : List Bool) (v : Control) :
    run (scratch.length+1) (cfg (some .restoreN) v n word scratch reversed output) =
      cfg (some .scanWord) none (scratch.reverse++n) word [] reversed output := by
  induction scratch generalizing v n with
  | nil =>
      change run 1 (cfg (some .restoreN) v n word [] reversed output) = _
      rw [run_succ, restoreN_nil]
      rfl
  | cons b scratch ih =>
      rw [List.length_cons, run_succ, restoreN_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (b::n) (some b)

theorem scanWord_run (n word reversed output : List Bool) (v : Control) :
    run (word.length+1) (cfg (some .scanWord) v n word [] reversed output) =
      cfg (some .reverse) none n [] [] ((field word).reverse++reversed) output := by
  induction word generalizing v reversed with
  | nil =>
      change run 1 (cfg (some .scanWord) v n [] [] reversed output) = _
      rw [run_succ, scanWord_nil]
      rfl
  | cons b word ih =>
      rw [List.length_cons, run_succ, scanWord_cons]
      simpa [field, List.reverse_cons, List.append_assoc] using
        ih (b::true::reversed) (some b)

theorem reverse_run (n reversed output : List Bool) (v : Control) :
    run (reversed.length+1) (cfg (some .reverse) v n [] [] reversed output) =
      cfg none none n [] [] [] (reversed.reverse++output) := by
  induction reversed generalizing v output with
  | nil =>
      change run 1 (cfg (some .reverse) v n [] [] [] output) = _
      rw [run_succ, reverse_nil]
      rfl
  | cons b reversed ih =>
      rw [List.length_cons, run_succ, reverse_cons]
      simpa [List.reverse_cons, List.append_assoc] using ih (b::output) (some b)

theorem packet_run (n word : List Bool) :
    run (2*n.length+word.length+
      (BitMachineBankCodec.encode ![n,word]).length+4)
      (cfg (some .scanN) none n word [] [] []) =
      cfg none none n [] [] []
        (BitMachineBankCodec.encode ![n,word]) := by
  have h₁ := scanN_run n word [] [] [] none
  have h₂ := restoreN_run n.reverse [] word (field n).reverse [] none
  have h₃ := scanWord_run n word (field n).reverse [] none
  simp only [List.append_nil] at h₁
  have h₂' : run (n.length+1)
      (cfg (some .restoreN) none [] word n.reverse (field n).reverse []) =
      cfg (some .scanWord) none n word [] (field n).reverse [] := by
    simpa using h₂
  have hpacket : BitMachineBankCodec.encode ![n,word] = field n ++ field word := by
    simp [BitMachineBankCodec.encode, BitMachineBankCodec.encodeFrom]
  have hlen : ((field word).reverse ++ (field n).reverse).length =
      (BitMachineBankCodec.encode ![n,word]).length := by
    rw [hpacket]
    simp [List.length_append]
    omega
  have h₄ := reverse_run n ((field word).reverse ++ (field n).reverse) [] none
  have hfirst :
      run (2*n.length+word.length+3)
        (cfg (some .scanN) none n word [] [] []) =
        cfg (some .reverse) none n [] []
          ((field word).reverse ++ (field n).reverse) [] := by
    calc
      run (2*n.length+word.length+3)
          (cfg (some .scanN) none n word [] [] []) =
        run (word.length+1) (run (n.length+1) (run (n.length+1)
          (cfg (some .scanN) none n word [] [] []))) := by
            rw [← run_add, ← run_add]
            congr 1
            omega
      _ = _ := by
        rw [h₁, h₂', h₃]
  calc
    run (2*n.length+word.length+
        (BitMachineBankCodec.encode ![n,word]).length+4)
        (cfg (some .scanN) none n word [] [] []) =
      run ((BitMachineBankCodec.encode ![n,word]).length+1)
        (run (2*n.length+word.length+3)
          (cfg (some .scanN) none n word [] [] [])) := by
            rw [← run_add]
            congr 1
            omega
    _ = cfg none none n [] [] []
          (BitMachineBankCodec.encode ![n,word]) := by
        rw [hfirst, ← hlen, h₄]
        simpa [List.reverse_append, hpacket]

/-- The exact cost of producing one canonical original-size-bearing packet.
It depends on this branch word and the original unary `n`, not on the number
of branches in the source list. -/
theorem unary_packet_run (n : ℕ) (word : List Bool) :
    run (4*n+3*word.length+6)
      (cfg (some .scanN) none (List.replicate n true) word [] [] []) =
      cfg none none (List.replicate n true) [] [] []
        (SourceOriginalBranchPackets.packet n word) := by
  have h := packet_run (List.replicate n true) word
  have he : BitMachineBankCodec.encode ![List.replicate n true,word] =
      SourceOriginalBranchPackets.packet n word := rfl
  rw [he] at h
  have hl := SourceOriginalBranchPackets.packet_length n word
  simp only [List.length_replicate, he, hl] at h
  convert h using 1 <;> congr 1 <;> omega

/-- Embedding the writer leaves every ambient bank outside the five chosen
locations untouched. This is the interface needed by the outer list loop
and by an upstream machine with nonempty private stacks. -/
theorem embedded_unary_packet_run {K : Type*} [DecidableEq K]
    (ι : Stack ↪ K) (foreign : K → List Bool)
    (n : ℕ) (word : List Bool) :
    ∃ t ≤ 4*n+3*word.length+6,
      ((advance (fun l => BitMachineStackEmbedding.stmt ι id id id none (program l)))^[t])
        (BitMachineStackEmbedding.cfg ι foreign id id none
          (cfg (some .scanN) none (List.replicate n true) word [] [] [])) =
        BitMachineStackEmbedding.cfg ι foreign id id none
          (cfg none none (List.replicate n true) [] [] []
            (SourceOriginalBranchPackets.packet n word)) := by
  let c := cfg (some .scanN) none (List.replicate n true) word [] [] []
  let T := 4*n+3*word.length+6
  have hraw : ((advance program)^[T]) c =
      cfg none none (List.replicate n true) [] [] []
        (SourceOriginalBranchPackets.packet n word) :=
    unary_packet_run n word
  have hhalt : (((advance program)^[T]) c).l = none := by rw [hraw]; rfl
  obtain ⟨t, ht, hr⟩ := BitMachineStackEmbedding.outputs ι foreign id id id
    (fun _ => rfl) none program
    (fun l => BitMachineStackEmbedding.stmt ι id id id none (program l))
    (fun _ => rfl) c T hhalt
  refine ⟨t, ht, ?_⟩
  simpa only [c, T, hraw] using hr

end EthInapproximability.CurrentPaper.SourceOriginalPacketWriter
