import EthInapproximability.CurrentPaper.BitMachineTrimLeadingZeros
import EthInapproximability.CurrentPaper.EncodedCommunication

/-!
# Canonical little-endian binary word (private lane b-g34-owner-1)

A three-stack finite controller: reverse the LSB-first input word onto a work
stack (MSB on top), drop the leading zero bits there (the admitted
`BitMachineTrimLeadingZeros.trim`, MSB-first), and pop the rest onto the output
stack. The output is `(trim q.reverse).reverse`, the canonical word
`(bitsValue q).bits`. Every cell move is one charged transition.
-/

namespace BG34Canon

open Turing Turing.TM2.Stmt EthInapproximability.CurrentPaper BitMachineEncoding

inductive Label where
  | rev | trim | copy
  deriving DecidableEq, Fintype

abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Label Control

def cfg (l : Option Label) (v : Control) (input work out : List Bool) : Config :=
  ⟨l, v, ![input, work, out]⟩

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .rev => pop 0 (fun _ b => b)
      (branch (fun v => v.isSome)
        (push 1 (fun v => v.getD false) (goto (fun _ => .rev)))
        (goto (fun _ => .trim)))
  | .trim => pop 1 (fun _ b => b)
      (branch (fun v => v.getD false)
        (push 2 (fun _ => true) (goto (fun _ => .copy)))
        (branch (fun v => v.isSome) (goto (fun _ => .trim)) halt))
  | .copy => pop 1 (fun _ b => b)
      (branch (fun v => v.isSome)
        (push 2 (fun v => v.getD false) (goto (fun _ => .copy))) halt)

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def canon (q : List Bool) : List Bool := (BitMachineTrimLeadingZeros.trim q.reverse).reverse

theorem rev_run (q work out : List Bool) (v : Control) :
    run (q.length + 1) (cfg (some .rev) v q work out) =
      cfg (some .trim) none [] (q.reverse ++ work) out := by
  induction q generalizing work v with
  | nil =>
      simp [run, advance, program, cfg, TM2.step, TM2.stepAux]
  | cons b q ih =>
      have hs : advance program (cfg (some .rev) v (b :: q) work out) =
          cfg (some .rev) (some b) q (b :: work) out := by
        simp [advance, program, cfg, TM2.step, TM2.stepAux]
        funext k
        fin_cases k <;> rfl
      simp only [List.length_cons, run, Function.iterate_succ_apply, hs]
      simpa only [run, List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (b :: work) (some b)

theorem copy_run (r input out : List Bool) (v : Control) :
    run (r.length + 1) (cfg (some .copy) v input r out) =
      cfg none none input [] (r.reverse ++ out) := by
  induction r generalizing v out with
  | nil =>
      simp [run, advance, program, cfg, TM2.step, TM2.stepAux]
  | cons b r ih =>
      have hs : advance program (cfg (some .copy) v input (b :: r) out) =
          cfg (some .copy) (some b) input r (b :: out) := by
        simp [advance, program, cfg, TM2.step, TM2.stepAux]
        funext k
        fin_cases k <;> rfl
      simp only [List.length_cons, run, Function.iterate_succ_apply, hs]
      simpa only [run, List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (b :: out) (some b)

def trimTime : List Bool → ℕ
  | [] => 1
  | false :: w => trimTime w + 1
  | true :: w => w.length + 2

theorem trimTime_le (w : List Bool) : trimTime w ≤ w.length + 1 := by
  induction w with
  | nil => simp [trimTime]
  | cons b w ih => cases b <;> simp [trimTime] <;> omega

theorem trim_run (w input out : List Bool) (v : Control) :
    run (trimTime w) (cfg (some .trim) v input w out) =
      cfg none none input [] ((BitMachineTrimLeadingZeros.trim w).reverse ++ out) := by
  induction w generalizing v with
  | nil =>
      simp [run, advance, program, cfg, TM2.step, TM2.stepAux, trimTime,
        BitMachineTrimLeadingZeros.trim]
  | cons b w ih =>
      cases b with
      | false =>
          have hs : advance program (cfg (some .trim) v input (false :: w) out) =
              cfg (some .trim) (some false) input w out := by
            simp [advance, program, cfg, TM2.step, TM2.stepAux]
            funext k
            fin_cases k <;> rfl
          simp only [trimTime, run, Function.iterate_succ_apply, hs]
          simpa only [run, BitMachineTrimLeadingZeros.trim] using ih (some false)
      | true =>
          have hs : advance program (cfg (some .trim) v input (true :: w) out) =
              cfg (some .copy) (some true) input w (true :: out) := by
            simp [advance, program, cfg, TM2.step, TM2.stepAux]
            funext k
            fin_cases k <;> rfl
          have hc := copy_run w input (true :: out) (some true)
          have hstep : run (trimTime (true :: w)) (cfg (some .trim) v input (true :: w) out) =
              run (w.length + 1) (advance program (cfg (some .trim) v input (true :: w) out)) := by
            simp only [run, trimTime]
            rw [show w.length + 2 = (w.length + 1) + 1 from rfl, Function.iterate_succ_apply]
          rw [hstep, hs, hc]
          simp [BitMachineTrimLeadingZeros.trim]

theorem canon_run (q : List Bool) :
    run (q.length + 1 + trimTime q.reverse) (cfg (some .rev) none q [] []) =
      cfg none none [] [] (canon q) := by
  rw [run, Nat.add_comm, Function.iterate_add_apply]
  have h1 := rev_run q [] [] none
  simp only [run, List.append_nil] at h1
  rw [h1]
  have h2 := trim_run q.reverse [] [] none
  simp only [run, List.append_nil] at h2
  rw [h2]
  rfl

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Fin 3) 2 Label.rev (none : Control) program

theorem outputs (q : List Bool) :
    machine.OutputsWithin q (canon q) (2 * q.length + 2) := by
  have ht : q.length + 1 + trimTime q.reverse ≤ 2 * q.length + 2 := by
    have := trimTime_le q.reverse
    rw [List.length_reverse] at this
    omega
  apply outputsWithin_of_raw_run (0 : Fin 3) 2 Label.rev (none : Control) program
    q (canon q) _ (2 * q.length + 2) ht
  all_goals
    have hi : rawInit (0 : Fin 3) Label.rev (none : Control) q = cfg (some .rev) none q [] [] := by
      unfold rawInit cfg
      congr 1
      funext k
      fin_cases k <;> simp
    rw [hi]
    have hr := canon_run q
    simp only [run] at hr
    rw [hr]
  · rfl
  · rfl

/-- A little-endian word with no trailing zero is the binary expansion of its value. -/
theorem bits_bitsValue_of_canonical (l : List Bool)
    (h : l = [] ∨ ∃ bs, l = bs ++ [true]) :
    (EncodedCommunication.bitsValue l).bits = l := by
  induction l with
  | nil => simp [EncodedCommunication.bitsValue]
  | cons b l ih =>
      rcases h with h | ⟨bs, hbs⟩
      · cases h
      · cases l with
        | nil =>
            have hb : b = true := by
              cases bs with
              | nil => simpa using hbs.symm
              | cons c cs => simp at hbs
            subst hb
            decide
        | cons c l =>
            have hl : c :: l = [] ∨ ∃ bs, c :: l = bs ++ [true] := by
              right
              cases bs with
              | nil => simp at hbs
              | cons d ds =>
                  refine ⟨ds, ?_⟩
                  have h' := hbs
                  simp only [List.cons_append, List.cons.injEq] at h'
                  exact h'.2
            have ih' := ih hl
            simp only [EncodedCommunication.bitsValue] at ih' ⊢
            rw [Nat.bits_append_bit _ _ (fun hz => by
              rw [hz] at ih'
              simp at ih')]
            rw [ih']

theorem canon_canonical (q : List Bool) :
    ∃ m : ℕ, canon q = m.bits := by
  refine ⟨EncodedCommunication.bitsValue (canon q), ?_⟩
  symm
  apply bits_bitsValue_of_canonical
  rcases BitMachineTrimLeadingZeros.trim_canonical q.reverse with h | ⟨bs, h⟩
  · left; simp [canon, h]
  · right; exact ⟨bs.reverse, by simp [canon, h]⟩

theorem bits_shape (k : ℕ) : k.bits = [] ∨ ∃ bs, k.bits = bs ++ [true] := by
  induction k using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
      right
      rw [Nat.bits_append_bit n b h]
      rcases ih with hn | ⟨bs, hbs⟩
      · have hn0 : n = 0 := by
          have := congrArg EncodedCommunication.bitsValue hn
          simpa [EncodedCommunication.bitsValue] using this
        have hb := h hn0
        subst hb
        exact ⟨[], by simp [hn]⟩
      · exact ⟨b :: bs, by simp [hbs]⟩

theorem canon_bits (k : ℕ) : canon k.bits = k.bits := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · have hne : k.bits ≠ [] := by
      intro h
      have := congrArg EncodedCommunication.bitsValue h
      simp [EncodedCommunication.bitsValue] at this
      omega
    obtain ⟨bs, hbs⟩ : ∃ bs, k.bits = bs ++ [true] := by
      rcases bits_shape k with h | h
      · exact (hne h).elim
      · exact h
    rw [canon, hbs]
    simp [BitMachineTrimLeadingZeros.trim]

end BG34Canon

#print axioms BG34Canon.outputs
#print axioms BG34Canon.canon_canonical
#print axioms BG34Canon.canon_bits
