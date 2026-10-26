import EthInapproximability.CurrentPaper.CNFValidatorCorrectness
import EthInapproximability.CurrentPaper.CNFValidatorBounded
import EthInapproximability.CurrentPaper.EncodedGraphMachineRuntime

/-!
# Total all-input CNF validation with a polynomial clock (unit 4, B4-S1)

Source: frozen v8 `06-eth.tex:238-242` and the `EncodedCNF` convention.
This module composes the checked field, sign, storage and clause runs of the
literal `CNFValidator` controller. Every bound counts transitions of that
controller; the final theorem is stated for every bitstring. The
machine-independent length lemmas `EncodedGraphMachineTotal.readNat_length`,
`EncodedGraphMachineRuntime.vertex_lengths` and
`EncodedGraphMachine.readUnary_failure` are reused by exact name.
-/

namespace EthInapproximability.CurrentPaper.CNFValidator.Runtime

open Turing BitMachineEncoding EthInapproximability.CurrentPaper.CNFValidator
open EthInapproximability.CurrentPaper.CNFValidator.Steps
open EthInapproximability.CurrentPaper.CNFValidator.Correctness

theorem field_run (f : Field) (v : Control) (hf : field v = f)
    (d : Data) (n L : Nat)
    (hinput : d.input.length ≤ L) (hn : n ≤ L) (hcap : d.cap.length ≤ L) :
    ∃ t ≤ 22 * (L + 1)^2, ∃ c,
      run t (cfg (some (.inl .scan)) ((none, none), v.2)
        {entryData v d n with value := []}) = c ∧
      match EncodedCommunication.readNat d.input with
      | none => RejectFrame d c
      | some (k, rest) => if Fits v d n k then
          ∃ w : Control, field w = field (storeControl f v) ∧
            c = cfg (some (storeNext f)) w
              (Steps.storeData f k
                (Correctness.storeData {d with input := rest} n k))
        else RejectFrame d c := by
  obtain ⟨t, ht, c, he, hp⟩ := field_to_store v d n L hinput hn hcap
  cases hr : EncodedCommunication.readNat d.input with
  | none => exact ⟨t, by omega, c, he, by simpa [hr] using hp⟩
  | some p =>
    obtain ⟨k, rest⟩ := p
    by_cases hok : Fits v d n k
    · simp only [hr, hok, ↓reduceIte] at hp
      obtain ⟨w, hw, hc⟩ := hp
      rw [hc] at he
      have hwf : field w = f := hw.trans hf
      have hs := store_run f (List.replicate k true) w hwf
        (Correctness.storeData {d with input := rest} n k)
      simp only [List.length_replicate] at hs
      have hk : k ≤ L := by
        by_cases hfc : field v = .count
        · have hh : k ≤ d.cap.length := by simpa [Fits, hfc] using hok
          exact hh.trans hcap
        · have hh : k < n := by simpa [Fits, hfc] using hok
          omega
      refine ⟨t + (k + 1), by nlinarith [Nat.zero_le (L^2)], _,
        (run_add he _).trans hs, ?_⟩
      simp only [hr, hok, ↓reduceIte]
      refine ⟨storeControl f w, ?_, rfl⟩
      cases f <;> simpa [storeControl, field, setPop, setField] using hw
    · exact ⟨t, by omega, c, he, by simpa [hr, hok] using hp⟩

/-- The clause-loop data: remaining input, saved input, unary variable
count, unary remaining-clause counter; every other stack empty. -/
def clauseData (bits original : List Bool) (n count : Nat) : Data :=
  {input := bits, original := original, vertices := List.replicate n true,
    clauses := List.replicate count true}

def IsLit (f : Field) : Prop := f = .lit0 ∨ f = .lit1 ∨ f = .lit2

/-- One literal: sign bit, canonical index field, strict bound `index < n`,
unary conversion and discard. -/
theorem literal_run (f : Field) (hlit : IsLit f) (v : Control) (hf : field v = f)
    (bits original : List Bool) (n count L : Nat)
    (hinput : bits.length ≤ L) (hn : n ≤ L) :
    ∃ t ≤ 23 * (L + 1)^2, ∃ c,
      run t (cfg (some (outer .sign)) v (clauseData bits original n count)) = c ∧
      match Bounded.readCheckedLiteral n bits with
      | none => RejectFrame (clauseData bits original n count) c
      | some (_, rest) => ∃ w : Control, field w = field (storeControl f v) ∧
          c = cfg (some (storeNext f)) w (clauseData rest original n count) := by
  have hnc : f ≠ .count := by rcases hlit with h | h | h <;> subst h <;> decide
  cases bits with
  | nil =>
      have hs := sign_nil v (clauseData [] original n count)
      refine ⟨1, by nlinarith [Nat.zero_le (L^2)], _, run_succ hs 0, ?_⟩
      exact ⟨rfl, rfl, rfl⟩
  | cons s tail =>
      have hs := sign_cons s tail v (clauseData tail original n count)
      have hs' : advance program
          (cfg (some (outer .sign)) v (clauseData (s :: tail) original n count)) =
          cfg (some (.inl .scan)) ((none, none), (setPop v (some s)).2)
            (clauseData tail original n count) := by
        simpa [clauseData] using hs
      have hfv : field (setPop v (some s)) = f := by simpa [field, setPop] using hf
      have hlen : tail.length ≤ L := by simp at hinput; omega
      obtain ⟨t, ht, c, he, hp⟩ := field_run f (setPop v (some s)) hfv
        (clauseData tail original n count) n L hlen hn (by simp [clauseData])
      have hi : {entryData (setPop v (some s)) (clauseData tail original n count) n with
          value := []} = clauseData tail original n count := by
        simp [entryData, clauseData]
      rw [hi] at he
      have he' := (run_succ hs' t).trans he
      rw [show (clauseData tail original n count).input = tail from rfl] at hp
      refine ⟨t + 1, by nlinarith [Nat.zero_le (L^2)], c, he', ?_⟩
      · have hfc : field (setPop v (some s)) ≠ .count := by rw [hfv]; exact hnc
        cases hr : EncodedCommunication.readNat tail with
        | none =>
            simp only [hr] at hp
            simpa [Bounded.readCheckedLiteral, hr, RejectFrame, clauseData] using hp
        | some p =>
            obtain ⟨k, rest⟩ := p
            by_cases hk : k < n
            · simp only [hr, Fits, hfc, ↓reduceIte, hk] at hp
              obtain ⟨w, hw, hc⟩ := hp
              simp only [Bounded.readCheckedLiteral, hr, Bind.bind, Option.bind, hk,
                ↓reduceIte]
              refine ⟨w, ?_, ?_⟩
              · rw [hw]; cases f <;> simp [storeControl, field, setPop, setField]
              · rw [hc]
                rcases hlit with h | h | h <;> subst h <;>
                  simp [Steps.storeData, Correctness.storeData, clauseData]
            · simp only [hr, Fits, hfc, ↓reduceIte, hk] at hp
              simpa [Bounded.readCheckedLiteral, hr, hk, RejectFrame, clauseData] using hp

theorem clause_loop (v : Control) (bits original : List Bool) (n count L : Nat)
    (hinput : bits.length ≤ L) (hn : n ≤ L) :
    ∃ t ≤ (count + 1) * (80 * (L + 1)^2), ∃ c,
      run t (cfg (some (outer .clauses)) v (clauseData bits original n count)) = c ∧
      match Bounded.readCheckedClauses n count bits with
      | none => RejectFrame (clauseData bits original n count) c
      | some (_, rest) => ∃ w : Control,
          c = cfg (some (outer .finalCheck)) w (clauseData rest original n 0) := by
  induction count generalizing v bits with
  | zero =>
      refine ⟨1, by nlinarith [Nat.zero_le (L^2)],
        cfg (some (outer .finalCheck)) (setPop v none) (clauseData bits original n 0), ?_, ?_⟩
      · simpa [clauseData] using run_succ (clauses_nil v (clauseData bits original n 0)) 0
      · exact ⟨setPop v none, rfl⟩
  | succ count ih =>
      let v0 : Control := setField (setPop v (some true)) .lit0
      have hs : advance program
          (cfg (some (outer .clauses)) v (clauseData bits original n (count + 1))) =
          cfg (some (outer .sign)) v0 (clauseData bits original n count) := by
        simpa [clauseData, List.replicate_succ] using
          clauses_cons true (List.replicate count true) v (clauseData bits original n count)
      obtain ⟨t₁, ht₁, c₁, he₁, hp₁⟩ := literal_run .lit0 (Or.inl rfl) v0 rfl
        bits original n count L hinput hn
      have he₁' := (run_succ hs t₁).trans he₁
      cases h₁ : Bounded.readCheckedLiteral n bits with
      | none =>
          simp only [h₁] at hp₁
          refine ⟨t₁ + 1, ?_, c₁, he₁', ?_⟩
          · nlinarith [Nat.zero_le (L^2), Nat.zero_le (count * (80 * (L + 1)^2))]
          · simpa [Bounded.readCheckedClauses, h₁, RejectFrame, clauseData] using hp₁
      | some p₁ =>
        obtain ⟨a, t1⟩ := p₁
        simp only [h₁] at hp₁
        obtain ⟨w₁, hw₁, hc₁⟩ := hp₁
        rw [hc₁] at he₁'
        have hl₁ := Bounded.readCheckedLiteral_length h₁
        obtain ⟨t₂, ht₂, c₂, he₂, hp₂⟩ := literal_run .lit1 (Or.inr (Or.inl rfl)) w₁
          (by simpa [storeControl, field, setField, v0] using hw₁)
          t1 original n count L (by omega) hn
        have he₂' := (run_add he₁' t₂).trans he₂
        cases h₂ : Bounded.readCheckedLiteral n t1 with
        | none =>
            simp only [h₂] at hp₂
            refine ⟨t₁ + 1 + t₂, ?_, c₂, he₂', ?_⟩
            · nlinarith [Nat.zero_le (L^2), Nat.zero_le (count * (80 * (L + 1)^2))]
            · simpa [Bounded.readCheckedClauses, h₁, h₂, RejectFrame, clauseData] using hp₂
        | some p₂ =>
          obtain ⟨b, t2⟩ := p₂
          simp only [h₂] at hp₂
          obtain ⟨w₂, hw₂, hc₂⟩ := hp₂
          rw [hc₂] at he₂'
          have hl₂ := Bounded.readCheckedLiteral_length h₂
          obtain ⟨t₃, ht₃, c₃, he₃, hp₃⟩ := literal_run .lit2 (Or.inr (Or.inr rfl)) w₂
            (by simpa [storeControl, field, setField] using hw₂)
            t2 original n count L (by omega) hn
          have he₃' := (run_add he₂' t₃).trans he₃
          cases h₃ : Bounded.readCheckedLiteral n t2 with
          | none =>
              simp only [h₃] at hp₃
              refine ⟨t₁ + 1 + t₂ + t₃, ?_, c₃, he₃', ?_⟩
              · nlinarith [Nat.zero_le (L^2), Nat.zero_le (count * (80 * (L + 1)^2))]
              · simpa [Bounded.readCheckedClauses, h₁, h₂, h₃, RejectFrame, clauseData]
                  using hp₃
          | some p₃ =>
            obtain ⟨c, t3⟩ := p₃
            simp only [h₃] at hp₃
            obtain ⟨w₃, _, hc₃⟩ := hp₃
            rw [hc₃] at he₃'
            have hl₃ := Bounded.readCheckedLiteral_length h₃
            obtain ⟨ti, hti, ci, hei, hpi⟩ := ih w₃ t3 (by omega)
            refine ⟨t₁ + 1 + t₂ + t₃ + ti, ?_, ci, (run_add he₃' ti).trans hei, ?_⟩
            · nlinarith [Nat.zero_le (L^2)]
            · cases hr : Bounded.readCheckedClauses n count t3 with
              | none =>
                  simp only [hr] at hpi
                  simpa [Bounded.readCheckedClauses, h₁, h₂, h₃, hr, RejectFrame,
                    clauseData] using hpi
              | some p =>
                  simp only [hr] at hpi
                  simpa [Bounded.readCheckedClauses, h₁, h₂, h₃, hr] using hpi

def HaltsWith (c : Config) (output : List Bool) : Prop :=
  c.l = none ∧ c.stk 13 = output

theorem reject_halts (c : Config) (h : c.l = some (outer .reject)) :
    HaltsWith (run 1 c) (false :: c.stk 13) := by
  rcases c with ⟨l, v, bank⟩
  change l = some (outer .reject) at h
  subst l
  simp [HaltsWith, run, advance, TM2.step, program, outer, outerProgram, TM2.stepAux]

theorem reject_frame_halts {d : Data} {c : Config} (h : RejectFrame d c) :
    HaltsWith (run 1 c) (false :: d.output) := by
  simpa only [h.2.2] using reject_halts c h.1

theorem final_check (v : Control) (rest original : List Bool) (n : Nat) :
    ∃ t ≤ original.length + 2, ∃ c,
      run t (cfg (some (outer .finalCheck)) v (clauseData rest original n 0)) = c ∧
      HaltsWith c (if rest = [] then true :: original.reverse else [false]) := by
  cases rest with
  | nil =>
      have hs := run_succ (finalCheck_nil v (clauseData [] original n 0)) 0
      have ha := accept_run original (setPop v none) (clauseData [] original n 0)
      have he := (run_add hs (original.length + 1)).trans ha
      refine ⟨1 + (original.length + 1), by omega, _, he, ?_⟩
      simp [HaltsWith, cfg, Data.stacks, clauseData, run]
  | cons b rest =>
      have hs := run_succ (finalCheck_cons b rest v (clauseData [] original n 0)) 0
      have ha := run_succ (reject_step (setPop v (some b)) (clauseData rest original n 0)) 0
      have he := (run_add hs 1).trans ha
      refine ⟨2, by omega, _, he, ?_⟩
      simp [HaltsWith, cfg, Data.stacks, clauseData, run]

def countData (bits original : List Bool) (n L : Nat) : Data :=
  {input := bits, original := original, cap := List.replicate L true,
    vertices := List.replicate n true}

theorem count_run (v : Control) (hf : field v = .count)
    (bits original : List Bool) (n L : Nat)
    (hinput : bits.length ≤ L) (hn : n ≤ L) :
    ∃ t ≤ 22 * (L + 1)^2, ∃ c,
      run t (cfg (some (.inl .scan)) ((none, none), v.2)
        (countData bits original n L)) = c ∧
      match EncodedCommunication.readNat bits with
      | none => RejectFrame (countData bits original n L) c
      | some (k, rest) => if k ≤ L then
          ∃ w : Control, c = cfg (some (outer .clauses)) w (clauseData rest original n k)
        else RejectFrame (countData bits original n L) c := by
  obtain ⟨t, ht, c, he, hp⟩ := field_run .count v hf (countData bits original n L) n L
    hinput hn (by simp [countData])
  have hi : {entryData v (countData bits original n L) n with value := []} =
      countData bits original n L := by simp [entryData, countData, hf]
  rw [hi] at he
  refine ⟨t, ht, c, he, ?_⟩
  cases hr : EncodedCommunication.readNat bits with
  | none => simpa [hr, countData] using hp
  | some p =>
      obtain ⟨k, rest⟩ := p
      by_cases hk : k ≤ L
      · simp only [countData, hr, Fits, hf, ↓reduceIte, List.length_replicate, hk] at hp
        obtain ⟨w, _, hw⟩ := hp
        simp only [hk, ↓reduceIte]
        refine ⟨w, ?_⟩
        simpa [storeNext, Steps.storeData, Correctness.storeData, clauseData,
          countData] using hw
      · simpa [hr, countData, Fits, hf, hk] using hp

def readTail (n L : Nat) (bits : List Bool) : Option (List EncodedCNF.Clause) := do
  let (count, tail) ← EncodedCommunication.readNat bits
  if count ≤ L then do
    let (clauses, rest) ← Bounded.readCheckedClauses n count tail
    if rest = [] then some clauses else none
  else none

def tailResult (n L : Nat) (bits original : List Bool) : List Bool :=
  if (readTail n L bits).isSome then true :: original.reverse else [false]

theorem tail_run (v : Control) (hf : field v = .count)
    (bits original : List Bool) (n L : Nat)
    (hinput : bits.length ≤ L) (hn : n ≤ L) :
    ∃ t ≤ 120 * (L + 1)^3 + original.length + 4, ∃ c,
      run t (cfg (some (.inl .scan)) ((none, none), v.2)
        (countData bits original n L)) = c ∧
      HaltsWith c (tailResult n L bits original) := by
  obtain ⟨t, ht, c, he, hp⟩ := count_run v hf bits original n L hinput hn
  have hsquare : (L + 1)^2 ≤ (L + 1)^3 := by nlinarith [Nat.zero_le (L^2)]
  cases hr : EncodedCommunication.readNat bits with
  | none =>
      simp only [hr] at hp
      refine ⟨t + 1, by nlinarith, _, run_add he 1, ?_⟩
      simpa [tailResult, readTail, hr, countData] using reject_frame_halts hp
  | some p =>
      obtain ⟨count, tail⟩ := p
      by_cases hcount : count ≤ L
      · simp only [hr, hcount, ↓reduceIte] at hp
        obtain ⟨w, hw⟩ := hp
        rw [hw] at he
        obtain ⟨u, hu, out, hout, hpost⟩ := clause_loop w tail original n count L
          ((EncodedGraphMachineTotal.readNat_length hr).trans hinput) hn
        have he' := (run_add he u).trans hout
        have hloop : (count + 1) * (80 * (L + 1)^2) ≤ 80 * (L + 1)^3 := by
          have hm := Nat.mul_le_mul_right (80 * (L + 1)^2) (Nat.add_le_add_right hcount 1)
          nlinarith
        cases hcl : Bounded.readCheckedClauses n count tail with
        | none =>
            simp only [hcl] at hpost
            refine ⟨t + u + 1, by nlinarith, _, run_add he' 1, ?_⟩
            simpa [tailResult, readTail, hr, hcount, hcl, clauseData] using
              reject_frame_halts hpost
        | some pair =>
            obtain ⟨clauses, rest⟩ := pair
            simp only [hcl] at hpost
            obtain ⟨z, hz⟩ := hpost
            rw [hz] at he'
            obtain ⟨f, hftime, final, hfinal, hhalt⟩ := final_check z rest original n
            refine ⟨t + u + f, by nlinarith, final, (run_add he' f).trans hfinal, ?_⟩
            by_cases hrest : rest = [] <;>
              simpa [tailResult, readTail, hr, hcount, hcl, hrest] using hhalt
      · simp only [hr, hcount, ↓reduceIte] at hp
        refine ⟨t + 1, by nlinarith, _, run_add he 1, ?_⟩
        simpa [tailResult, readTail, hr, hcount, countData] using reject_frame_halts hp

def initialData (input : List Bool) : Data :=
  {input := input, original := input.reverse, cap := List.replicate input.length true}

theorem vertex_run (input : List Bool) :
    ∃ t ≤ input.length + 1, ∃ c,
      run t (cfg (some (outer .vertices)) initialControl (initialData input)) = c ∧
      match EncodedGraph.readUnary input with
      | none => RejectFrame (initialData input) c
      | some (n, rest) => c = cfg (some (.inl .scan)) (headerControl initialControl)
          (countData rest input.reverse n input.length) := by
  cases hr : EncodedGraph.readUnary input with
  | none =>
      have hi := EncodedGraphMachine.readUnary_failure input hr
      have he := vertices_unterminated input.length initialControl (initialData input)
      have hstart : {initialData input with input := List.replicate input.length true} =
          initialData input := by rw [← hi]; rfl
      rw [hstart] at he
      refine ⟨input.length + 1, le_rfl, _, he, ?_⟩
      exact ⟨rfl, rfl, rfl⟩
  | some p =>
      obtain ⟨n, rest⟩ := p
      have hi := EncodedGraph.readUnary_sound hr
      have hl := EncodedGraphMachineRuntime.vertex_lengths hr
      have he := vertices_run n rest initialControl (initialData input)
      have hstart : {initialData input with input := EncodedGraph.unary n ++ rest} =
          initialData input := by rw [hi]; rfl
      rw [hstart] at he
      refine ⟨n + 1, by omega, _, he, ?_⟩
      simp [initialData, countData]

theorem tailResult_eq_result {input rest : List Bool} {n : Nat}
    (h : EncodedGraph.readUnary input = some (n, rest)) :
    tailResult n input.length rest input.reverse = result input := by
  have hd := Bounded.decode_eq input
  simp only [result]
  rw [← hd]
  unfold Bounded.decode
  rw [h]
  simp only [Bind.bind, Option.bind]
  unfold tailResult readTail
  simp only [List.reverse_reverse]
  cases hn : EncodedCommunication.readNat rest with
  | none => simp [hn]
  | some p =>
      obtain ⟨count, tail⟩ := p
      simp only [Bind.bind, Option.bind, hn]
      split
      · cases he : Bounded.readCheckedClauses n count tail with
        | none => rfl
        | some p =>
            obtain ⟨clauses, suffix⟩ := p
            simp only [Bind.bind, Option.bind]
            split <;> rfl
      · rfl

theorem raw_outputs (input : List Bool) :
    ∃ t ≤ 250 * (input.length + 1)^3, ∃ c,
      run t (rawInit 0 (outer .save) initialControl input) = c ∧
      HaltsWith c (result input) := by
  have hstart := startup input
  obtain ⟨t, ht, c, he, hp⟩ := vertex_run input
  have he' := (run_add hstart t).trans he
  have hsquare : input.length ≤ (input.length + 1)^3 := by
    nlinarith [Nat.zero_le (input.length^2)]
  have hcube : 0 < (input.length + 1)^3 := by positivity
  cases hr : EncodedGraph.readUnary input with
  | none =>
      simp only [hr] at hp
      refine ⟨(2 * input.length + 2) + t + 1, by nlinarith, _, run_add he' 1, ?_⟩
      have hbad : EncodedCNF.decode input = none := by simp [EncodedCNF.decode, hr]
      simpa [initialData, result, hbad] using reject_frame_halts hp
  | some p =>
      obtain ⟨n, rest⟩ := p
      simp only [hr] at hp
      rw [hp] at he'
      have hl := EncodedGraphMachineRuntime.vertex_lengths hr
      obtain ⟨u, hu, out, hout, hhalt⟩ := tail_run (headerControl initialControl) rfl
        rest input.reverse n input.length (by omega) (by omega)
      have hic : ((none, none), (headerControl initialControl).2) =
          headerControl initialControl := rfl
      rw [hic] at hout
      refine ⟨(2 * input.length + 2) + t + u, ?_, out, (run_add he' u).trans hout, ?_⟩
      · simp only [List.length_reverse] at hu
        nlinarith
      · simpa only [tailResult_eq_result hr] using hhalt

/-- **B4-S1.** The fixed finite CNF validator, on EVERY bitstring, halts
within `250 (|input|+1)^3` transitions with output `true :: input` when
`EncodedCNF.decode input` succeeds and `[false]` otherwise. -/
theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input) (250 * (input.length + 1)^3) := by
  obtain ⟨t, ht, c, he, hhalt⟩ := raw_outputs input
  apply outputsWithin_of_raw_run (0 : Stack) 13 (outer .save) initialControl program
    input (result input) t (250 * (input.length + 1)^3) ht
  · rw [show ((advance program)^[t]) (rawInit 0 (outer .save) initialControl input) = c from he]
    exact hhalt.1
  · rw [show ((advance program)^[t]) (rawInit 0 (outer .save) initialControl input) = c from he]
    exact hhalt.2

theorem polytime : BitMachine.Polytime result :=
  ⟨machine, 250, 3, outputs⟩

theorem outputs_valid (f : EncodedCNF.Formula) (hf : f.Valid) :
    machine.OutputsWithin (EncodedCNF.encode f) (true :: EncodedCNF.encode f)
      (250 * ((EncodedCNF.encode f).length + 1)^3) := by
  have h := outputs (EncodedCNF.encode f)
  rwa [result_of_decoded (EncodedCNF.decode_encode f hf)] at h

theorem outputs_malformed (input : List Bool) (h : EncodedCNF.decode input = none) :
    machine.OutputsWithin input [false] (250 * (input.length + 1)^3) := by
  have hh := outputs input
  rwa [result_of_malformed h] at hh

end EthInapproximability.CurrentPaper.CNFValidator.Runtime
