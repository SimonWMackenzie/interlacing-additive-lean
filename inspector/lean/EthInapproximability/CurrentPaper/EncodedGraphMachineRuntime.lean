import EthInapproximability.CurrentPaper.EncodedGraphMachineTotal

/-!
# Polynomial runtime of the explicit graph validator

Source: frozen v8 `03-exact-hardness.tex`, explicit graph construction, and
the Boolean-stack machine convention in `06-eth.tex`. Every runtime bound
below counts transitions of the literal fifteen-stack graph controller.
-/

namespace EthInapproximability.CurrentPaper.EncodedGraphMachineRuntime

open Turing BitMachineEncoding EncodedGraphMachine
open EncodedGraphMachineCorrectness EncodedGraphMachineLoops EncodedGraphMachineTotal

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
      run t (cfg (some (outer .finalCheck)) v (edgeData rest original n 0)) = c ∧
      HaltsWith c (if rest = [] then true :: original.reverse else [false]) := by
  cases rest with
  | nil =>
      have hs := run_succ (finalCheck_nil v (edgeData [] original n 0)) 0
      have ha := accept_run original (setPop v none) (edgeData [] original n 0)
      have he := (run_add hs (original.length + 1)).trans ha
      refine ⟨1 + (original.length + 1), by omega, _, he, ?_⟩
      simp [HaltsWith, cfg, Data.stacks, edgeData, run]
  | cons b rest =>
      have hs := run_succ (finalCheck_cons b rest v (edgeData [] original n 0)) 0
      have ha := run_succ (reject_step (setPop v (some b)) (edgeData rest original n 0)) 0
      have he := (run_add hs 1).trans ha
      refine ⟨2, by omega, _, he, ?_⟩
      simp [HaltsWith, cfg, Data.stacks, edgeData, run]

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
          ∃ w : Control, c = cfg (some (outer .edges)) w (edgeData rest original n k)
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
        obtain ⟨w, _, _, hw⟩ := hp
        simp only [hk, ↓reduceIte]
        refine ⟨w, ?_⟩
        simpa [storeNext, EncodedGraphMachineLoops.storeData,
          EncodedGraphMachineCorrectness.storeData, edgeData, countData] using hw
      · simpa [hr, countData, Fits, hf, hk] using hp

def readTail (n L : Nat) (bits : List Bool) : Option (List (Nat × Nat)) := do
  let (count, tail) ← EncodedCommunication.readNat bits
  if count ≤ L then do
    let (edges, rest) ← EncodedGraphBounded.readCheckedEdges n count tail
    if rest = [] then some edges else none
  else none

def tailResult (n L : Nat) (bits original : List Bool) : List Bool :=
  if (readTail n L bits).isSome then true :: original.reverse else [false]

theorem tail_run (v : Control) (hf : field v = .count)
    (bits original : List Bool) (n L : Nat)
    (hinput : bits.length ≤ L) (hn : n ≤ L) :
    ∃ t ≤ 100 * (L + 1)^3 + original.length + 4, ∃ c,
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
        obtain ⟨u, hu, out, hout, hpost⟩ := edge_loop w tail original n count L
          ((readNat_length hr).trans hinput) hn
        have he' := (run_add he u).trans hout
        have hedge : (count + 1) * (50 * (L + 1)^2) ≤ 50 * (L + 1)^3 := by
          have hm := Nat.mul_le_mul_right (50 * (L + 1)^2) (Nat.add_le_add_right hcount 1)
          nlinarith
        cases hedges : EncodedGraphBounded.readCheckedEdges n count tail with
        | none =>
            simp only [hedges] at hpost
            refine ⟨t + u + 1, by nlinarith, _, run_add he' 1, ?_⟩
            simpa [tailResult, readTail, hr, hcount, hedges, edgeData] using
              reject_frame_halts hpost
        | some pair =>
            obtain ⟨edges, rest⟩ := pair
            simp only [hedges] at hpost
            obtain ⟨z, hz⟩ := hpost
            rw [hz] at he'
            obtain ⟨f, hftime, final, hfinal, hhalt⟩ := final_check z rest original n
            refine ⟨t + u + f, by nlinarith, final, (run_add he' f).trans hfinal, ?_⟩
            by_cases hrest : rest = [] <;>
              simpa [tailResult, readTail, hr, hcount, hedges, hrest] using hhalt
      · simp only [hr, hcount, ↓reduceIte] at hp
        refine ⟨t + 1, by nlinarith, _, run_add he 1, ?_⟩
        simpa [tailResult, readTail, hr, hcount, countData] using reject_frame_halts hp

theorem vertex_lengths {input rest : List Bool} {n : Nat}
    (h : EncodedGraph.readUnary input = some (n, rest)) :
    n + 1 + rest.length = input.length := by
  have he := congrArg List.length (EncodedGraph.readUnary_sound h)
  simpa [EncodedGraph.unary, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using he

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
      have hi := readUnary_failure input hr
      have he := vertices_unterminated input.length initialControl (initialData input)
      have hstart : {initialData input with input := List.replicate input.length true} =
          initialData input := by rw [← hi]; rfl
      rw [hstart] at he
      refine ⟨input.length + 1, le_rfl, _, he, ?_⟩
      exact ⟨rfl, rfl, rfl⟩
  | some p =>
      obtain ⟨n, rest⟩ := p
      have hi := EncodedGraph.readUnary_sound hr
      have hl := vertex_lengths hr
      have he := vertices_run n rest initialControl (initialData input)
      have hstart : {initialData input with input := EncodedGraph.unary n ++ rest} =
          initialData input := by rw [hi]; rfl
      rw [hstart] at he
      refine ⟨n + 1, by omega, _, he, ?_⟩
      simp [initialData, countData]

theorem tailResult_eq_result {input rest : List Bool} {n : Nat}
    (h : EncodedGraph.readUnary input = some (n, rest)) :
    tailResult n input.length rest input.reverse = result input := by
  have hd := EncodedGraphBounded.decode_eq input
  simp only [result]
  rw [← hd]
  unfold EncodedGraphBounded.decode
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
      · cases he : EncodedGraphBounded.readCheckedEdges n count tail with
        | none => rfl
        | some p =>
            obtain ⟨edges, suffix⟩ := p
            simp only [Bind.bind, Option.bind]
            split <;> rfl
      · rfl

theorem raw_outputs (input : List Bool) :
    ∃ t ≤ 200 * (input.length + 1)^3, ∃ c,
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
      have hbad : EncodedGraph.decode input = none := by simp [EncodedGraph.decode, hr]
      simpa [initialData, result, hbad] using reject_frame_halts hp
  | some p =>
      obtain ⟨n, rest⟩ := p
      simp only [hr] at hp
      rw [hp] at he'
      have hl := vertex_lengths hr
      obtain ⟨u, hu, out, hout, hhalt⟩ := tail_run (headerControl initialControl) rfl
        rest input.reverse n input.length (by omega) (by omega)
      have hic : ((none, none), (headerControl initialControl).2) =
          headerControl initialControl := rfl
      rw [hic] at hout
      refine ⟨(2 * input.length + 2) + t + u, ?_, out, (run_add he' u).trans hout, ?_⟩
      · simp only [List.length_reverse] at hu
        nlinarith
      · simpa only [tailResult_eq_result hr] using hhalt

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input) (200 * (input.length + 1)^3) := by
  obtain ⟨t, ht, c, he, hhalt⟩ := raw_outputs input
  apply outputsWithin_of_raw_run (0 : Stack) 13 (outer .save) initialControl program
    input (result input) t (200 * (input.length + 1)^3) ht
  · rw [show ((advance program)^[t]) (rawInit 0 (outer .save) initialControl input) = c from he]
    exact hhalt.1
  · rw [show ((advance program)^[t]) (rawInit 0 (outer .save) initialControl input) = c from he]
    exact hhalt.2

theorem polytime : BitMachine.Polytime result :=
  ⟨machine, 200, 3, outputs⟩

end EthInapproximability.CurrentPaper.EncodedGraphMachineRuntime
