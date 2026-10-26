import EthInapproximability.CurrentPaper.SourceUnaryBinaryCall
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.EncodedGraph
import EthInapproximability.CurrentPaper.SourceNormalizationMachineMark

/-!
# Canonical graph endpoint-field writer

Each input unary endpoint is physically converted by the existing finite
binary-successor iteration. The resulting canonical bit word is written as
`EncodedCommunication.field` into a reversed payload bank. A one-bit pair
flag simultaneously counts completed edges in a retained unary bank.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineEndpointWriter

open Turing TM2.Stmt BitMachineEncoding

noncomputable abbrev counter := SourceUnaryBinaryCall.counter

inductive Admin where
  | read | write | pair
  deriving DecidableEq, Fintype

abbrev Stack := BitMachineIteration.Stack counter ⊕ Fin 4
abbrev Label := Admin ⊕ BitMachineIteration.Label counter
abbrev Control := Option Bool × BitMachineIteration.Control counter
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def iterationStack : BitMachineIteration.Stack counter ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def iterationControl (v : BitMachineIteration.Control counter) : Control :=
  (none,v)

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl .read => pop (.inr 0) (fun v b => (b,v.2))
      (branch (fun v => v.1.isSome)
        (branch (fun v => v.1.getD false)
          (push (.inl (.inr 0)) (fun _ => true)
            (goto (fun _ => .inl .read)))
          (load (fun v => (none,v.2))
            (goto (fun _ => .inr (.inr .testFuel)))))
        halt)
  | .inl .write => pop (.inl (.inl counter.input))
      (fun v b => (b,v.2))
      (branch (fun v => v.1.isSome)
        (push (.inr 1) (fun _ => true)
          (push (.inr 1) (fun v => v.1.getD false)
            (goto (fun _ => .inl .write))))
        (push (.inr 1) (fun _ => false)
          (goto (fun _ => .inl .pair))))
  | .inl .pair => pop (.inr 3) (fun v b => (b,v.2))
      (branch (fun v => v.1.isSome)
        (push (.inr 2) (fun _ => true)
          (goto (fun _ => .inl .read)))
        (push (.inr 3) (fun _ => true)
          (goto (fun _ => .inl .read))))
  | .inr l => BitMachineStackEmbedding.stmt iterationStack Sum.inr
      iterationControl Prod.snd (some (.inl .write))
      (BitMachineIteration.program counter l)

noncomputable def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

noncomputable def cfg (l : Option Label) (v : Control)
    (S : BitMachineIteration.Stack counter → List Bool)
    (stream reverseFields edgeCount parity : List Bool) : Config :=
  ⟨l,v,Sum.elim S ![stream,reverseFields,edgeCount,parity]⟩

noncomputable def idleBank (fuel : List Bool) :
    BitMachineIteration.Stack counter → List Bool :=
  (BitMachineIteration.ready counter [] fuel).stk

noncomputable def wordBank (bits : List Bool) :
    BitMachineIteration.Stack counter → List Bool :=
  (BitMachineIteration.finished counter bits).stk

noncomputable def start (stream : List Bool) : Config :=
  cfg (some (.inl .read)) (none,(counter.initial,none))
    (idleBank []) stream [] [] []

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem read_true_step (a : ℕ) (v : Option Bool)
    (stream revout count parity : List Bool) :
    TM2.step program
      (cfg (some (.inl .read)) (v,(counter.initial,none))
        (idleBank (List.replicate a true))
        (true :: stream) revout count parity) =
    some (cfg (some (.inl .read)) (some true,(counter.initial,none))
      (idleBank (List.replicate (a + 1) true))
      stream revout count parity) := by
  apply congrArg (fun S => some
    (⟨some (.inl Admin.read),(some true,(counter.initial,none)),S⟩ : Config))
  funext k
  cases k with
  | inl k =>
      cases k with
      | inl j => simp only [idleBank, SourceUnaryBinaryCall.initial_bank]; rfl
      | inr j => fin_cases j <;> simp only [idleBank, SourceUnaryBinaryCall.initial_bank] <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem read_false_step (a : ℕ) (v : Option Bool)
    (stream revout count parity : List Bool) :
    TM2.step program
      (cfg (some (.inl .read)) (v,(counter.initial,none))
        (idleBank (List.replicate a true))
        (false :: stream) revout count parity) =
    some (cfg (some (.inr (.inr .testFuel)))
      (none,(counter.initial,none))
      (idleBank (List.replicate a true)) stream revout count parity) := by
  apply congrArg (fun S => some
      (⟨some (.inr (.inr (BitMachineIteration.Admin.testFuel))),
      (none,(counter.initial,none)),S⟩ : Config))
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

theorem read_prefix_run (a u : ℕ) (v : Option Bool)
    (stream revout count parity : List Bool) :
    run (u + 1)
      (cfg (some (.inl .read)) (v,(counter.initial,none))
        (idleBank (List.replicate a true))
        (List.replicate u true ++ false :: stream) revout count parity) =
    cfg (some (.inr (.inr .testFuel))) (none,(counter.initial,none))
      (idleBank (List.replicate (a + u) true)) stream revout count parity := by
  induction u generalizing a v with
  | zero =>
      simpa only [List.replicate_zero, List.nil_append, Nat.add_zero,
        zero_add] using run_succ (read_false_step a v stream revout count parity) 0
  | succ u ih =>
      have h := read_true_step a v
        (List.replicate u true ++ false :: stream) revout count parity
      have hs := run_succ h (u + 1)
      have hr := hs.trans (ih (a + 1) (some true))
      have hnum : (a + 1) + u = a + (u + 1) := by omega
      rw [hnum] at hr
      simpa only [List.replicate_succ, List.cons_append, Nat.succ_eq_add_one,
        Nat.add_assoc] using hr

theorem conversion_run (u : ℕ) (stream revout count parity : List Bool) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient * (u + 1) ^ 2,
      run t
        (cfg (some (.inr (.inr .testFuel))) (none,(counter.initial,none))
          (idleBank (List.replicate u true)) stream revout count parity) =
      cfg (some (.inl .write)) (none,(counter.initial,none))
        (wordBank u.bits) stream revout count parity := by
  let input := List.replicate u true
  obtain ⟨t,ht,hr⟩ := SourceUnaryBinaryCall.raw_run input
  let S : Stack → List Bool :=
    Sum.elim (idleBank input) ![stream,revout,count,parity]
  have hhalt : (((advance (BitMachineIteration.program counter))^[t])
      (BitMachineIteration.ready counter [] input)).l = none := by
    change (BitMachineIteration.run counter t
      (BitMachineIteration.ready counter [] input)).l = none
    rw [hr]
    rfl
  obtain ⟨s,hs,he⟩ := BitMachineStackEmbedding.outputs iterationStack S
    Sum.inr iterationControl Prod.snd (by intro x; rfl)
    (some (.inl .write)) (BitMachineIteration.program counter) program
    (by intro l; rfl) (BitMachineIteration.ready counter [] input) t hhalt
  refine ⟨s, ?_, ?_⟩
  · simpa [input, List.length_replicate] using hs.trans ht
  · rw [← BitMachineIteration.run, hr] at he
    simp only [input, List.length_replicate] at he
    change run s (BitMachineStackEmbedding.cfg iterationStack S
        Sum.inr iterationControl (some (.inl .write))
        (BitMachineIteration.ready counter [] input)) =
      BitMachineStackEmbedding.cfg iterationStack S
        Sum.inr iterationControl (some (.inl .write))
        (BitMachineIteration.finished counter u.bits) at he
    convert he using 1
    · apply congrArg (fun B => run s
        (⟨some (.inr (.inr .testFuel)),
          (none,(counter.initial,none)),B⟩ : Config))
      funext k
      cases k with
      | inl k => exact (BitMachineStackEmbedding.bank_at iterationStack S _ k).symm
      | inr k =>
          have hk : ¬ ∃ j, iterationStack j = Sum.inr k := by simp [iterationStack]
          rw [BitMachineStackEmbedding.bank_outside iterationStack S _ _ hk]
    · apply congrArg (fun B => (⟨some (.inl .write),
          (none,(counter.initial,none)),B⟩ : Config))
      funext k
      cases k with
      | inl k => exact (BitMachineStackEmbedding.bank_at iterationStack S _ k).symm
      | inr k =>
          have hk : ¬ ∃ j, iterationStack j = Sum.inr k := by simp [iterationStack]
          rw [BitMachineStackEmbedding.bank_outside iterationStack S _ _ hk]
          rfl

private theorem write_cons_step (b : Bool) (bits stream revout count parity : List Bool) :
    TM2.step program
      (cfg (some (.inl .write)) (none,(counter.initial,none))
        (wordBank (b :: bits)) stream revout count parity) =
    some (cfg (some (.inl .write)) (some b,(counter.initial,none))
      (wordBank bits) stream (b :: true :: revout) count parity) := by
  simp only [TM2.step, program, TM2.stepAux, cfg,
    Sum.elim_inl, SourceUnaryBinaryCall.final_bank, wordBank]
  apply congrArg (fun S => some
    (⟨some (.inl Admin.write),(some b,(counter.initial,none)),S⟩ : Config))
  funext k
  cases k with
  | inl k =>
      cases k with
      | inl j =>
          by_cases h : j = counter.input
          · subst j
            simp [Function.update]
          · simp [Function.update, h]
      | inr j => fin_cases j <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem write_nil_step (v : Option Bool)
    (stream revout count parity : List Bool) :
    TM2.step program
      (cfg (some (.inl .write)) (v,(counter.initial,none))
        (wordBank []) stream revout count parity) =
    some (cfg (some (.inl .pair)) (none,(counter.initial,none))
      (wordBank []) stream (false :: revout) count parity) := by
  simp only [TM2.step, program, TM2.stepAux, cfg,
    Sum.elim_inl, SourceUnaryBinaryCall.final_bank, wordBank]
  apply congrArg (fun S => some
    (⟨some (.inl Admin.pair),(none,(counter.initial,none)),S⟩ : Config))
  funext k
  cases k with
  | inl k =>
      cases k with
      | inl j =>
          by_cases h : j = counter.input
          · subst j; simp [Function.update]
          · simp [Function.update, h]
      | inr j => fin_cases j <;> rfl
  | inr k => fin_cases k <;> rfl

theorem write_field_run (bits stream revout count parity : List Bool)
    (v : Option Bool) :
    run (bits.length + 1)
      (cfg (some (.inl .write)) (v,(counter.initial,none))
        (wordBank bits) stream revout count parity) =
    cfg (some (.inl .pair)) (none,(counter.initial,none))
      (wordBank []) stream
      ((EncodedCommunication.field bits).reverse ++ revout) count parity := by
  induction bits generalizing v revout with
  | nil =>
      simpa [EncodedCommunication.field] using
        run_succ (write_nil_step v stream revout count parity) 0
  | cons b bits ih =>
      have h := write_cons_step b bits stream revout count parity
      have hs := run_succ h (bits.length + 1)
      have hr := hs.trans (ih (b :: true :: revout) (some b))
      simpa [EncodedCommunication.field, List.reverse_cons, List.append_assoc]
        using hr

private theorem wordBank_nil_eq_idleBank_nil : wordBank [] = idleBank [] := by
  rw [wordBank, idleBank, SourceUnaryBinaryCall.final_bank,
    SourceUnaryBinaryCall.initial_bank]
  funext k
  cases k with
  | inl k => by_cases h : k = counter.input <;> simp [h]
  | inr k => fin_cases k <;> simp

private theorem pair_first_step (v : Option Bool)
    (stream revout count : List Bool) :
    TM2.step program
      (cfg (some (.inl .pair)) (v,(counter.initial,none))
        (wordBank []) stream revout count []) =
    some (cfg (some (.inl .read)) (none,(counter.initial,none))
      (idleBank []) stream revout count [true]) := by
  rw [wordBank_nil_eq_idleBank_nil]
  apply congrArg (fun S => some
    (⟨some (.inl Admin.read),(none,(counter.initial,none)),S⟩ : Config))
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

private theorem pair_second_step (v : Option Bool)
    (stream revout count : List Bool) :
    TM2.step program
      (cfg (some (.inl .pair)) (v,(counter.initial,none))
        (wordBank []) stream revout count [true]) =
    some (cfg (some (.inl .read)) (some true,(counter.initial,none))
      (idleBank []) stream revout (true :: count) []) := by
  rw [wordBank_nil_eq_idleBank_nil]
  apply congrArg (fun S => some
    (⟨some (.inl Admin.read),(some true,(counter.initial,none)),S⟩ : Config))
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

noncomputable def fieldCost (u : ℕ) : ℕ :=
  u + 1 + UnaryBinaryEncoding.coefficient * (u + 1) ^ 2 + u.bits.length + 1

theorem field_stage (u : ℕ) (v : Option Bool)
    (stream revout count parity : List Bool) :
    ∃ t ≤ fieldCost u,
      run t
        (cfg (some (.inl .read)) (v,(counter.initial,none))
          (idleBank []) (EncodedGraph.unary u ++ stream) revout count parity) =
      cfg (some (.inl .pair)) (none,(counter.initial,none))
        (wordBank []) stream
        ((EncodedCommunication.natField u).reverse ++ revout) count parity := by
  have hread := read_prefix_run 0 u v stream revout count parity
  have hread' : run (u + 1)
      (cfg (some (.inl .read)) (v,(counter.initial,none))
        (idleBank []) (EncodedGraph.unary u ++ stream) revout count parity) =
      cfg (some (.inr (.inr .testFuel))) (none,(counter.initial,none))
        (idleBank (List.replicate u true)) stream revout count parity := by
    simpa [EncodedGraph.unary] using hread
  obtain ⟨s,hs,hconvert⟩ := conversion_run u stream revout count parity
  have hwrite := write_field_run u.bits stream revout count parity none
  have hfirst := (run_add hread' s).trans hconvert
  have hfull := (run_add hfirst (u.bits.length + 1)).trans hwrite
  refine ⟨u + 1 + s + (u.bits.length + 1), ?_, ?_⟩
  · unfold fieldCost
    omega
  · simpa only [EncodedCommunication.natField] using hfull

noncomputable def edgeCost (p : ℕ × ℕ) : ℕ :=
  fieldCost p.1 + 1 + fieldCost p.2 + 1

theorem edge_stage (u v : ℕ) (ctl : Option Bool)
    (stream revout count : List Bool) :
    ∃ t ≤ edgeCost (u,v),
      run t
        (cfg (some (.inl .read)) (ctl,(counter.initial,none))
          (idleBank [])
          (EncodedGraph.unary u ++ EncodedGraph.unary v ++ stream)
          revout count []) =
      cfg (some (.inl .read)) (some true,(counter.initial,none))
        (idleBank []) stream
        ((EncodedCommunication.natField u ++
          EncodedCommunication.natField v).reverse ++ revout)
        (true :: count) [] := by
  obtain ⟨a,ha,hfirst⟩ := field_stage u ctl
    (EncodedGraph.unary v ++ stream) revout count []
  have hpair₁ := pair_first_step none (EncodedGraph.unary v ++ stream)
    ((EncodedCommunication.natField u).reverse ++ revout) count
  have hafter₁ := (run_add hfirst 1).trans (run_succ hpair₁ 0)
  obtain ⟨b,hb,hsecond⟩ := field_stage v none stream
    ((EncodedCommunication.natField u).reverse ++ revout) count [true]
  have hafter₂ := (run_add hafter₁ b).trans hsecond
  have hpair₂ := pair_second_step none stream
    ((EncodedCommunication.natField v).reverse ++
      ((EncodedCommunication.natField u).reverse ++ revout)) count
  have hfull := (run_add hafter₂ 1).trans (run_succ hpair₂ 0)
  refine ⟨a + 1 + b + 1, ?_, ?_⟩
  · change a + 1 + b + 1 ≤ fieldCost u + 1 + fieldCost v + 1
    omega
  · simpa only [List.append_assoc, List.reverse_append] using hfull

def unaryEdges : List (ℕ × ℕ) → List Bool
  | [] => []
  | p :: ps => EncodedGraph.unary p.1 ++ EncodedGraph.unary p.2 ++ unaryEdges ps

theorem unaryEdges_eq_endpointStream (ps : List (ℕ × ℕ)) :
    unaryEdges ps = SourceNormalizationMachineMark.endpointStream
      (ps.flatMap fun p => [p.1,p.2]) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [unaryEdges, List.flatMap_cons]
      rw [ih]
      simp [SourceNormalizationMachineMark.endpointStream, List.append_assoc]

noncomputable def edgesCost : List (ℕ × ℕ) → ℕ
  | [] => 0
  | p :: ps => edgeCost p + edgesCost ps

def endingControl (ps : List (ℕ × ℕ)) (ctl : Option Bool) : Option Bool :=
  if ps.isEmpty then ctl else some true

theorem edges_stage (ps : List (ℕ × ℕ)) (ctl : Option Bool)
    (revout count : List Bool) :
    ∃ t ≤ edgesCost ps,
      run t
        (cfg (some (.inl .read)) (ctl,(counter.initial,none))
          (idleBank []) (unaryEdges ps) revout count []) =
      cfg (some (.inl .read)) (endingControl ps ctl,(counter.initial,none))
        (idleBank []) []
        ((EncodedGraph.edgeFields ps).reverse ++ revout)
        (List.replicate ps.length true ++ count) [] := by
  induction ps generalizing ctl revout count with
  | nil =>
      refine ⟨0, by simp [edgesCost], ?_⟩
      simp [run, unaryEdges, endingControl, EncodedGraph.edgeFields]
  | cons p ps ih =>
      rcases p with ⟨u,v⟩
      obtain ⟨a,ha,hfirst⟩ := edge_stage u v ctl
        (unaryEdges ps) revout count
      obtain ⟨b,hb,hsecond⟩ := ih (some true)
        ((EncodedCommunication.natField u ++
          EncodedCommunication.natField v).reverse ++ revout)
        (true :: count)
      have hfull := (run_add hfirst b).trans hsecond
      refine ⟨a + b, ?_, ?_⟩
      · change a + b ≤ edgeCost (u,v) + edgesCost ps
        omega
      · simpa [unaryEdges, endingControl, EncodedGraph.edgeFields,
          List.reverse_append, List.replicate_add, List.append_assoc]
          using hfull

private theorem read_empty_step (v : Option Bool)
    (revout count : List Bool) :
    TM2.step program
      (cfg (some (.inl .read)) (v,(counter.initial,none))
        (idleBank []) [] revout count []) =
    some (cfg none (none,(counter.initial,none))
      (idleBank []) [] revout count []) := by
  apply congrArg (fun S => some
    (⟨none,(none,(counter.initial,none)),S⟩ : Config))
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

theorem writer_run (ps : List (ℕ × ℕ)) :
    ∃ t ≤ edgesCost ps + 1,
      run t (start (unaryEdges ps)) =
      cfg none (none,(counter.initial,none)) (idleBank []) []
        (EncodedGraph.edgeFields ps).reverse
        (List.replicate ps.length true) [] := by
  obtain ⟨t,ht,hr⟩ := edges_stage ps none [] []
  have hstop := read_empty_step (endingControl ps none)
    (EncodedGraph.edgeFields ps).reverse (List.replicate ps.length true)
  refine ⟨t + 1, by omega, ?_⟩
  simp only [List.append_nil] at hr
  have hfull := (run_add hr 1).trans (run_succ hstop 0)
  simpa only [start] using hfull

end EthInapproximability.CurrentPaper.SourceNormalizationMachineEndpointWriter
