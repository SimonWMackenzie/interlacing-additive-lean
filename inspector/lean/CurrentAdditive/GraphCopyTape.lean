import CurrentAdditive.GraphCopyResource

/-! Single input-tape adapter for selected v39 sources.tex:69-78. The input
word is unary N followed by the ORIGINAL canonical graph code. The prefix is
physically scanned into its retained counter bank before the graph decoder. -/

namespace Paper2.CurrentAdditive.GraphCopyTape

open EthInapproximability.CurrentPaper Turing TM2.Stmt BitMachineEncoding
open Paper2.CurrentAdditive.GraphCopyPadding

abbrev Stack := GraphCopyEncoded.Stack
abbrev Label := Unit ⊕ GraphCopyEncoded.Label
abbrev Control := Option Bool × GraphCopyEncoded.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def inputStack : Stack := .inl (.inl 0)
def nStack : Stack := .inr (.inr 0)
noncomputable def outputStack : Stack := GraphCopyEncoded.outputStack
noncomputable def initialCode : GraphCopyEncoded.Control := (GraphCopyEncoded.start [] 0).var
noncomputable def prefixControl (v : Option Bool) : Control := (v, initialCode)
def codeControl (v : GraphCopyEncoded.Control) : Control := (none, v)

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl _ => pop inputStack (fun _ b => prefixControl b)
      (branch (fun v => v.1.isSome)
        (branch (fun v => v.1.getD false)
          (push nStack (fun _ => true) (goto (fun _ => .inl ())))
          (load (fun _ => codeControl initialCode)
            (goto (fun _ => .inr (.inl (.inr .capScan))))))
        halt)
  | .inr l => BitMachineStackEmbedding.stmt (Function.Embedding.refl Stack)
      Sum.inr codeControl Prod.snd none (GraphCopyEncoded.program l)

noncomputable def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_succ {c d : Config} (h : advance program c = d) (u : ℕ) :
    run (u + 1) c = run u d := by
  simp only [run, Function.iterate_succ_apply, h]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

noncomputable def prefixCfg (v : Option Bool) (word : List Bool) (n : ℕ) : Config :=
  ⟨some (.inl ()), prefixControl v,
    fun k => if k = inputStack then word else if k = nStack then List.replicate n true else []⟩

noncomputable def codeStart (bits : List Bool) (N : ℕ) : Config :=
  ⟨some (.inr (.inl (.inr .capScan))), codeControl initialCode,
    fun k => if k = inputStack then bits else if k = nStack then List.replicate N true else []⟩

private theorem prefix_true (v : Option Bool) (bits : List Bool) (n : ℕ) :
    advance program (prefixCfg v (true :: bits) n) = prefixCfg (some true) bits (n + 1) := by
  apply congrArg (fun S => (⟨some (.inl ()), prefixControl (some true), S⟩ : Config))
  funext k
  by_cases hi : k = inputStack
  · subst k
    simp [advance, TM2.step, TM2.stepAux, program, prefixCfg, inputStack, nStack]
  · by_cases hn : k = nStack
    · subst k
      simp [advance, TM2.step, TM2.stepAux, program, prefixCfg, inputStack, nStack,
        List.replicate_succ]
    · change k ≠ Sum.inl (Sum.inl 0) at hi
      change k ≠ Sum.inr (Sum.inr 0) at hn
      simp [advance, TM2.step, TM2.stepAux, program, prefixCfg, hi, hn,
        inputStack, nStack]

private theorem prefix_false (v : Option Bool) (bits : List Bool) (n : ℕ) :
    advance program (prefixCfg v (false :: bits) n) = codeStart bits n := by
  apply congrArg (fun S => (⟨some (.inr (.inl (.inr .capScan))), codeControl initialCode, S⟩ : Config))
  funext k
  by_cases hi : k = inputStack
  · subst k
    simp [advance, TM2.step, TM2.stepAux, program, prefixCfg, codeStart, inputStack, nStack]
  · change k ≠ Sum.inl (Sum.inl 0) at hi
    simp [advance, TM2.step, TM2.stepAux, program, prefixCfg, codeStart, hi,
      inputStack, nStack]

theorem prefix_run (N n : ℕ) (bits : List Bool) (v : Option Bool) :
    run (N + 1) (prefixCfg v (EncodedGraph.unary N ++ bits) n) = codeStart bits (n + N) := by
  induction N generalizing n v with
  | zero => simpa [EncodedGraph.unary, run] using prefix_false v bits n
  | succ N ih =>
      have hp : EncodedGraph.unary (N + 1) ++ bits =
          true :: (EncodedGraph.unary N ++ bits) := by
        simp [EncodedGraph.unary, List.replicate_succ]
      rw [hp]
      have h := (run_succ (prefix_true v (EncodedGraph.unary N ++ bits) n) (N + 1)).trans
        (ih (n + 1) (some true))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem original_code_stacks (bits : List Bool) (N : ℕ) (k : Stack) :
    (GraphCopyEncoded.start bits N).stk k =
      if k = inputStack then bits else if k = nStack then List.replicate N true else [] := by
  cases k with
  | inl k =>
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | inr k =>
      cases k with
      | inl k => simp [GraphCopyEncoded.start, inputStack, nStack]
      | inr k => fin_cases k <;> rfl

private theorem code_start (bits : List Bool) (N : ℕ) :
    codeStart bits N = BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack)
      (codeStart bits N).stk Sum.inr codeControl none (GraphCopyEncoded.start bits N) := by
  have hb := BitMachineStackEmbedding.bank_eq_self (Function.Embedding.refl Stack)
    (codeStart bits N).stk (GraphCopyEncoded.start bits N).stk (by
      intro k
      exact original_code_stacks bits N k)
  change (⟨some (.inr (.inl (.inr .capScan))), codeControl initialCode,
    (codeStart bits N).stk⟩ : Config) =
    ⟨some (.inr (.inl (.inr .capScan))), codeControl initialCode,
      BitMachineStackEmbedding.bank (Function.Embedding.refl Stack)
        (codeStart bits N).stk (GraphCopyEncoded.start bits N).stk⟩
  rw [hb]

noncomputable def finalHost (g : EncodedGraph.Graph) (N : ℕ) : Config :=
  BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack)
    (codeStart (EncodedGraph.encode g) N).stk Sum.inr codeControl none
    (GraphCopyEncoded.finalHost g N)

def encodeInput (g : EncodedGraph.Graph) (N : ℕ) : List Bool :=
  EncodedGraph.unary N ++ EncodedGraph.encode g

theorem encodeInput_length (g : EncodedGraph.Graph) (N : ℕ) :
    (encodeInput g N).length = GraphCopyResource.inputSize g N := by
  simp [encodeInput, EncodedGraph.unary, GraphCopyResource.inputSize]
  omega

noncomputable def coefficient : ℕ := 200 * UnaryBinaryEncoding.coefficient + 5201

theorem tape_run (g : EncodedGraph.Graph) (hg : g.Valid) (N : ℕ)
    (hm : 0 < g.edges.length) :
    ∃ t ≤ coefficient * ((encodeInput g N).length + 1)^6,
      run t (prefixCfg none (encodeInput g N) 0) = finalHost g N := by
  have hp : run (N + 1) (prefixCfg none (encodeInput g N) 0) =
      codeStart (EncodedGraph.encode g) N := by
    simpa only [encodeInput, Nat.zero_add] using prefix_run N 0 (EncodedGraph.encode g) none
  obtain ⟨a, ha, hr⟩ := GraphCopyResource.encoded_graph_copy_polynomial_run g hg N hm
  obtain ⟨b, hb, he⟩ := BitMachineStackEmbedding.outputs (Function.Embedding.refl Stack)
    (codeStart (EncodedGraph.encode g) N).stk Sum.inr codeControl Prod.snd
    (by intro v; rfl) none GraphCopyEncoded.program program (by intro l; rfl)
    (GraphCopyEncoded.start (EncodedGraph.encode g) N) a (by
      change (GraphCopyEncoded.run a _).l = none
      rw [hr]; rfl)
  change ((advance GraphCopyEncoded.program)^[a]) _ = _ at hr
  rw [hr] at he
  have hN : N + 1 ≤ ((encodeInput g N).length + 1)^6 := by
    rw [encodeInput_length]
    have hp : GraphCopyResource.inputSize g N + 1 ≤
        (GraphCopyResource.inputSize g N + 1)^6 := by
      simpa only [pow_one] using (Nat.pow_le_pow_right
        (show 0 < GraphCopyResource.inputSize g N + 1 by omega) (show 1 ≤ 6 by decide))
    unfold GraphCopyResource.inputSize at *
    omega
  refine ⟨N + 1 + b, ?_, ?_⟩
  · rw [encodeInput_length] at *
    unfold coefficient
    nlinarith
  · exact (run_add hp b).trans ((congrArg (run b) (code_start _ _)).trans he)

theorem final_output (g : EncodedGraph.Graph) (N : ℕ) :
    (finalHost g N).stk outputStack =
      EncodedGraph.encode (encodedCopies g (copies N g.edges.length)) := by
  change BitMachineStackEmbedding.bank (Function.Embedding.refl Stack) _ _
    ((Function.Embedding.refl Stack) GraphCopyEncoded.outputStack) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact GraphCopyEncoded.final_output g N

noncomputable def machine : BitMachine.Machine :=
  ofFinite inputStack outputStack (.inl ()) (prefixControl none) program

/-- A concrete one-input, one-output bit machine on every valid canonical
source pair. The result is the actual graph-copy code, not an abstract graph. -/
theorem machine_outputs (g : EncodedGraph.Graph) (hg : g.Valid) (N : ℕ)
    (hm : 0 < g.edges.length) :
    machine.OutputsWithin (encodeInput g N)
      (EncodedGraph.encode (encodedCopies g (copies N g.edges.length)))
      (coefficient * ((encodeInput g N).length + 1)^6) := by
  obtain ⟨t, ht, hr⟩ := tape_run g hg N hm
  have hi : rawInit inputStack (.inl ()) (prefixControl none) (encodeInput g N) =
      prefixCfg none (encodeInput g N) 0 := by
    simp only [rawInit, prefixCfg, List.replicate_zero, ite_self]
  apply outputsWithin_of_raw_run inputStack outputStack (.inl ()) (prefixControl none)
    program (encodeInput g N) _ t _ ht
  · rw [hi]
    change (run t _).l = none
    rw [hr]
    rfl
  · rw [hi]
    change (run t _).stk outputStack = _
    rw [hr]
    exact final_output g N

#print axioms machine_outputs
#print axioms tape_run

end Paper2.CurrentAdditive.GraphCopyTape
