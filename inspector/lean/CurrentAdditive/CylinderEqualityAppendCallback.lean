import CurrentAdditive.ContextListSchedulerFixedBound
import CurrentAdditive.CylinderEqualMachine
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast

/-!
One concrete callback for a counted V2 list scheduler.  The selected word is
compared with the caller's context word, while the context and source/index
registers survive.  Three physical copy passes append the resulting bit at
the end of bank 9.  This is a reusable equality-cell callback, not a complete
cylinder feature evaluator.
-/

namespace CurrentAdditive.CylinderEqualityAppendCallback

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := Fin 15
abbrev BLabel := SourceClausePreservingBroadcast.Label
abbrev ELabel := CylinderEqualMachine.Label
abbrev BControl := Unit × Option Bool
abbrev EControl := CylinderEqualMachine.Control
abbrev Control := BControl × EControl

inductive Label where
  | copyContext (l : BLabel)
  | compare (l : ELabel)
  | normalize
  | copyOld (l : BLabel)
  | clearOutput
  | copyResult (l : BLabel)
  | done
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def identityStack : Stack ↪ Stack where
  toFun := id
  inj' := by intro a b h; exact h

theorem bank_id (foreign S : Stack → List Bool) :
    BitMachineStackEmbedding.bank identityStack foreign S = S := by
  funext j
  simpa [identityStack] using
    BitMachineStackEmbedding.bank_at identityStack foreign S j

def compareStack : Fin 3 ↪ Stack where
  toFun k := ![6, 11, 7] k
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def bcontrol (v : BControl) : Control := (v, (true, none, none))
def econtrol (v : EControl) : Control := (((), none), v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copyContext l => BitMachineStackEmbedding.stmt identityStack
      Label.copyContext bcontrol Prod.fst (some (.compare .scan))
      (SourceClausePreservingBroadcast.program 12 14 [11] l)
  | .compare l => BitMachineStackEmbedding.stmt compareStack
      Label.compare econtrol Prod.snd (some .normalize)
      (CylinderEqualMachine.program l)
  | .normalize => load (fun _ => bcontrol ((), none))
      (goto (fun _ => .copyOld .scan))
  | .copyOld l => BitMachineStackEmbedding.stmt identityStack
      Label.copyOld bcontrol Prod.fst (some .clearOutput)
      (SourceClausePreservingBroadcast.program 9 14 [7] l)
  | .clearOutput =>
      pop 9 (fun v b => (((), b), v.2))
        (branch (fun v => v.1.2.isSome)
          (load (fun v => (((), none), v.2))
            (goto (fun _ => .clearOutput)))
          (load (fun v => (((), none), v.2))
            (goto (fun _ => .copyResult .scan))))
  | .copyResult l => BitMachineStackEmbedding.stmt identityStack
      Label.copyResult bcontrol Prod.fst (some .done)
      (SourceClausePreservingBroadcast.program 7 14 [9] l)
  | .done => halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem finite_program : Finite Stack ∧ Finite Label ∧ Finite Control :=
  ⟨inferInstance, inferInstance, inferInstance⟩

def initialBank (word context output : List Bool) : Stack → List Bool :=
  fun k => if k = 6 then word else if k = 12 then context
    else if k = 9 then output else []

def initial (word context output : List Bool) : Config :=
  ⟨some (.copyContext .scan), bcontrol ((), none),
   initialBank word context output⟩

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c')
    (m : Nat) : run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem broadcast_phase (source temp target : Stack)
    (labels : BLabel → Label) (next : Label)
    (hprog : ∀ l, program (labels l) =
      BitMachineStackEmbedding.stmt identityStack labels bcontrol Prod.fst
        (some next) (SourceClausePreservingBroadcast.program
          source temp [target] l))
    (bits : List Bool) (S : Stack → List Bool)
    (hsource : S source = bits) (htemp : S temp = [])
    (hst : source ≠ temp) (hsi : source ≠ target)
    (hti : temp ≠ target) :
    ∃ t ≤ 2 * bits.length + 3,
      run t ⟨some (labels .scan), bcontrol ((), none), S⟩ =
        ⟨some next, bcontrol ((), none),
          SourceClausePreservingBroadcast.result source temp [target] bits S⟩ := by
  let c : TM2.Cfg (fun _ : Stack => Bool) BLabel BControl :=
    ⟨some .scan, ((), none), S⟩
  have hlocal := SourceClausePreservingBroadcast.run_halt
    source temp [target] hst (by simp) (by simp [hsi])
    (by simp [hti]) bits S hsource htemp
  have hh : (((advance (SourceClausePreservingBroadcast.program
      source temp [target]))^[2 * bits.length + 3]) c).l = none := by
    rw [hlocal]
  obtain ⟨t, hbound, hrun⟩ := BitMachineStackEmbedding.outputs
    identityStack S labels bcontrol Prod.fst (by intro v; rfl)
    (some next) (SourceClausePreservingBroadcast.program source temp [target])
    program hprog c (2 * bits.length + 3) hh
  change run t (BitMachineStackEmbedding.cfg identityStack S
    labels bcontrol (some next) c) =
    BitMachineStackEmbedding.cfg identityStack S labels bcontrol
      (some next) (((advance (SourceClausePreservingBroadcast.program
        source temp [target]))^[2 * bits.length + 3]) c) at hrun
  rw [hlocal] at hrun
  refine ⟨t, hbound, ?_⟩
  simpa [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, bank_id, c]
    using hrun

theorem copy_context (word context output : List Bool) :
    ∃ t ≤ 2 * context.length + 3,
      run t (initial word context output) =
        ⟨some (.compare .scan), bcontrol ((), none),
         SourceClausePreservingBroadcast.result 12 14 [11] context
           (initialBank word context output)⟩ := by
  let S := initialBank word context output
  let c : TM2.Cfg (fun _ : Stack => Bool) BLabel BControl :=
    ⟨some .scan, ((), none), S⟩
  have hs : S 12 = context := by simp [S, initialBank]
  have ht : S 14 = [] := by simp [S, initialBank]
  have hlocal := SourceClausePreservingBroadcast.run_halt
    (12 : Stack) 14 [11] (by decide) (by decide) (by decide)
    (by decide) context S hs ht
  have hh : (((advance (SourceClausePreservingBroadcast.program
      (12 : Stack) 14 [11]))^[2 * context.length + 3]) c).l = none := by
    rw [hlocal]
  obtain ⟨t, hbound, hrun⟩ := BitMachineStackEmbedding.outputs
    identityStack S Label.copyContext bcontrol Prod.fst
    (by intro v; rfl) (some (.compare .scan))
    (SourceClausePreservingBroadcast.program (12 : Stack) 14 [11])
    program (by intro l; rfl) c (2 * context.length + 3) hh
  change run t (BitMachineStackEmbedding.cfg identityStack S
    Label.copyContext bcontrol (some (.compare .scan)) c) =
    BitMachineStackEmbedding.cfg identityStack S Label.copyContext
      bcontrol (some (.compare .scan))
      (((advance (SourceClausePreservingBroadcast.program
        (12 : Stack) 14 [11]))^[2 * context.length + 3]) c) at hrun
  have hstart : BitMachineStackEmbedding.cfg identityStack S
      Label.copyContext bcontrol (some (.compare .scan)) c =
      initial word context output := by
    simp [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
      bank_id, c, S, initial]
  rw [hstart, hlocal] at hrun
  refine ⟨t, hbound, ?_⟩
  simpa [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    bank_id] using hrun

theorem compare_phase (left right out : List Bool)
    (S : Stack → List Bool) (hleft : S 6 = left)
    (hright : S 11 = right) (hout : S 7 = out) :
    ∃ t ≤ min left.length right.length + 1,
      ∃ (vFinal : Control) (SFinal : Stack → List Bool),
      run t ⟨some (.compare .scan), bcontrol ((), none), S⟩ =
        ⟨some .normalize, vFinal, SFinal⟩ ∧
      SFinal 7 = decide (left = right) :: out ∧
      (∀ k, k ≠ 6 → k ≠ 11 → k ≠ 7 → SFinal k = S k) := by
  let c := CylinderEqualMachine.cfg (some .scan)
    (true, none, none) left right out
  obtain ⟨t, ht, hhalt, houtput⟩ :=
    CylinderEqualMachine.compare_run true left right out
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    compareStack S Label.compare econtrol Prod.snd
    (by intro v; rfl) (some .normalize)
    CylinderEqualMachine.program program (by intro l; rfl)
    c t hhalt
  change run u (BitMachineStackEmbedding.cfg compareStack S
    Label.compare econtrol (some .normalize) c) =
    BitMachineStackEmbedding.cfg compareStack S Label.compare
      econtrol (some .normalize)
      (CylinderEqualMachine.run t c) at he
  have hstart : BitMachineStackEmbedding.cfg compareStack S
      Label.compare econtrol (some .normalize) c =
      ⟨some (.compare .scan), bcontrol ((), none), S⟩ := by
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
    congr 1
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [compareStack, c,
      CylinderEqualMachine.cfg, CylinderEqualMachine.bank,
      hleft, hright, hout]
  rw [hstart] at he
  change (CylinderEqualMachine.run t c).l = none at hhalt
  simp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    hhalt] at he
  let SFinal := BitMachineStackEmbedding.bank compareStack S
    (CylinderEqualMachine.run t c).stk
  refine ⟨u, hu.trans ht, econtrol (CylinderEqualMachine.run t c).var,
    SFinal, ?_, ?_, ?_⟩
  · simpa [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
      SFinal] using he
  · have hbank := BitMachineStackEmbedding.bank_at compareStack S
      (CylinderEqualMachine.run t c).stk (2 : Fin 3)
    simpa [SFinal, compareStack, c, houtput] using hbank
  · intro k h6 h11 h7
    exact BitMachineStackEmbedding.bank_outside compareStack S
      (CylinderEqualMachine.run t c).stk k (by
        rintro ⟨i, hi⟩
        fin_cases i <;> simp_all [compareStack])

def afterContext (word context output : List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result 12 14 [11] context
    (initialBank word context output)

theorem afterContext_values (word context output : List Bool) :
    afterContext word context output 6 = word ∧
    afterContext word context output 11 = context ∧
    afterContext word context output 7 = [] ∧
    afterContext word context output 9 = output ∧
    afterContext word context output 12 = context ∧
    afterContext word context output 14 = [] := by
  simp [afterContext, SourceClausePreservingBroadcast.result,
    BitMachineBroadcast.prepend, initialBank]

theorem normalize_step (v : Control) (S : Stack → List Bool) :
    run 1 ⟨some .normalize, v, S⟩ =
      ⟨some (.copyOld .scan), bcontrol ((), none), S⟩ := by
  simp [run, advance, TM2.step, TM2.stepAux, program]

theorem clear_output (S : Stack → List Bool) :
    run ((S 9).length + 1)
      ⟨some .clearOutput, bcontrol ((), none), S⟩ =
      ⟨some (.copyResult .scan), bcontrol ((), none),
        Function.update S 9 []⟩ := by
  generalize hs : S 9 = bits
  induction bits generalizing S with
  | nil =>
      simp [run, advance, TM2.step, TM2.stepAux, program, hs,
        bcontrol]
  | cons b tail ih =>
      have hstep : advance program
          ⟨some .clearOutput, bcontrol ((), none), S⟩ =
          ⟨some .clearOutput, bcontrol ((), none),
            Function.update S 9 tail⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, hs,
          bcontrol]
      have htail : (Function.update S 9 tail) 9 = tail := by simp
      have h := ih (Function.update S 9 tail) htail
      rw [List.length_cons, show tail.length + 1 + 1 =
        1 + (tail.length + 1) by omega,
        run_add (show run 1
          ⟨some .clearOutput, bcontrol ((), none), S⟩ =
          ⟨some .clearOutput, bcontrol ((), none),
            Function.update S 9 tail⟩ by
            simpa [run] using hstep) (tail.length + 1)]
      simpa [Function.update_idem] using h

theorem result_target (source temp target : Stack)
    (bits : List Bool) (S : Stack → List Bool)
    (hst : source ≠ temp) (hsource : source ≠ target)
    (htemp : temp ≠ target) :
    SourceClausePreservingBroadcast.result source temp [target]
      bits S target = bits ++ S target := by
  exact SourceClausePreservingBroadcast.target_written source temp
    [target] (by simp [htemp]) (by simp [hsource]) hst
    bits S target (by simp)

theorem result_other (source temp target : Stack)
    (bits : List Bool) (S : Stack → List Bool) (k : Stack)
    (hs : k ≠ source) (ht : k ≠ temp) (hd : k ≠ target) :
    SourceClausePreservingBroadcast.result source temp [target]
      bits S k = S k := by
  simp [SourceClausePreservingBroadcast.result,
    BitMachineBroadcast.prepend, hs, ht, hd]

theorem result_source (source temp target : Stack)
    (bits : List Bool) (S : Stack → List Bool)
    (h : source ≠ temp) :
    SourceClausePreservingBroadcast.result source temp [target]
      bits S source = bits := by
  exact SourceClausePreservingBroadcast.source_restored source temp
    [target] h bits S

theorem result_temp (source temp target : Stack)
    (bits : List Bool) (S : Stack → List Bool) :
    SourceClausePreservingBroadcast.result source temp [target]
      bits S temp = [] := by
  exact SourceClausePreservingBroadcast.temp_empty source temp
    [target] bits S

theorem done_step (v : Control) (S : Stack → List Bool) :
    run 1 ⟨some .done, v, S⟩ = ⟨none, v, S⟩ := by
  rfl

def callbackBound (word context output : List Bool) : Nat :=
  (2 * context.length + 3) +
  (min word.length context.length + 1) + 1 +
  (2 * output.length + 3) + (output.length + 1) +
  (2 * (output.length + 1) + 3) + 1

theorem run_selected (word context output : List Bool)
    (S : Stack → List Bool)
    (hword : S 6 = word) (hcontext : S 12 = context)
    (houtput : S 9 = output)
    (h11 : S 11 = []) (h7 : S 7 = []) (h14 : S 14 = []) :
    ∃ t ≤ callbackBound word context output,
      ∃ (vFinal : Control) (SFinal : Stack → List Bool),
      run t ⟨some (.copyContext .scan), bcontrol ((), none), S⟩ =
        ⟨none, vFinal, SFinal⟩ ∧
      SFinal 9 = output ++ [decide (word = context)] ∧
      (∀ k : Stack, k = 8 ∨ k = 10 ∨ k = 12 ∨ k = 13 →
        SFinal k = S k) := by
  obtain ⟨a, ha, hcopy⟩ := broadcast_phase 12 14 11
    Label.copyContext (.compare .scan) (by intro l; rfl)
    context S hcontext h14 (by decide) (by decide) (by decide)
  let S1 := SourceClausePreservingBroadcast.result 12 14 [11] context S
  have h1word : S1 6 = word := by
    change SourceClausePreservingBroadcast.result 12 14 [11]
      context S 6 = word
    rw [result_other 12 14 11 context S 6 (by decide)
      (by decide) (by decide), hword]
  have h1right : S1 11 = context := by
    simpa [h11] using result_target 12 14 11 context S
      (by decide) (by decide) (by decide)
  have h1out : S1 7 = [] := by
    change SourceClausePreservingBroadcast.result 12 14 [11]
      context S 7 = []
    rw [result_other 12 14 11 context S 7 (by decide)
      (by decide) (by decide), h7]
  obtain ⟨b, hb, v2, S2, hcompare, h2bit, h2foreign⟩ :=
    compare_phase word context [] S1 h1word h1right h1out
  have h2out : S2 9 = output := by
    rw [h2foreign 9 (by decide) (by decide) (by decide)]
    change SourceClausePreservingBroadcast.result 12 14 [11]
      context S 9 = output
    rw [result_other 12 14 11 context S 9 (by decide)
      (by decide) (by decide), houtput]
  have h2temp : S2 14 = [] := by
    rw [h2foreign 14 (by decide) (by decide) (by decide)]
    exact result_temp 12 14 11 context S
  have hnormalize := normalize_step v2 S2
  obtain ⟨c, hc, hcopyOld⟩ := broadcast_phase 9 14 7
    Label.copyOld .clearOutput (by intro l; rfl)
    output S2 h2out h2temp (by decide) (by decide) (by decide)
  let S3 := SourceClausePreservingBroadcast.result 9 14 [7] output S2
  have h3bit : S3 7 = output ++ [decide (word = context)] := by
    simpa [h2bit] using result_target 9 14 7 output S2
      (by decide) (by decide) (by decide)
  have h3out : S3 9 = output := result_source 9 14 7 output S2
    (by decide)
  have h3temp : S3 14 = [] := result_temp 9 14 7 output S2
  have hclear := clear_output S3
  let S4 := Function.update S3 9 []
  have h4bit : S4 7 = output ++ [decide (word = context)] := by
    simpa [S4] using h3bit
  have h4out : S4 9 = [] := by simp [S4]
  have h4temp : S4 14 = [] := by simpa [S4] using h3temp
  obtain ⟨d, hd, hcopyResult⟩ := broadcast_phase 7 14 9
    Label.copyResult .done (by intro l; rfl)
    (output ++ [decide (word = context)]) S4 h4bit h4temp
    (by decide) (by decide) (by decide)
  let S5 := SourceClausePreservingBroadcast.result 7 14 [9]
    (output ++ [decide (word = context)]) S4
  have h5out : S5 9 = output ++ [decide (word = context)] := by
    simpa [h4out] using result_target 7 14 9
      (output ++ [decide (word = context)]) S4
      (by decide) (by decide) (by decide)
  have htotal : run (a + b + 1 + c + (output.length + 1) + d + 1)
      ⟨some (.copyContext .scan), bcontrol ((), none), S⟩ =
      ⟨none, bcontrol ((), none), S5⟩ := by
    have h1 : run a ⟨some (.copyContext .scan), bcontrol ((), none), S⟩ =
        ⟨some (.compare .scan), bcontrol ((), none), S1⟩ := hcopy
    have h2 : run (a + b)
        ⟨some (.copyContext .scan), bcontrol ((), none), S⟩ =
        ⟨some .normalize, v2, S2⟩ :=
      (run_add h1 b).trans hcompare
    have h3 : run (a + b + 1)
        ⟨some (.copyContext .scan), bcontrol ((), none), S⟩ =
        ⟨some (.copyOld .scan), bcontrol ((), none), S2⟩ :=
      (run_add h2 1).trans hnormalize
    have h4 : run (a + b + 1 + c)
        ⟨some (.copyContext .scan), bcontrol ((), none), S⟩ =
        ⟨some .clearOutput, bcontrol ((), none), S3⟩ :=
      (run_add h3 c).trans hcopyOld
    have h5 : run (a + b + 1 + c + (output.length + 1))
        ⟨some (.copyContext .scan), bcontrol ((), none), S⟩ =
        ⟨some (.copyResult .scan), bcontrol ((), none), S4⟩ := by
      rw [run_add h4 (output.length + 1), ← h3out]
      exact hclear
    have h6 : run (a + b + 1 + c + (output.length + 1) + d)
        ⟨some (.copyContext .scan), bcontrol ((), none), S⟩ =
        ⟨some .done, bcontrol ((), none), S5⟩ :=
      (run_add h5 d).trans hcopyResult
    exact (run_add h6 1).trans (done_step _ _)
  refine ⟨a + b + 1 + c + (output.length + 1) + d + 1,
    ?_, bcontrol ((), none), S5, htotal, h5out, ?_⟩
  · unfold callbackBound
    have hlen : (output ++ [decide (word = context)]).length =
        output.length + 1 := by simp
    omega
  · intro k hk
    have hk6 : k ≠ 6 := by rcases hk with h | h | h | h <;> simp_all
    have hk11 : k ≠ 11 := by rcases hk with h | h | h | h <;> simp_all
    have hk7 : k ≠ 7 := by rcases hk with h | h | h | h <;> simp_all
    have hk14 : k ≠ 14 := by rcases hk with h | h | h | h <;> simp_all
    have hk9 : k ≠ 9 := by rcases hk with h | h | h | h <;> simp_all
    have hS1 : S1 k = S k := by
      rcases hk with h | h | h | h
      · subst k; exact result_other 12 14 11 context S 8
          (by decide) (by decide) (by decide)
      · subst k; exact result_other 12 14 11 context S 10
          (by decide) (by decide) (by decide)
      · subst k; simpa [hcontext] using result_source 12 14 11
          context S (by decide)
      · subst k; exact result_other 12 14 11 context S 13
          (by decide) (by decide) (by decide)
    have hS2 : S2 k = S1 k := h2foreign k hk6 hk11 hk7
    have hS3 : S3 k = S2 k := result_other 9 14 7 output S2 k
      hk9 hk14 hk7
    have hS4 : S4 k = S3 k := by simp [S4, hk9]
    have hS5 : S5 k = S4 k := result_other 7 14 9
      (output ++ [decide (word = context)]) S4 k hk7 hk14 hk9
    exact hS5.trans (hS4.trans (hS3.trans (hS2.trans hS1)))

#print axioms finite_program
#print axioms copy_context
#print axioms compare_phase
#print axioms afterContext_values
#print axioms clear_output
#print axioms run_selected

end CurrentAdditive.CylinderEqualityAppendCallback
