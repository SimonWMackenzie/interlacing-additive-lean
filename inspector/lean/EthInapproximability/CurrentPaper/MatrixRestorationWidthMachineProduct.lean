import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.Parameters

/-!
# Physical unary target for restoration width

The fixed twelve-bank program starts from four unary operands `b,c,s,q`,
writes the literal constant 1280, and executes four preserving unary
multiplication phases. Its result is `1280*b*c*s*q`. The constant is a fixed
finite instruction expansion; no input-dependent arithmetic is executed by
the host language or finite control. The ceiling logarithm and power are
separate physical phases in the parent owner.
-/

namespace EthInapproximability.CurrentPaper.MatrixRestorationWidthMachineProduct

open Turing Turing.TM2.Stmt BitMachineEncoding

set_option maxRecDepth 8192

inductive Label where
  | constant
  | multiply (phase : Fin 4) (label : MatrixAddressMachine.Label)
  deriving DecidableEq, Fintype

abbrev Stack := Fin 12
abbrev Control := Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def slots (p : Fin 4) : Fin 6 ↪ Stack where
  toFun := ![![0,1,9,10,11,5], ![5,2,9,10,11,6],
    ![6,3,9,10,11,7], ![7,4,9,10,11,8]] p
  inj' := by fin_cases p <;> decide

def next (p : Fin 4) : Option Label :=
  if h : p.val+1 < 4 then some (.multiply ⟨p.val+1,h⟩ .outer) else none

def pushOn (r : Stack) : ℕ → TM2.Stmt (fun _ : Stack => Bool) Label Control →
    TM2.Stmt (fun _ : Stack => Bool) Label Control
  | 0, q => q
  | k+1, q => push r (fun _ => true) (pushOn r k q)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .constant => pushOn 4 1280 (goto (fun _ => .multiply 0 .outer))
  | .multiply p l => BitMachineStackEmbedding.stmt (slots p)
      (fun k => .multiply p k) id id (next p) (MatrixAddressMachine.program l)

def unary (n : ℕ) : List Bool := List.replicate n true

def inputBank (b c s q : ℕ) : Stack → List Bool :=
  ![unary b,unary c,unary s,unary q,[],[],[],[],[],[],[],[]]

def constantBank (b c s q : ℕ) : Stack → List Bool :=
  ![unary b,unary c,unary s,unary q,unary 1280,[],[],[],[],[],[],[]]

def outputBank (b c s q : ℕ) : Stack → List Bool :=
  ![unary b,unary c,unary s,unary q,unary 1280,
    unary (b*c),unary (b*c*s),unary (b*c*s*q),
    unary (1280*b*c*s*q),[],[],[]]

def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) : Config := ⟨l,v,S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m+n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem pushOn_step (r : Stack) (k : ℕ)
    (q : TM2.Stmt (fun _ : Stack => Bool) Label Control)
    (v : Control) (S : Stack → List Bool) :
    TM2.stepAux (pushOn r k q) v S =
      TM2.stepAux q v
        (Function.update S r (unary k ++ S r)) := by
  induction k generalizing S with
  | zero => simp [pushOn, unary]
  | succ k ih =>
      simp only [pushOn, TM2.stepAux]
      rw [ih]
      simp only [Function.update_self]
      have he : Function.update (Function.update S r (true :: S r)) r
          (unary k ++ true :: S r) =
          Function.update S r (unary (k+1) ++ S r) := by
        funext j
        by_cases hj : j = r
        · subst j
          simp [unary, List.replicate_succ', List.append_assoc]
        · simp [hj]
      rw [he]

theorem constant_step (b c s q : ℕ) :
    advance program (cfg (some .constant) false (inputBank b c s q)) =
      cfg (some (.multiply 0 .outer)) false (constantBank b c s q) := by
  simp only [advance, TM2.step, program, cfg, Option.getD_some,
    pushOn_step, TM2.stepAux]
  congr 1
  funext k
  fin_cases k <;> rfl

/-- One actual multiplication phase changes only its selected output bank.
The six selected input/work-bank hypotheses are physical bank equalities. -/
theorem phase_run (p : Fin 4) (row width : ℕ) (S : Stack → List Bool)
    (hS : ∀ k : Fin 6, S (slots p k) =
      ![unary row,unary width,[],[],[],S (slots p 5)] k) :
    ∃ t ≤ MatrixAddressMachine.exactTime row width 0,
      run t (cfg (some (.multiply p .outer)) false S) =
        cfg (next p) false (Function.update S (slots p 5)
          (unary (row*width) ++ S (slots p 5))) := by
  let input := MatrixAddressMachine.cfg (some .outer) false
    (unary row) (unary width) [] [] [] (S (slots p 5))
  let output := MatrixAddressMachine.cfg none false
    (unary row) (unary width) [] [] []
    (unary (row*width) ++ S (slots p 5))
  have hr : ((advance MatrixAddressMachine.program)^[(MatrixAddressMachine.exactTime row width 0)])
      input = output := by
    simpa only [Nat.add_zero, unary] using
      (MatrixAddressMachine.address_run row width 0 false (S (slots p 5)))
  have hh : (((advance MatrixAddressMachine.program)^[(MatrixAddressMachine.exactTime row width 0)])
      input).l = none := by rw [hr]; rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs (slots p) S
    (fun l => Label.multiply p l) id id (fun _ => rfl) (next p)
    MatrixAddressMachine.program program (fun _ => rfl)
    input (MatrixAddressMachine.exactTime row width 0) hh
  rw [hr] at he
  have hbank : BitMachineStackEmbedding.bank (slots p) S input.stk = S :=
    BitMachineStackEmbedding.bank_eq_self (slots p) S input.stk (fun k => (hS k).symm)
  have hout : output.stk = Function.update input.stk 5
      (unary (row*width) ++ S (slots p 5)) := by
    funext k
    fin_cases k <;> rfl
  have hi : BitMachineStackEmbedding.cfg (slots p) S
      (fun l => Label.multiply p l) id (next p) input =
      cfg (some (.multiply p .outer)) false S := by
    change (⟨_,_,BitMachineStackEmbedding.bank (slots p) S input.stk⟩ : Config) = _
    rw [hbank]
    rfl
  have ho : BitMachineStackEmbedding.cfg (slots p) S
      (fun l => Label.multiply p l) id (next p) output =
      cfg (next p) false
        (Function.update S (slots p 5)
          (unary (row*width) ++ S (slots p 5))) := by
    change (⟨_,_,BitMachineStackEmbedding.bank (slots p) S output.stk⟩ : Config) = _
    rw [hout, BitMachineStackEmbedding.bank_update, hbank]
    rfl
  exact ⟨t, ht, by simpa only [run, hi, ho] using he⟩

def productTime (b c s q : ℕ) : ℕ :=
  1 + MatrixAddressMachine.exactTime b c 0 +
    MatrixAddressMachine.exactTime (b*c) s 0 +
    MatrixAddressMachine.exactTime (b*c*s) q 0 +
    MatrixAddressMachine.exactTime (b*c*s*q) 1280 0

theorem product_run (b c s q : ℕ) :
    ∃ t ≤ productTime b c s q,
      run t (cfg (some .constant) false (inputBank b c s q)) =
        cfg none false (outputBank b c s q) := by
  let S₀ := constantBank b c s q
  let S₁ := Function.update S₀ 5 (unary (b*c))
  let S₂ := Function.update S₁ 6 (unary (b*c*s))
  let S₃ := Function.update S₂ 7 (unary (b*c*s*q))
  have h₀ := phase_run 0 b c S₀ (by intro k; fin_cases k <;> rfl)
  obtain ⟨t₀, ht₀, hr₀⟩ := h₀
  have hS₁ : Function.update S₀ (slots 0 5)
      (unary (b*c) ++ S₀ (slots 0 5)) = S₁ := by
    change Function.update S₀ 5 (unary (b*c) ++ S₀ 5) =
      Function.update S₀ 5 (unary (b*c))
    have hz : S₀ 5 = [] := rfl
    rw [hz, List.append_nil]
  rw [hS₁] at hr₀
  obtain ⟨t₁, ht₁, hr₁⟩ := phase_run 1 (b*c) s S₁
    (by intro k; fin_cases k <;> rfl)
  have hS₂ : Function.update S₁ (slots 1 5)
      (unary (b*c*s) ++ S₁ (slots 1 5)) = S₂ := by
    change Function.update S₁ 6 (unary (b*c*s) ++ S₁ 6) =
      Function.update S₁ 6 (unary (b*c*s))
    have hz : S₁ 6 = [] := by simp [S₁,S₀,constantBank]
    rw [hz, List.append_nil]
  rw [hS₂] at hr₁
  obtain ⟨t₂, ht₂, hr₂⟩ := phase_run 2 (b*c*s) q S₂
    (by intro k; fin_cases k <;> rfl)
  have hS₃ : Function.update S₂ (slots 2 5)
      (unary (b*c*s*q) ++ S₂ (slots 2 5)) = S₃ := by
    change Function.update S₂ 7 (unary (b*c*s*q) ++ S₂ 7) =
      Function.update S₂ 7 (unary (b*c*s*q))
    have hz : S₂ 7 = [] := by simp [S₂,S₁,S₀,constantBank]
    rw [hz, List.append_nil]
  rw [hS₃] at hr₂
  obtain ⟨t₃, ht₃, hr₃⟩ := phase_run 3 (b*c*s*q) 1280 S₃
    (by intro k; fin_cases k <;> rfl)
  have hS₄ : Function.update S₃ (slots 3 5)
      (unary ((b*c*s*q)*1280) ++ S₃ (slots 3 5)) = outputBank b c s q := by
    have hz : S₃ 8 = [] := by simp [S₃,S₂,S₁,S₀,constantBank]
    change Function.update S₃ 8 (unary ((b*c*s*q)*1280) ++ S₃ 8) =
      outputBank b c s q
    rw [hz, List.append_nil]
    have hmul : b*c*s*q*1280 = 1280*b*c*s*q := by ring
    rw [hmul]
    funext k
    fin_cases k <;>
      simp [S₃,S₂,S₁,S₀,outputBank,constantBank]
  rw [hS₄] at hr₃
  have hstart : run 1 (cfg (some .constant) false (inputBank b c s q)) =
      cfg (some (.multiply 0 .outer)) false S₀ := by
    simpa only [run, Function.iterate_one, S₀] using constant_step b c s q
  have hrun := (run_add (run_add (run_add (run_add hstart t₀ |>.trans hr₀) t₁ |>.trans hr₁)
    t₂ |>.trans hr₂) t₃).trans hr₃
  refine ⟨1+t₀+t₁+t₂+t₃, ?_, ?_⟩
  · dsimp [productTime]
    omega
  · simpa only [Nat.add_assoc] using hrun

end EthInapproximability.CurrentPaper.MatrixRestorationWidthMachineProduct
