import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Physical address arithmetic for a template query

Source: locked v8 `B-effectivity-details.tex`, `thm:paper-materialization`.
Three actual preserving unary multiply-add runs compute `ell * width1`
and `(z * d + alpha) * a`. The intermediate value is physically written
before the last multiplication; it is not supplied as input.
-/

namespace EthInapproximability.CurrentPaper.MatrixTemplateAddressSetup

open Turing BitMachineEncoding

abbrev Label := Fin 3 × MatrixAddressMachine.Label
abbrev Config := TM2.Cfg (fun _ : Fin 12 => Bool) Label Bool

def slots (p : Fin 3) : Fin 6 ↪ Fin 12 where
  toFun := ![![0, 1, 6, 7, 8, 9], ![2, 3, 4, 7, 8, 10], ![10, 5, 6, 7, 8, 11]] p
  inj' := by fin_cases p <;> decide

def next (p : Fin 3) : Option Label :=
  if h : p.val + 1 < 3 then some (⟨p.val + 1, h⟩, .outer) else none

def program (l : Label) : TM2.Stmt (fun _ : Fin 12 => Bool) Label Bool :=
  BitMachineStackEmbedding.stmt (slots l.1) (fun k => (l.1, k)) id id (next l.1)
    (MatrixAddressMachine.program l.2)

def cfg (l : Option Label) (s : Bool) (S : Fin 12 → List Bool) : Config := ⟨l, s, S⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

/-- One actual multiply-add phase, including the exact frame outside its
six selected stacks. It does not charge a stack-bank replacement as a step. -/
theorem phase_run (p : Fin 3) (row width column : ℕ) (s : Bool)
    (S : Fin 12 → List Bool)
    (hS : ∀ k : Fin 6, S (slots p k) =
      ![List.replicate row true, List.replicate width true, List.replicate column true,
        [], [], S (slots p 5)] k) :
    ∃ t ≤ MatrixAddressMachine.exactTime row width column,
      run t (cfg (some (p, .outer)) s S) =
        cfg (next p) false (Function.update S (slots p 5)
          (List.replicate (row * width + column) true ++ S (slots p 5))) := by
  let input := MatrixAddressMachine.cfg (some .outer) s
    (List.replicate row true) (List.replicate width true) (List.replicate column true)
    [] [] (S (slots p 5))
  let output := MatrixAddressMachine.cfg none false
    (List.replicate row true) (List.replicate width true) (List.replicate column true)
    [] [] (List.replicate (row * width + column) true ++ S (slots p 5))
  have hr :
      ((advance MatrixAddressMachine.program)^[MatrixAddressMachine.exactTime row width column])
        input = output := MatrixAddressMachine.address_run row width column s (S (slots p 5))
  have hh :
      (((advance MatrixAddressMachine.program)^[MatrixAddressMachine.exactTime row width column])
        input).l = none := by rw [hr]; rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs (slots p) S (fun k => (p, k))
    id id (fun _ => rfl) (next p) MatrixAddressMachine.program program (fun _ => rfl)
    input (MatrixAddressMachine.exactTime row width column) hh
  rw [hr] at he
  have hbank : BitMachineStackEmbedding.bank (slots p) S input.stk = S :=
    BitMachineStackEmbedding.bank_eq_self (slots p) S input.stk (fun k => (hS k).symm)
  have ho : output.stk = Function.update input.stk 5
      (List.replicate (row * width + column) true ++ S (slots p 5)) := by
    funext k; fin_cases k <;> rfl
  have hi : BitMachineStackEmbedding.cfg (slots p) S (fun k => (p, k)) id (next p) input =
      cfg (some (p, .outer)) s S := by
    change (⟨_, _, BitMachineStackEmbedding.bank (slots p) S input.stk⟩ : Config) = _
    rw [hbank]
    rfl
  have ho' : BitMachineStackEmbedding.cfg (slots p) S (fun k => (p, k)) id (next p) output =
      cfg (next p) false (Function.update S (slots p 5)
        (List.replicate (row * width + column) true ++ S (slots p 5))) := by
    change (⟨_, _, BitMachineStackEmbedding.bank (slots p) S output.stk⟩ : Config) = _
    rw [ho, BitMachineStackEmbedding.bank_update, hbank]
    rfl
  exact ⟨t, ht, by simpa only [run, hi, ho'] using he⟩

def contents (ell width1 z d alpha a : ℕ) (s1 mid s2 : List Bool) : Fin 12 → List Bool :=
  ![List.replicate ell true, List.replicate width1 true, List.replicate z true,
    List.replicate d true, List.replicate alpha true, List.replicate a true,
    [], [], [], s1, mid, s2]

def bound (ell width1 z d alpha a : ℕ) : ℕ :=
  MatrixAddressMachine.exactTime ell width1 0 +
    MatrixAddressMachine.exactTime z d alpha +
    MatrixAddressMachine.exactTime (z * d + alpha) a 0

/-- All address inputs survive; both output suffixes survive; scratch is
empty. Stack 10 retains the computed intermediate value for caller cleanup. -/
theorem setup_run (ell width1 z d alpha a : ℕ) (s : Bool) (out1 out2 : List Bool) :
    ∃ t ≤ bound ell width1 z d alpha a,
      run t (cfg (some (0, .outer)) s (contents ell width1 z d alpha a out1 [] out2)) =
        cfg none false (contents ell width1 z d alpha a
          (List.replicate (ell * width1) true ++ out1)
          (List.replicate (z * d + alpha) true)
          (List.replicate ((z * d + alpha) * a) true ++ out2)) := by
  let S₀ := contents ell width1 z d alpha a out1 [] out2
  let S₁ := contents ell width1 z d alpha a (List.replicate (ell * width1) true ++ out1) [] out2
  let S₂ := contents ell width1 z d alpha a (List.replicate (ell * width1) true ++ out1)
    (List.replicate (z * d + alpha) true) out2
  let S₃ := contents ell width1 z d alpha a (List.replicate (ell * width1) true ++ out1)
    (List.replicate (z * d + alpha) true)
    (List.replicate ((z * d + alpha) * a) true ++ out2)
  obtain ⟨t₀, ht₀, h₀⟩ := phase_run 0 ell width1 0 s S₀ (by intro k; fin_cases k <;> rfl)
  have e₀ : Function.update S₀ (slots 0 5)
      (List.replicate (ell * width1 + 0) true ++ S₀ (slots 0 5)) = S₁ := by
    funext k; fin_cases k <;> rfl
  rw [e₀] at h₀
  obtain ⟨t₁, ht₁, h₁⟩ := phase_run 1 z d alpha false S₁ (by intro k; fin_cases k <;> rfl)
  have e₁ : Function.update S₁ (slots 1 5)
      (List.replicate (z * d + alpha) true ++ S₁ (slots 1 5)) = S₂ := by
    funext k; fin_cases k <;> simp [S₁, S₂, contents, slots, Function.update]
  rw [e₁] at h₁
  obtain ⟨t₂, ht₂, h₂⟩ := phase_run 2 (z * d + alpha) a 0 false S₂
    (by intro k; fin_cases k <;> rfl)
  have e₂ : Function.update S₂ (slots 2 5)
      (List.replicate ((z * d + alpha) * a + 0) true ++ S₂ (slots 2 5)) = S₃ := by
    funext k; fin_cases k <;> rfl
  rw [e₂] at h₂
  refine ⟨t₀ + t₁ + t₂, by unfold bound; omega, ?_⟩
  exact (run_add ((run_add h₀ t₁).trans h₁) t₂).trans h₂

theorem bound_polynomial (ell width1 z d alpha a : ℕ) :
    bound ell width1 z d alpha a ≤ 24 * (ell + width1 + z + d + alpha + a + 1) ^ 3 := by
  unfold bound MatrixAddressMachine.exactTime
  ring_nf
  omega

end EthInapproximability.CurrentPaper.MatrixTemplateAddressSetup
