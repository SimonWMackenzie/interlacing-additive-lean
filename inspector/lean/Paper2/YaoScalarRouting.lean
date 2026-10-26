import Paper2.YaoSourceIdentity
import EthInapproximability.CurrentPaper.BitMachineCopy

/-! A five-phase physical copy controller from the output scalar bank to
the exact five scalar slots of `EntryCombined.cfg`. The full-tape source slot
is external and is not modified by this controller. -/

namespace Paper2.YaoEntryParameterJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

abbrev RouteStack (t lambda : ℕ) := PayloadStack t lambda ⊕ (Fin 13 ⊕ Unit)
abbrev RouteLabel := Fin 5 × BitMachineCopy.Label
abbrev RouteConfig (t lambda : ℕ) :=
  TM2.Cfg (fun _ : RouteStack t lambda => Bool) RouteLabel (Option Bool)

noncomputable def routeScalarSource (t lambda : ℕ) (phase : Fin 5) :
    PayloadStack t lambda :=
  ![.inl (selectorSlot t lambda 11), bCell t lambda,
    fresh t lambda 6, strideCell t lambda, hCell t lambda] phase

noncomputable def routeSource (t lambda : ℕ) (phase : Fin 5) : RouteStack t lambda :=
  .inl (routeScalarSource t lambda phase)

def routeTarget (t lambda : ℕ) (phase : Fin 5) : RouteStack t lambda :=
  .inr (.inl (![0,7,8,9,10] phase))

def routeScratch (t lambda : ℕ) : RouteStack t lambda := .inr (.inr ())

noncomputable def routeEmbed (t lambda : ℕ) (phase : Fin 5) :
    Fin 3 ↪ RouteStack t lambda where
  toFun := ![routeSource t lambda phase, routeTarget t lambda phase,
    routeScratch t lambda]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [routeSource,routeTarget,routeScratch]

def routeNext (phase : Fin 5) : Option RouteLabel :=
  if h : phase.val + 1 < 5 then some (⟨phase.val+1, by omega⟩,.scan) else none

noncomputable def routeProgram (t lambda : ℕ) (l : RouteLabel) :
    TM2.Stmt (fun _ : RouteStack t lambda => Bool) RouteLabel (Option Bool) :=
  BitMachineStackEmbedding.stmt (routeEmbed t lambda l.1)
    (fun k => (l.1,k)) id id (routeNext l.1) (BitMachineCopy.program l.2)

noncomputable def routeRun (t lambda n : ℕ) (c : RouteConfig t lambda) :=
  ((advance (routeProgram t lambda))^[n]) c

theorem route_phase (t lambda : ℕ) (phase : Fin 5)
    (S : RouteStack t lambda → List Bool) (bits : List Bool)
    (hsource : S (routeSource t lambda phase) = bits)
    (htarget : S (routeTarget t lambda phase) = [])
    (hscratch : S (routeScratch t lambda) = []) :
    ∃ steps ≤ 2*bits.length+2,
      routeRun t lambda steps ⟨some (phase,.scan),none,S⟩ =
        ⟨routeNext phase,none,
          Function.update S (routeTarget t lambda phase) bits⟩ := by
  let ι := routeEmbed t lambda phase
  let input := BitMachineCopy.cfg (some .scan) none bits [] []
  let output := BitMachineCopy.cfg none none bits bits []
  have hr : ((advance BitMachineCopy.program)^[2*bits.length+2]) input = output := by
    simpa only [input,output,List.append_nil] using
      BitMachineCopy.run_correct none bits []
  have hh : (((advance BitMachineCopy.program)^[2*bits.length+2]) input).l = none := by
    rw [hr]
    rfl
  obtain ⟨steps,hsteps,he⟩ := BitMachineStackEmbedding.outputs ι S
    (fun k => (phase,k)) id id (by intro x; rfl)
    (routeNext phase) BitMachineCopy.program
    (routeProgram t lambda) (by intro l; rfl)
    input (2*bits.length+2) hh
  rw [hr] at he
  have hbank : BitMachineStackEmbedding.bank ι S input.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [input,BitMachineCopy.cfg,
      BitMachineCopy.stackContents,ι,routeEmbed,
      hsource,htarget,hscratch]
  have hlocal : output.stk = Function.update input.stk 1 bits := by
    funext k
    fin_cases k <;> rfl
  have hfinish : BitMachineStackEmbedding.bank ι S output.stk =
      Function.update S (routeTarget t lambda phase) bits := by
    rw [hlocal,BitMachineStackEmbedding.bank_update,hbank]
    rfl
  refine ⟨steps,hsteps,?_⟩
  change routeRun t lambda steps
    ⟨some (phase,.scan),none,BitMachineStackEmbedding.bank ι S input.stk⟩ =
    ⟨routeNext phase,none,BitMachineStackEmbedding.bank ι S output.stk⟩ at he
  rw [hbank,hfinish] at he
  exact he

theorem route_source_ne_target (t lambda : ℕ) (i j : Fin 5) :
    routeSource t lambda i ≠ routeTarget t lambda j := by
  simp [routeSource,routeTarget]

theorem route_targets_injective (t lambda : ℕ) :
    Function.Injective (routeTarget t lambda) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [routeTarget]

theorem route_next_zero (t lambda : ℕ) :
    routeNext (0 : Fin 5) = some (1,.scan) := rfl
theorem route_next_one (t lambda : ℕ) :
    routeNext (1 : Fin 5) = some (2,.scan) := rfl
theorem route_next_two (t lambda : ℕ) :
    routeNext (2 : Fin 5) = some (3,.scan) := rfl
theorem route_next_three (t lambda : ℕ) :
    routeNext (3 : Fin 5) = some (4,.scan) := rfl
theorem route_next_four (t lambda : ℕ) :
    routeNext (4 : Fin 5) = none := rfl

theorem route_run_add (t lambda m n : ℕ) (c : RouteConfig t lambda) :
    routeRun t lambda (m+n) c =
      routeRun t lambda n (routeRun t lambda m c) := by
  rw [Nat.add_comm]
  exact Function.iterate_add_apply _ _ _ _

theorem route_all_five (t lambda : ℕ)
    (S : RouteStack t lambda → List Bool)
    (hempty : ∀ j : Fin 5, S (routeTarget t lambda j) = [])
    (hscratch : S (routeScratch t lambda) = []) :
    ∃ (n : ℕ),
      n ≤ ∑ j : Fin 5, (2*(S (routeSource t lambda j)).length+2) ∧
      let S₁ := Function.update S (routeTarget t lambda 0)
        (S (routeSource t lambda 0))
      let S₂ := Function.update S₁ (routeTarget t lambda 1)
        (S (routeSource t lambda 1))
      let S₃ := Function.update S₂ (routeTarget t lambda 2)
        (S (routeSource t lambda 2))
      let S₄ := Function.update S₃ (routeTarget t lambda 3)
        (S (routeSource t lambda 3))
      let S₅ := Function.update S₄ (routeTarget t lambda 4)
        (S (routeSource t lambda 4))
      routeRun t lambda n ⟨some (0,.scan),none,S⟩ = ⟨none,none,S₅⟩ := by
  let word (j : Fin 5) := S (routeSource t lambda j)
  let S₁ := Function.update S (routeTarget t lambda 0) (word 0)
  let S₂ := Function.update S₁ (routeTarget t lambda 1) (word 1)
  let S₃ := Function.update S₂ (routeTarget t lambda 2) (word 2)
  let S₄ := Function.update S₃ (routeTarget t lambda 3) (word 3)
  let S₅ := Function.update S₄ (routeTarget t lambda 4) (word 4)
  have hsource (i : Fin 5) :
      S₁ (routeSource t lambda i) = word i ∧
      S₂ (routeSource t lambda i) = word i ∧
      S₃ (routeSource t lambda i) = word i ∧
      S₄ (routeSource t lambda i) = word i := by
    have h0 (j : Fin 5) : routeTarget t lambda j ≠ routeSource t lambda i :=
      (route_source_ne_target t lambda i j).symm
    simp only [S₁,S₂,S₃,S₄,Function.update_of_ne (h0 0),
      Function.update_of_ne (h0 1),Function.update_of_ne (h0 2),
      Function.update_of_ne (h0 3)]
    exact ⟨rfl,rfl,rfl,rfl⟩
  have hscratch' :
      S₁ (routeScratch t lambda) = [] ∧
      S₂ (routeScratch t lambda) = [] ∧
      S₃ (routeScratch t lambda) = [] ∧
      S₄ (routeScratch t lambda) = [] := by
    have hn (j : Fin 5) : routeTarget t lambda j ≠ routeScratch t lambda := by
      simp [routeTarget,routeScratch]
    simp only [S₁,S₂,S₃,S₄,Function.update_of_ne (hn 0),
      Function.update_of_ne (hn 1),Function.update_of_ne (hn 2),
      Function.update_of_ne (hn 3)]
    exact ⟨hscratch,hscratch,hscratch,hscratch⟩
  have htarget :
      S₁ (routeTarget t lambda 1) = [] ∧
      S₂ (routeTarget t lambda 2) = [] ∧
      S₃ (routeTarget t lambda 3) = [] ∧
      S₄ (routeTarget t lambda 4) = [] := by
    simpa [S₁,S₂,S₃,S₄,routeTarget] using
      (show S (routeTarget t lambda 1) = [] ∧
        S (routeTarget t lambda 2) = [] ∧
        S (routeTarget t lambda 3) = [] ∧
        S (routeTarget t lambda 4) = [] from
        ⟨hempty 1,hempty 2,hempty 3,hempty 4⟩)
  obtain ⟨n₀,hn₀,hr₀⟩ := route_phase t lambda 0 S (word 0) rfl (hempty 0) hscratch
  obtain ⟨n₁,hn₁,hr₁⟩ := route_phase t lambda 1 S₁ (word 1)
    (hsource 1).1 htarget.1 hscratch'.1
  obtain ⟨n₂,hn₂,hr₂⟩ := route_phase t lambda 2 S₂ (word 2)
    (hsource 2).2.1 htarget.2.1 hscratch'.2.1
  obtain ⟨n₃,hn₃,hr₃⟩ := route_phase t lambda 3 S₃ (word 3)
    (hsource 3).2.2.1 htarget.2.2.1 hscratch'.2.2.1
  obtain ⟨n₄,hn₄,hr₄⟩ := route_phase t lambda 4 S₄ (word 4)
    (hsource 4).2.2.2 htarget.2.2.2 hscratch'.2.2.2
  refine ⟨n₀+n₁+n₂+n₃+n₄,?_,?_⟩
  · change n₀+n₁+n₂+n₃+n₄ ≤
      ∑ j : Fin 5, (2*(word j).length+2)
    simp only [Fin.sum_univ_five]
    omega
  · dsimp only
    rw [route_run_add,route_run_add,route_run_add,route_run_add]
    simp only [route_next_zero,route_next_one,route_next_two,
      route_next_three,route_next_four] at hr₀ hr₁ hr₂ hr₃ hr₄
    rw [hr₀,hr₁,hr₂,hr₃,hr₄]

#print axioms route_phase

end Paper2.YaoEntryParameterJoin
