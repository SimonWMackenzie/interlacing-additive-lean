import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! A literal three-stack transducer inserts a zero before each block of K
input bits. K is a fixed machine parameter; neither unbounded counters nor
an assumed padded-output oracle occur in its finite control. -/

namespace CurrentAdditive.V38ZeroPad

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def next {K : ℕ} (p : Fin K) : Fin K :=
  ⟨(p.val + 1) % K, Nat.mod_lt _ (Nat.zero_lt_of_lt p.isLt)⟩

def padFrom {K : ℕ} : Fin K → List Bool → List Bool
  | _, [] => []
  | p, b :: bs => (if p.val = 0 then [false] else []) ++
      b :: padFrom (next p) bs

theorem padFrom_length_le {K : ℕ} (p : Fin K) (bits : List Bool) :
    (padFrom p bits).length ≤ 2 * bits.length := by
  induction bits generalizing p with
  | nil => simp [padFrom]
  | cons b bs ih =>
      simp only [padFrom, List.length_append, List.length_cons]
      split <;> simp only [List.length_singleton, List.length_nil] <;>
        have := ih (next p) <;> omega

inductive Stack where | source | work | output
  deriving DecidableEq, Fintype
inductive Label (K : ℕ) where | copy (p : Fin K) | reverse
  deriving DecidableEq, Fintype
abbrev Control := Option Bool
abbrev Config (K : ℕ) := TM2.Cfg (fun _ : Stack => Bool) (Label K) Control

def program (K : ℕ) : Label K → TM2.Stmt (fun _ : Stack => Bool) (Label K) Control
  | .copy p => pop .source (fun _ b => b)
      (branch Option.isSome
        (branch (fun _ => decide (p.val = 0))
          (push .work (fun _ => false)
            (push .work (fun s => s.getD false) (goto (fun _ => .copy (next p)))))
          (push .work (fun s => s.getD false) (goto (fun _ => .copy (next p)))))
        (goto (fun _ => .reverse)))
  | .reverse => pop .work (fun _ b => b)
      (branch Option.isSome
        (push .output (fun s => s.getD false) (goto (fun _ => .reverse)))
        (load (fun _ => none) halt))

def cfg {K : ℕ} (l : Option (Label K)) (s : Control)
    (bits work out : List Bool) : Config K :=
  ⟨l, s, fun k => match k with
    | .source => bits | .work => work | .output => out⟩

def run (K t : ℕ) (q : Config K) : Config K :=
  ((advance (program K))^[t]) q

theorem run_add (K t u : ℕ) (q : Config K) :
    run K (t + u) q = run K u (run K t q) := by
  rw [Nat.add_comm t u]
  exact Function.iterate_add_apply _ _ _ _

theorem run_succ {K : ℕ} {c e : Config K}
    (h : TM2.step (program K) c = some e) (t : ℕ) :
    run K (t + 1) c = run K t e := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

theorem step_copy_nil {K : ℕ} (p : Fin K) (s : Control)
    (work out : List Bool) :
    TM2.step (program K) (cfg (some (.copy p)) s [] work out) =
      some (cfg (some .reverse) none [] work out) := by
  simp only [TM2.step, TM2.stepAux, program, cfg, List.head?_nil,
    List.tail_nil, Option.isSome_none, Bool.cond_false]
  congr 1
  apply congrArg (fun S => (⟨some Label.reverse, none, S⟩ : Config K))
  funext k
  cases k <;> simp

theorem step_copy_cons {K : ℕ} (p : Fin K) (s : Control)
    (b : Bool) (bits work out : List Bool) :
    TM2.step (program K) (cfg (some (.copy p)) s (b :: bits) work out) =
      some (cfg (some (.copy (next p))) (some b) bits
        (b :: ((if p.val = 0 then [false] else []) ++ work)) out) := by
  by_cases hp : p.val = 0
  all_goals
    simp [TM2.step, TM2.stepAux, program, cfg, hp]
    congr 1
    funext k
    cases k <;> simp

theorem copy_run {K : ℕ} (p : Fin K) (s : Control)
    (bits work out : List Bool) :
    ∃ v : Control,
      run K (bits.length + 1) (cfg (some (.copy p)) s bits work out) =
        cfg (some .reverse) v [] ((padFrom p bits).reverse ++ work) out := by
  induction bits generalizing p s work with
  | nil =>
      exact ⟨none, by simpa [padFrom] using run_succ (step_copy_nil p s work out) 0⟩
  | cons b bs ih =>
      obtain ⟨v, hv⟩ := ih (next p) (some b)
        (b :: ((if p.val = 0 then [false] else []) ++ work))
      refine ⟨v, ?_⟩
      rw [List.length_cons, run_succ (step_copy_cons p s b bs work out)]
      by_cases hp : p.val = 0 <;>
        simpa [padFrom, hp, List.reverse_append, List.append_assoc] using hv

theorem step_reverse_cons {K : ℕ} (s : Control) (b : Bool)
    (bits work out : List Bool) :
    TM2.step (program K) (cfg (some .reverse) s bits (b :: work) out) =
      some (cfg (some .reverse) (some b) bits work (b :: out)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  congr 1
  funext k
  cases k <;> simp

theorem step_reverse_nil {K : ℕ} (s : Control) (bits out : List Bool) :
    TM2.step (program K) (cfg (some .reverse) s bits [] out) =
      some (cfg none none bits [] out) := by
  simp only [TM2.step, TM2.stepAux, program, cfg, List.head?_nil,
    List.tail_nil, Option.isSome_none, Bool.cond_false]
  congr 1
  apply congrArg (fun S => (⟨none, none, S⟩ : Config K))
  funext k
  cases k <;> simp

theorem reverse_run {K : ℕ} (s : Control) (bits work out : List Bool) :
    run K (work.length + 1) (cfg (some .reverse) s bits work out) =
      cfg none none bits [] (work.reverse ++ out) := by
  induction work generalizing s out with
  | nil => simpa using run_succ (step_reverse_nil (K := K) s bits out) 0
  | cons b bs ih =>
      rw [List.length_cons, run_succ (step_reverse_cons s b bits bs out)]
      simpa [List.reverse_cons, List.append_assoc] using ih (some b) (b :: out)

theorem pad_run {K : ℕ} (p : Fin K) (bits : List Bool) :
    ∃ steps ≤ 3 * bits.length + 2,
      run K steps (cfg (some (.copy p)) none bits [] []) =
        cfg none none [] [] (padFrom p bits) := by
  obtain ⟨v, hv⟩ := copy_run p none bits [] []
  simp only [List.append_nil] at hv
  refine ⟨bits.length + 1 + ((padFrom p bits).length + 1), ?_, ?_⟩
  · have := padFrom_length_le p bits
    omega
  · rw [run_add, hv]
    simpa using reverse_run v [] (padFrom p bits).reverse []

noncomputable def machine (K : ℕ) (hK : 0 < K) : BitMachine.Machine :=
  ofFinite Stack.source Stack.output (Label.copy ⟨0, hK⟩) none (program K)

theorem machine_outputs (K : ℕ) (hK : 0 < K) (bits : List Bool) :
    (machine K hK).OutputsWithin bits (padFrom ⟨0, hK⟩ bits)
      (3 * bits.length + 2) := by
  obtain ⟨n, hn, hr⟩ := pad_run (⟨0, hK⟩ : Fin K) bits
  have hi : rawInit Stack.source (Label.copy (⟨0, hK⟩ : Fin K)) none bits =
      cfg (some (.copy ⟨0, hK⟩)) none bits [] [] := by
    apply congrArg (fun S => (⟨some (Label.copy (⟨0, hK⟩ : Fin K)), none, S⟩ : Config K))
    funext k
    cases k <;> simp [rawInit, cfg]
  apply outputsWithin_of_raw_run Stack.source Stack.output
    (Label.copy ⟨0, hK⟩) none (program K) bits _ n _ hn
  · rw [hi]
    exact congrArg (fun c => c.l) hr
  · rw [hi]
    exact congrArg (fun c => c.stk .output) hr

theorem machine_polytime (K : ℕ) (hK : 0 < K) :
    BitMachine.Polytime (padFrom (⟨0, hK⟩ : Fin K)) := by
  refine ⟨machine K hK, 3, 1, fun bits => ?_⟩
  exact BitMachine.outputsWithin_mono _ (machine_outputs K hK bits) (by simp; omega)

#print axioms pad_run
#print axioms machine_outputs
#print axioms machine_polytime

end CurrentAdditive.V38ZeroPad
