import EthInapproximability.CurrentPaper.BitMachineBroadcast

/-!
# A fixed list of charged word moves/copies on one bank

Lane owner:b-stage4-entry-program-4 (Paper B, unit 2, map item 3, segment 2).

ONE fixed program for a fixed (syntactic) list of jobs. Job `j` pops its
source cell `j.src` completely into a blank temporary cell (the admitted
`BitMachineBroadcast.scanStep`), then pops the temporary cell back, pushing
every bit onto every cell of the fixed list `j.tgts` (the admitted
`BitMachineBroadcast.restoreStep`). If `j.src ∈ j.tgts` the source word is
restored (a source-preserving copy); otherwise it is a move; `tgts = []` is
a charged clear. Every job costs exactly `2 * |word| + 2` steps, plus one
final halting step. Only the admitted `scan_run`/`restore_run` are used.
-/

namespace EthInapproximability.CurrentPaper.MultiMove

open Turing TM2.Stmt BitMachineEncoding BitMachineBroadcast

variable {K : Type*} [DecidableEq K]

/-- One job: source cell and the fixed list of target cells. -/
structure Job (K : Type*) where
  src : K
  tgts : List K

abbrev Label (n : ℕ) := Fin (n + 1) × Bool
abbrev Control := Unit × Option Bool

/-- The single fixed program: label `(i, false)` scans job `i`'s source,
`(i, true)` restores it onto the targets; label `(n, _)` halts. -/
def program (jobs : List (Job K)) (temp : K) :
    Label jobs.length → TM2.Stmt (fun _ : K => Bool) (Label jobs.length) Control
  | (i, false) =>
      if h : i.val < jobs.length then
        scanStep (jobs[i.val]'h).src temp (i, false) (i, true)
      else halt
  | (i, true) =>
      if h : i.val < jobs.length then
        restoreStep temp (jobs[i.val]'h).tgts (i, true) (⟨i.val + 1, by omega⟩, false)
      else halt

def startLabel (jobs : List (Job K)) : Label jobs.length := (0, false)
def initial : Control := ((), none)

/-- Effect of one job on the bank. -/
def step (j : Job K) (S : K → List Bool) : K → List Bool :=
  prepend j.tgts (S j.src) (Function.update S j.src [])

/-- Effect of the whole job list. -/
def apply : List (Job K) → (K → List Bool) → K → List Bool
  | [], S => S
  | j :: js, S => apply js (step j S)

/-- Exact number of steps of the job list (without the final halt). -/
def cost : List (Job K) → (K → List Bool) → ℕ
  | [], _ => 0
  | j :: js, S => (2 * (S j.src).length + 2) + cost js (step j S)

/-- Syntactic validity of a job list for the temporary cell. -/
def Valid (temp : K) (jobs : List (Job K)) : Prop :=
  ∀ j ∈ jobs, j.src ≠ temp ∧ temp ∉ j.tgts ∧ j.tgts.Nodup

theorem step_temp (temp : K) (j : Job K) (hj : j.src ≠ temp ∧ temp ∉ j.tgts ∧ j.tgts.Nodup)
    (S : K → List Bool) (hS : S temp = []) : step j S temp = [] := by
  simp only [step, prepend, hj.2.1, if_false]
  rw [Function.update_of_ne (Ne.symm hj.1)]
  exact hS

theorem apply_temp (temp : K) : ∀ (jobs : List (Job K)), Valid temp jobs →
    ∀ (S : K → List Bool), S temp = [] → apply jobs S temp = []
  | [], _, _, hS => hS
  | j :: js, hv, S, hS => by
      simp only [apply]
      exact apply_temp temp js (fun x hx => hv x (List.mem_cons_of_mem j hx)) _
        (step_temp temp j (hv j List.mem_cons_self) S hS)

theorem job_run (jobs : List (Job K)) (temp : K) (k : ℕ) (hk : k < jobs.length)
    (hj : (jobs[k]'hk).src ≠ temp ∧ temp ∉ (jobs[k]'hk).tgts ∧ (jobs[k]'hk).tgts.Nodup)
    (S : K → List Bool) (hS : S temp = []) :
    ((advance (program jobs temp))^[2 * (S (jobs[k]'hk).src).length + 2])
      (⟨some (⟨k, by omega⟩, false), ((), none), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label jobs.length) Control) =
      ⟨some (⟨k + 1, by omega⟩, false), ((), none), step (jobs[k]'hk) S⟩ := by
  set j := jobs[k]'hk with hjdef
  have hscan : program jobs temp (⟨k, by omega⟩, false) =
      scanStep j.src temp (⟨k, by omega⟩, false) (⟨k, by omega⟩, true) := by
    simp only [program, hk, dif_pos, hjdef]
  have hrest : program jobs temp (⟨k, by omega⟩, true) =
      restoreStep temp j.tgts (⟨k, by omega⟩, true) (⟨k + 1, by omega⟩, false) := by
    simp only [program, hk, dif_pos, hjdef]
  have hs := scan_run (program jobs temp) j.src temp hj.1 _ _ hscan () none
    (S j.src) [] S
  have hc : contents j.src temp S (S j.src) [] = S := by
    funext x
    by_cases hx : x = temp
    · subst hx; simp [contents, hS]
    · by_cases hy : x = j.src
      · subst hy; simp [contents, Function.update_of_ne hx]
      · simp [contents, Function.update_of_ne hx]
  rw [hc] at hs
  have hr := restore_run (program jobs temp) temp j.tgts hj.2.2 hj.2.1 _ _ hrest () none
    ((S j.src).reverse ++ []) (Function.update S j.src [])
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at hr hs
  have he := (run_add (program jobs temp) hs ((S j.src).length + 1)).trans hr
  have hfin : Function.update (prepend j.tgts (S j.src) (Function.update S j.src [])) temp [] =
      step j S := by
    funext x
    by_cases hx : x = temp
    · subst hx
      rw [Function.update_self]
      exact (step_temp x j hj S hS).symm
    · rw [Function.update_of_ne hx]
      rfl
  rw [hfin] at he
  have ht : (S j.src).length + 1 + ((S j.src).length + 1) = 2 * (S j.src).length + 2 := by
    omega
  rw [ht] at he
  exact he

theorem run_from (jobs : List (Job K)) (temp : K) (hv : Valid temp jobs) :
    ∀ (m k : ℕ) (hk : k + m = jobs.length) (S : K → List Bool), S temp = [] →
      ((advance (program jobs temp))^[cost (jobs.drop k) S])
        (⟨some (⟨k, by omega⟩, false), ((), none), S⟩ :
          TM2.Cfg (fun _ : K => Bool) (Label jobs.length) Control) =
        ⟨some (⟨jobs.length, by omega⟩, false), ((), none), apply (jobs.drop k) S⟩ := by
  intro m
  induction m with
  | zero =>
      intro k hk S _
      have hd : jobs.drop k = [] := List.drop_of_length_le (by omega)
      rw [hd]
      simp only [cost, apply, Function.iterate_zero, id]
      have : (⟨k, by omega⟩ : Fin (jobs.length + 1)) = ⟨jobs.length, by omega⟩ :=
        Fin.ext (by simp; omega)
      rw [this]
  | succ m ih =>
      intro k hk S hS
      have hlt : k < jobs.length := by omega
      have hd : jobs.drop k = jobs[k] :: jobs.drop (k + 1) := List.drop_eq_getElem_cons hlt
      have hj := hv (jobs[k]) (List.getElem_mem hlt)
      rw [hd]
      simp only [cost, apply]
      rw [Nat.add_comm, Function.iterate_add_apply, job_run jobs temp k hlt hj S hS]
      exact ih (k + 1) (by omega) _ (step_temp temp _ hj S hS)

/-- The whole fixed job list, then one halting step. -/
theorem run (jobs : List (Job K)) (temp : K) (hv : Valid temp jobs)
    (S : K → List Bool) (hS : S temp = []) :
    ((advance (program jobs temp))^[cost jobs S + 1])
      (⟨some (startLabel jobs), initial, S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label jobs.length) Control) =
      ⟨none, initial, apply jobs S⟩ := by
  have h := run_from jobs temp hv jobs.length 0 (by omega) S hS
  simp only [List.drop_zero] at h
  rw [Nat.add_comm, Function.iterate_add_apply]
  simp only [startLabel, initial]
  have h0 : ((0 : Fin (jobs.length + 1))) = ⟨0, by omega⟩ := rfl
  rw [h0, h]
  have hh : program jobs temp (⟨jobs.length, by omega⟩, false) = halt := by
    simp [program]
  simp [advance, TM2.step, hh, TM2.stepAux]

#print axioms step_temp
#print axioms apply_temp
#print axioms job_run
#print axioms run_from
#print axioms run

end EthInapproximability.CurrentPaper.MultiMove
