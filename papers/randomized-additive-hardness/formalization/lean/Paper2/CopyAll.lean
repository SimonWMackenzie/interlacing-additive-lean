import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineInline

/-! Unit 3, segment (2) tool: ONE fixed program running a finite family of the
production copy programs `MatrixStage4ScalarPreparationOps.copyProgram (cps i)`,
`i : Fin N`, one after the other (each call inlined by the production
`BitMachineInline.stmt`; every handoff is one charged step). Exact exit bank
`done cps N T` (each destination cell receives its source word prepended, every
other cell unchanged) and the uniform clock `N * (2 * Lmax + 3) + 1` when every
source cell holds at most `Lmax` bits. -/

set_option maxHeartbeats 4000000

namespace Paper2.CopyAll

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

variable {K : Type*} [DecidableEq K]

abbrev Lab (N : ℕ) := Fin (N + 1) ⊕ (Fin N × BitMachineCopy.Label)

/-- Label `.inl i` (`i < N`): start copy `i`; `.inl N`: halt; `.inr (i, l)`: copy `i`
at local label `l`, whose halt continues at `.inl (i + 1)`. -/
def prog {N : ℕ} (cps : Fin N → (Fin 3 ↪ K)) :
    Lab N → TM2.Stmt (fun _ : K => Bool) (Lab N) (Option Bool)
  | .inl i => if h : i.val < N then
      load (fun _ => none) (goto (fun _ => .inr (⟨i.val, h⟩, BitMachineCopy.Label.scan)))
    else halt
  | .inr (i, l) => BitMachineInline.stmt (fun l' => (.inr (i, l') : Lab N)) id id
      (some (.inl ⟨i.val + 1, by omega⟩)) (copyProgram (cps i) l)

/-- The bank after the first `i` copies. -/
def done {N : ℕ} (cps : Fin N → (Fin 3 ↪ K)) : ℕ → (K → List Bool) → K → List Bool
  | 0, T => T
  | i + 1, T => if h : i < N then
      Function.update (done cps i T) (cps ⟨i, h⟩ 1) (T (cps ⟨i, h⟩ 0) ++ T (cps ⟨i, h⟩ 1))
    else done cps i T

theorem done_off {N : ℕ} (cps : Fin N → (Fin 3 ↪ K)) (T : K → List Bool) (a : K)
    (ha : ∀ j, cps j 1 ≠ a) (i : ℕ) : done cps i T a = T a := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [done]
    split_ifs with h
    · rw [Function.update_of_ne (Ne.symm (ha _)), ih]
    · exact ih

theorem done_at_lt {N : ℕ} (cps : Fin N → (Fin 3 ↪ K))
    (hdd : ∀ i j, cps i 1 = cps j 1 → i = j) (T : K → List Bool) (j : Fin N) (i : ℕ)
    (hi : i ≤ j.val) : done cps i T (cps j 1) = T (cps j 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [done]
    split_ifs with h
    · rw [Function.update_of_ne, ih (by omega)]
      intro e
      have := hdd _ _ e
      rw [this] at hi
      simp at hi
    · exact ih (by omega)

theorem done_at {N : ℕ} (cps : Fin N → (Fin 3 ↪ K))
    (hdd : ∀ i j, cps i 1 = cps j 1 → i = j) (T : K → List Bool) (j : Fin N) (i : ℕ)
    (hi : j.val < i) : done cps i T (cps j 1) = T (cps j 0) ++ T (cps j 1) := by
  induction i with
  | zero => omega
  | succ i ih =>
    simp only [done]
    split_ifs with h
    · by_cases hj : j.val = i
      · have : j = ⟨i, h⟩ := Fin.ext hj
        subst this
        rw [Function.update_self]
      · rw [Function.update_of_ne, ih (by omega)]
        intro e
        have := hdd _ _ e
        exact hj (by rw [this])
    · exact ih (by have := j.isLt; omega)

/-- The full exit bank at a destination cell. -/
theorem done_dst {N : ℕ} (cps : Fin N → (Fin 3 ↪ K))
    (hdd : ∀ i j, cps i 1 = cps j 1 → i = j) (T : K → List Bool) (j : Fin N) :
    done cps N T (cps j 1) = T (cps j 0) ++ T (cps j 1) :=
  done_at cps hdd T j N j.isLt

/-- Sources and scratch cells keep their entry value during the whole run. -/
theorem done_src {N : ℕ} (cps : Fin N → (Fin 3 ↪ K)) (T : K → List Bool)
    (a : K) (ha : ∀ j, cps j 1 ≠ a) (i : ℕ) : done cps i T a = T a := done_off cps T a ha i

theorem copy_step {N : ℕ} (cps : Fin N → (Fin 3 ↪ K)) (i : ℕ) (h : i < N)
    (S : K → List Bool) (hz : S (cps ⟨i, h⟩ 2) = []) (v : Option Bool) :
    ∃ t ≤ 2 * (S (cps ⟨i, h⟩ 0)).length + 2 + 1,
    ((advance (prog cps))^[t])
        (⟨some (.inl ⟨i, by omega⟩), v, S⟩ : TM2.Cfg (fun _ : K => Bool) (Lab N) (Option Bool)) =
      ⟨some (.inl ⟨i + 1, by omega⟩), none,
        Function.update S (cps ⟨i, h⟩ 1) (S (cps ⟨i, h⟩ 0) ++ S (cps ⟨i, h⟩ 1))⟩ := by
  have e0 : advance (prog cps)
      (⟨some (.inl ⟨i, by omega⟩), v, S⟩ : TM2.Cfg (fun _ : K => Bool) (Lab N) (Option Bool)) =
      ⟨some (.inr (⟨i, h⟩, BitMachineCopy.Label.scan)), none, S⟩ := by
    simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, prog, h]
  have hc := copy_run (cps ⟨i, h⟩) S hz
  have hh : (((advance (copyProgram (cps ⟨i, h⟩)))^[2 * (S (cps ⟨i, h⟩ 0)).length + 2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : K => Bool)
        BitMachineCopy.Label (Option Bool))).l = none := by rw [hc]
  obtain ⟨n, hn, hr⟩ := BitMachineInline.outputs (fun l' => (.inr (⟨i, h⟩, l') : Lab N))
    (id : Option Bool → Option Bool) id (fun _ => rfl) (some (.inl ⟨i + 1, by omega⟩))
    (copyProgram (cps ⟨i, h⟩)) (prog cps) (fun _ => rfl)
    (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : K => Bool) BitMachineCopy.Label (Option Bool))
    _ hh
  rw [hc] at hr
  refine ⟨n + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply, e0]
  exact hr

/-- All `N` copies: ONE run, exact exit bank, uniform clock. -/
theorem all_run {N : ℕ} (cps : Fin N → (Fin 3 ↪ K))
    (hsd : ∀ i j, cps i 0 ≠ cps j 1) (hzd : ∀ i j, cps i 2 ≠ cps j 1)
    (hdd : ∀ i j, cps i 1 = cps j 1 → i = j)
    (T : K → List Bool) (hz : ∀ i, T (cps i 2) = []) (Lmax : ℕ)
    (hL : ∀ i, (T (cps i 0)).length ≤ Lmax) (v : Option Bool) :
    ∃ t ≤ N * (2 * Lmax + 3) + 1, ∃ v',
      ((advance (prog cps))^[t])
          (⟨some (.inl ⟨0, by omega⟩), v, T⟩ : TM2.Cfg (fun _ : K => Bool) (Lab N) (Option Bool)) =
        ⟨none, v', done cps N T⟩ := by
  suffices H : ∀ m, m ≤ N → ∀ (v : Option Bool),
      ∃ t ≤ m * (2 * Lmax + 3) + 1, ∃ v',
        ((advance (prog cps))^[t])
            (⟨some (.inl ⟨N - m, by omega⟩), v, done cps (N - m) T⟩ :
              TM2.Cfg (fun _ : K => Bool) (Lab N) (Option Bool)) =
          ⟨none, v', done cps N T⟩ by
    have := H N le_rfl v
    simpa using this
  intro m
  induction m with
  | zero =>
    intro _ v
    refine ⟨1, by omega, v, ?_⟩
    have hlab : (⟨N - 0, by omega⟩ : Fin (N + 1)) = ⟨N, by omega⟩ := Fin.ext (by simp)
    rw [hlab, Nat.sub_zero, Function.iterate_one]
    simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, prog]
  | succ m ih =>
    intro hm v
    have hi : N - (m + 1) < N := by omega
    set i := N - (m + 1) with hidef
    have hsrc : done cps i T (cps ⟨i, hi⟩ 0) = T (cps ⟨i, hi⟩ 0) :=
      done_off cps T _ (fun j => (hsd _ j).symm) i
    have hdst : done cps i T (cps ⟨i, hi⟩ 1) = T (cps ⟨i, hi⟩ 1) :=
      done_at_lt cps hdd T ⟨i, hi⟩ i le_rfl
    have hzz : done cps i T (cps ⟨i, hi⟩ 2) = [] := by
      rw [done_off cps T _ (fun j => (hzd _ j).symm) i]; exact hz _
    obtain ⟨t1, ht1, e1⟩ := copy_step cps i hi (done cps i T) hzz v
    have hnext : Function.update (done cps i T) (cps ⟨i, hi⟩ 1)
        (done cps i T (cps ⟨i, hi⟩ 0) ++ done cps i T (cps ⟨i, hi⟩ 1)) = done cps (i + 1) T := by
      rw [hsrc, hdst]
      simp only [done, dif_pos hi]
    rw [hnext] at e1
    obtain ⟨t', ht', v', hr⟩ := ih (by omega) none
    have hlab : (⟨i + 1, by omega⟩ : Fin (N + 1)) = ⟨N - m, by omega⟩ :=
      Fin.ext (by simp [hidef]; omega)
    have hdone : done cps (i + 1) T = done cps (N - m) T := by
      rw [show i + 1 = N - m by omega]
    rw [hlab, hdone] at e1
    refine ⟨t' + t1, ?_, v', ?_⟩
    · have := hL ⟨i, hi⟩
      rw [hsrc] at ht1
      have : (m + 1) * (2 * Lmax + 3) + 1 = (2 * Lmax + 3) + (m * (2 * Lmax + 3) + 1) := by ring
      omega
    · rw [Function.iterate_add_apply, e1, hr]

end Paper2.CopyAll

#print axioms Paper2.CopyAll.done_off
#print axioms Paper2.CopyAll.done_dst
#print axioms Paper2.CopyAll.copy_step
#print axioms Paper2.CopyAll.all_run
