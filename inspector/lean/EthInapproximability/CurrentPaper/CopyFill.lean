import EthInapproximability.CurrentPaper.MultiMove

/-!
# Source-preserving copy lists: closed-form exit bank and exact cost

Lane owner:b-stage4-entry-program-4 (Paper B, unit 2, map item 3, segment 2).

A copy job `(s, ds)` is the `MultiMove` job `⟨s, s :: ds⟩`: the source word
is restored and every destination receives it. Under syntactic disjointness
(no source is a destination, all destination lists together duplicate-free,
the temporary is none of them) and blank destinations, the exit bank is the
closed form `fill` (each destination holds its source word, every other
cell unchanged) and the cost is the sum of `2 * |source| + 2`.
-/

namespace EthInapproximability.CurrentPaper.CopyFill

open MultiMove BitMachineBroadcast

variable {K : Type*} [DecidableEq K]

def toJob (j : K × List K) : Job K := ⟨j.1, j.1 :: j.2⟩

/-- Closed-form exit bank. -/
def fill : List (K × List K) → (K → List Bool) → K → List Bool
  | [], S, k => S k
  | j :: js, S, k => if k ∈ j.2 then S j.1 else fill js S k

def fillCost (jobs : List (K × List K)) (S : K → List Bool) : ℕ :=
  (jobs.map (fun j => 2 * (S j.1).length + 2)).sum

/-- The syntactic side conditions. -/
structure Good (temp : K) (jobs : List (K × List K)) : Prop where
  src_not_dst : ∀ j ∈ jobs, ∀ i ∈ jobs, j.1 ∉ i.2
  dst_nodup : (jobs.flatMap (·.2)).Nodup
  src_temp : ∀ j ∈ jobs, j.1 ≠ temp
  temp_dst : ∀ j ∈ jobs, temp ∉ j.2

omit [DecidableEq K] in
theorem Good.tail {temp : K} {j : K × List K} {js : List (K × List K)}
    (h : Good temp (j :: js)) : Good temp js where
  src_not_dst := fun a ha b hb =>
    h.src_not_dst a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
  dst_nodup := by
    have := h.dst_nodup
    simp only [List.flatMap_cons] at this
    exact (List.nodup_append.mp this).2.1
  src_temp := fun a ha => h.src_temp a (List.mem_cons_of_mem _ ha)
  temp_dst := fun a ha => h.temp_dst a (List.mem_cons_of_mem _ ha)

omit [DecidableEq K] in
theorem Good.valid {temp : K} {jobs : List (K × List K)} (h : Good temp jobs) :
    Valid temp (jobs.map toJob) := by
  intro J hJ
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hJ
  refine ⟨h.src_temp j hj, ?_, ?_⟩
  · simp only [toJob, List.mem_cons, not_or]
    exact ⟨fun e => h.src_temp j hj e.symm, h.temp_dst j hj⟩
  · simp only [toJob, List.nodup_cons]
    refine ⟨h.src_not_dst j hj j hj, ?_⟩
    exact (List.nodup_flatMap.mp h.dst_nodup).1 j hj

theorem step_off (j : K × List K) (S : K → List Bool) (c : K) (hc : c ∉ j.2) :
    step (toJob j) S c = S c := by
  simp only [step, toJob, prepend, List.mem_cons]
  by_cases hs : c = j.1
  · subst hs; simp
  · simp [hs, hc]

theorem step_on (j : K × List K) (S : K → List Bool) (c : K) (hc : c ∈ j.2)
    (hsc : j.1 ∉ j.2) :
    step (toJob j) S c = S j.1 ++ S c := by
  have hs : c ≠ j.1 := fun e => hsc (e ▸ hc)
  simp [step, toJob, prepend, hc, Function.update_of_ne hs]

theorem fill_off (js : List (K × List K)) (S : K → List Bool) (k : K)
    (hk : ∀ i ∈ js, k ∉ i.2) : fill js S k = S k := by
  induction js with
  | nil => rfl
  | cons i is ih =>
      simp only [fill, hk i List.mem_cons_self, if_false]
      exact ih (fun a ha => hk a (List.mem_cons_of_mem _ ha))

theorem fill_congr (js : List (K × List K)) (S T : K → List Bool) (k : K)
    (hk : S k = T k) (hs : ∀ i ∈ js, S i.1 = T i.1) : fill js S k = fill js T k := by
  induction js with
  | nil => exact hk
  | cons i is ih =>
      simp only [fill]
      split_ifs
      · exact hs i List.mem_cons_self
      · exact ih (fun a ha => hs a (List.mem_cons_of_mem _ ha))

theorem apply_eq_fill (temp : K) : ∀ (jobs : List (K × List K)), Good temp jobs →
    ∀ (S : K → List Bool), (∀ j ∈ jobs, ∀ d ∈ j.2, S d = []) →
      apply (jobs.map toJob) S = fill jobs S ∧ cost (jobs.map toJob) S = fillCost jobs S
  | [], _, S, _ => ⟨rfl, rfl⟩
  | j :: js, hg, S, hb => by
      have hgt := hg.tail
      have hsj : j.1 ∉ j.2 := hg.src_not_dst j List.mem_cons_self j List.mem_cons_self
      have hnd := hg.dst_nodup
      simp only [List.flatMap_cons] at hnd
      have hdisj : ∀ d ∈ j.2, ∀ i ∈ js, d ∉ i.2 := by
        intro d hd i hi hdi
        exact (List.nodup_append.mp hnd).2.2 d hd d
          (List.mem_flatMap.mpr ⟨i, hi, hdi⟩) rfl
      have hb' : ∀ i ∈ js, ∀ d ∈ i.2, step (toJob j) S d = [] := by
        intro i hi d hd
        have hoff : d ∉ j.2 := fun h => hdisj d h i hi hd
        rw [step_off j S d hoff]
        exact hb i (List.mem_cons_of_mem _ hi) d hd
      obtain ⟨ih1, ih2⟩ := apply_eq_fill temp js hgt (step (toJob j) S) hb'
      have hsrc : ∀ i ∈ js, step (toJob j) S i.1 = S i.1 := by
        intro i hi
        exact step_off j S i.1
          (hg.src_not_dst i (List.mem_cons_of_mem _ hi) j List.mem_cons_self)
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, apply]
        rw [ih1]
        funext k
        simp only [fill]
        split_ifs with hk
        · rw [fill_off js _ k (fun i hi => hdisj k hk i hi), step_on j S k hk hsj,
            hb j List.mem_cons_self k hk, List.append_nil]
        · exact (fill_congr js S _ k (step_off j S k hk).symm
            (fun i hi => (hsrc i hi).symm)).symm
      · simp only [List.map_cons, cost]
        rw [ih2]
        simp only [fillCost, List.map_cons, List.sum_cons, toJob]
        congr 1
        congr 1
        apply List.map_congr_left
        intro i hi
        exact congrArg (fun l : List Bool => 2 * l.length + 2) (hsrc i hi)

/-- The copy-list run: one fixed program, closed-form exit bank, exact cost. -/
theorem run (temp : K) (jobs : List (K × List K)) (hg : Good temp jobs)
    (S : K → List Bool) (hS : S temp = []) (hb : ∀ j ∈ jobs, ∀ d ∈ j.2, S d = []) :
    ((BitMachineEncoding.advance (program (jobs.map toJob) temp))^[fillCost jobs S + 1])
      (⟨some (startLabel (jobs.map toJob)), initial, S⟩ :
        Turing.TM2.Cfg (fun _ : K => Bool) (Label (jobs.map toJob).length) Control) =
      ⟨none, initial, fill jobs S⟩ := by
  obtain ⟨h1, h2⟩ := apply_eq_fill temp jobs hg S hb
  have h := MultiMove.run (jobs.map toJob) temp hg.valid S hS
  rw [h1, h2] at h
  exact h

#print axioms apply_eq_fill
#print axioms run

end EthInapproximability.CurrentPaper.CopyFill
