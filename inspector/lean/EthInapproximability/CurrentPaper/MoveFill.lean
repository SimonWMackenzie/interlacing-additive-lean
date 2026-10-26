import EthInapproximability.CurrentPaper.MultiMove

/-!
# Move lists: closed-form exit bank and exact cost

Lane owner:b-stage4-entry-program-4 (Paper B, unit 2, map item 3, segment 2).

A move job `(s, ds)` is the `MultiMove` job `⟨s, ds⟩`: the source word is
moved onto every destination and the source is left blank (`ds = []` is a
charged clear). Under syntactic side conditions (sources pairwise distinct
and no source a destination, all destination lists together duplicate-free,
the temporary none of them) and blank destinations, the exit bank is the
closed form `mfill` and the cost is the sum of `2 * |source| + 2`.
-/

namespace EthInapproximability.CurrentPaper.MoveFill

open MultiMove BitMachineBroadcast

variable {K : Type*} [DecidableEq K]

def toJob (j : K × List K) : Job K := ⟨j.1, j.2⟩

def mfill : List (K × List K) → (K → List Bool) → K → List Bool
  | [], S, k => S k
  | j :: js, S, k => if k ∈ j.2 then S j.1 else if k = j.1 then [] else mfill js S k

def mfillCost (jobs : List (K × List K)) (S : K → List Bool) : ℕ :=
  (jobs.map (fun j => 2 * (S j.1).length + 2)).sum

structure Good (temp : K) (jobs : List (K × List K)) : Prop where
  src_nodup : (jobs.map (·.1)).Nodup
  src_not_dst : ∀ j ∈ jobs, ∀ i ∈ jobs, j.1 ∉ i.2
  dst_nodup : (jobs.flatMap (·.2)).Nodup
  src_temp : ∀ j ∈ jobs, j.1 ≠ temp
  temp_dst : ∀ j ∈ jobs, temp ∉ j.2

omit [DecidableEq K] in
theorem Good.tail {temp : K} {j : K × List K} {js : List (K × List K)}
    (h : Good temp (j :: js)) : Good temp js where
  src_nodup := by
    have := h.src_nodup
    simp only [List.map_cons, List.nodup_cons] at this
    exact this.2
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
  exact ⟨h.src_temp j hj, h.temp_dst j hj, (List.nodup_flatMap.mp h.dst_nodup).1 j hj⟩

theorem step_off (j : K × List K) (S : K → List Bool) (c : K) (hc : c ∉ j.2)
    (hs : c ≠ j.1) : step (toJob j) S c = S c := by
  simp [step, toJob, prepend, hc, Function.update_of_ne hs]

theorem step_src (j : K × List K) (S : K → List Bool) (hsc : j.1 ∉ j.2) :
    step (toJob j) S j.1 = [] := by
  simp [step, toJob, prepend, hsc]

theorem step_on (j : K × List K) (S : K → List Bool) (c : K) (hc : c ∈ j.2)
    (hsc : j.1 ∉ j.2) : step (toJob j) S c = S j.1 ++ S c := by
  have hs : c ≠ j.1 := fun e => hsc (e ▸ hc)
  simp [step, toJob, prepend, hc, Function.update_of_ne hs]

theorem mfill_off (js : List (K × List K)) (S : K → List Bool) (k : K)
    (hk : ∀ i ∈ js, k ∉ i.2 ∧ k ≠ i.1) : mfill js S k = S k := by
  induction js with
  | nil => rfl
  | cons i is ih =>
      simp only [mfill, (hk i List.mem_cons_self).1, (hk i List.mem_cons_self).2, if_false]
      exact ih (fun a ha => hk a (List.mem_cons_of_mem _ ha))

theorem mfill_congr (js : List (K × List K)) (S T : K → List Bool) (k : K)
    (hk : S k = T k) (hs : ∀ i ∈ js, S i.1 = T i.1) : mfill js S k = mfill js T k := by
  induction js with
  | nil => exact hk
  | cons i is ih =>
      simp only [mfill]
      split_ifs
      · exact hs i List.mem_cons_self
      · rfl
      · exact ih (fun a ha => hs a (List.mem_cons_of_mem _ ha))

theorem apply_eq_mfill (temp : K) : ∀ (jobs : List (K × List K)), Good temp jobs →
    ∀ (S : K → List Bool), (∀ j ∈ jobs, ∀ d ∈ j.2, S d = []) →
      apply (jobs.map toJob) S = mfill jobs S ∧ cost (jobs.map toJob) S = mfillCost jobs S
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
      have hsn := hg.src_nodup
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hsn
      have hsrc_ne : ∀ i ∈ js, i.1 ≠ j.1 := fun i hi e => hsn.1 ⟨i, hi, e⟩
      have hsrc_dst : ∀ i ∈ js, i.1 ∉ j.2 := fun i hi =>
        hg.src_not_dst i (List.mem_cons_of_mem _ hi) j List.mem_cons_self
      have hdst_src : ∀ d ∈ j.2, ∀ i ∈ js, d ≠ i.1 := fun d hd i hi e =>
        hsrc_dst i hi (e ▸ hd)
      have hb' : ∀ i ∈ js, ∀ d ∈ i.2, step (toJob j) S d = [] := by
        intro i hi d hd
        have hoff : d ∉ j.2 := fun h => hdisj d h i hi hd
        have hns : d ≠ j.1 := fun e =>
          hg.src_not_dst j List.mem_cons_self i (List.mem_cons_of_mem _ hi) (e ▸ hd)
        rw [step_off j S d hoff hns]
        exact hb i (List.mem_cons_of_mem _ hi) d hd
      obtain ⟨ih1, ih2⟩ := apply_eq_mfill temp js hgt (step (toJob j) S) hb'
      have hsrc : ∀ i ∈ js, step (toJob j) S i.1 = S i.1 := fun i hi =>
        step_off j S i.1 (hsrc_dst i hi) (hsrc_ne i hi)
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, apply]
        rw [ih1]
        funext k
        simp only [mfill]
        split_ifs with hk hk2
        · rw [mfill_off js _ k (fun i hi => ⟨hdisj k hk i hi, hdst_src k hk i hi⟩),
            step_on j S k hk hsj, hb j List.mem_cons_self k hk, List.append_nil]
        · subst hk2
          rw [mfill_off js _ j.1 (fun i hi => ⟨hg.src_not_dst j List.mem_cons_self i
              (List.mem_cons_of_mem _ hi), fun e => hsrc_ne i hi e.symm⟩),
            step_src j S hsj]
        · exact (mfill_congr js S _ k (step_off j S k hk hk2).symm
            (fun i hi => (hsrc i hi).symm)).symm
      · simp only [List.map_cons, cost]
        rw [ih2]
        simp only [mfillCost, List.map_cons, List.sum_cons, toJob]
        congr 1
        congr 1
        apply List.map_congr_left
        intro i hi
        exact congrArg (fun l : List Bool => 2 * l.length + 2) (hsrc i hi)

theorem run (temp : K) (jobs : List (K × List K)) (hg : Good temp jobs)
    (S : K → List Bool) (hS : S temp = []) (hb : ∀ j ∈ jobs, ∀ d ∈ j.2, S d = []) :
    ((BitMachineEncoding.advance (program (jobs.map toJob) temp))^[mfillCost jobs S + 1])
      (⟨some (startLabel (jobs.map toJob)), initial, S⟩ :
        Turing.TM2.Cfg (fun _ : K => Bool) (Label (jobs.map toJob).length) Control) =
      ⟨none, initial, mfill jobs S⟩ := by
  obtain ⟨h1, h2⟩ := apply_eq_mfill temp jobs hg S hb
  have h := MultiMove.run (jobs.map toJob) temp hg.valid S hS
  rw [h1, h2] at h
  exact h

#print axioms apply_eq_mfill
#print axioms run

end EthInapproximability.CurrentPaper.MoveFill
