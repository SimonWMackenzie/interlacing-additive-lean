import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! A fixed finite list of physical source-preserving unary copies, sequenced
on one bank with `BitMachineRawSequence`. Every copy is the checked
`MatrixStage4ScalarPreparationOps.copyProgram`; every copy and handoff is
charged. The list is a fixed program parameter, never an input. -/

set_option maxHeartbeats 1000000

namespace Paper2.CopyList

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

variable {K : Type*} [DecidableEq K]

def Label : List (Fin 3 ↪ K) → Type
  | [] => Unit
  | _ :: xs => BitMachineRawSequence.Label BitMachineCopy.Label (Label xs)

def Control : List (Fin 3 ↪ K) → Type
  | [] => Unit
  | _ :: xs => Option Bool × Control xs

def first : (xs : List (Fin 3 ↪ K)) → Label xs
  | [] => ()
  | _ :: _ => BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan

def initialControl : (xs : List (Fin 3 ↪ K)) → Control xs
  | [] => ()
  | _ :: xs => (none, initialControl xs)

def program : (xs : List (Fin 3 ↪ K)) →
    Label xs → TM2.Stmt (fun _ : K => Bool) (Label xs) (Control xs)
  | [] => fun _ => .halt
  | x :: xs => BitMachineRawSequence.program
      (MatrixStage4ScalarPreparationOps.copyProgram x) (program xs)
      (first xs) none (initialControl xs)

/-- Sequential semantics: each copy prepends its source word to its target. -/
def apply (S : K → List Bool) : List (Fin 3 ↪ K) → K → List Bool
  | [] => S
  | x :: xs => apply (Function.update S (x 1) (S (x 0) ++ S (x 1))) xs

def cost (S : K → List Bool) : List (Fin 3 ↪ K) → Nat
  | [] => 1
  | x :: xs => (2 * (S (x 0)).length + 2) +
      cost (Function.update S (x 1) (S (x 0) ++ S (x 1))) xs + 1

theorem run (scr : K) : ∀ (xs : List (Fin 3 ↪ K)) (S : K → List Bool),
    S scr = [] → (∀ x ∈ xs, x 2 = scr) →
    ∃ t ≤ cost S xs,
      ((advance (program xs))^[t])
        (⟨some (first xs), initialControl xs, S⟩ :
          TM2.Cfg (fun _ : K => Bool) (Label xs) (Control xs)) =
        ⟨none, initialControl xs, apply S xs⟩
  | [], S, _, _ => ⟨1, le_rfl, rfl⟩
  | x :: xs, S, hS, hx => by
      have hx2 : x 2 = scr := hx x (List.mem_cons_self ..)
      have hcopy := MatrixStage4ScalarPreparationOps.copy_run x S
        (by rw [hx2]; exact hS)
      let S' := Function.update S (x 1) (S (x 0) ++ S (x 1))
      have h12 : x 1 ≠ scr := by
        rw [← hx2]
        intro h
        exact absurd (x.injective h) (by decide)
      have hS' : S' scr = [] := by
        simp only [S', Function.update_of_ne h12.symm]
        exact hS
      obtain ⟨t, ht, hr⟩ := run scr xs S' hS'
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
      obtain ⟨u, hu, hrun⟩ := BitMachineRawSequence.runs
        (MatrixStage4ScalarPreparationOps.copyProgram x) (program xs)
        BitMachineCopy.Label.scan (first xs) none none
        (initialControl xs) (initialControl xs)
        S S' (apply S' xs) (2 * (S (x 0)).length + 2) t hcopy hr
      refine ⟨u, ?_, ?_⟩
      · change u ≤ (2 * (S (x 0)).length + 2) + cost S' xs + 1
        omega
      · exact hrun

/-- Fresh targets: no target is any copy's source, targets are pairwise
distinct and initially empty. Then each target receives its source word
and every other cell is unchanged. -/
theorem apply_fresh : ∀ (xs : List (Fin 3 ↪ K)) (S : K → List Bool),
    (∀ x ∈ xs, ∀ y ∈ xs, y 1 ≠ x 0) →
    (xs.map (fun x => x 1)).Nodup →
    (∀ x ∈ xs, S (x 1) = []) →
    (∀ x ∈ xs, apply S xs (x 1) = S (x 0)) ∧
      (∀ j, (∀ x ∈ xs, x 1 ≠ j) → apply S xs j = S j)
  | [], S, _, _, _ => ⟨fun _ h => absurd h (List.not_mem_nil), fun _ _ => rfl⟩
  | x :: xs, S, hsrc, hnd, hempty => by
      let S' := Function.update S (x 1) (S (x 0) ++ S (x 1))
      have hx1 : S (x 1) = [] := hempty x (List.mem_cons_self ..)
      have hnd' : (xs.map (fun x => x 1)).Nodup := (List.nodup_cons.mp hnd).2
      have hnotin : ∀ y ∈ xs, y 1 ≠ x 1 := by
        intro y hy h
        apply (List.nodup_cons.mp hnd).1
        exact List.mem_map.mpr ⟨y, hy, h⟩
      have hS'y : ∀ y ∈ xs, S' (y 1) = S (y 1) := by
        intro y hy
        simp only [S', Function.update_of_ne (hnotin y hy)]
      obtain ⟨ih1, ih2⟩ := apply_fresh xs S'
        (fun a ha b hb => hsrc a (List.mem_cons_of_mem _ ha) b
          (List.mem_cons_of_mem _ hb)) hnd'
        (fun y hy => by
          rw [hS'y y hy]
          exact hempty y (List.mem_cons_of_mem _ hy))
      refine ⟨?_, ?_⟩
      · intro y hy
        change apply S' xs (y 1) = S (y 0)
        rcases List.mem_cons.mp hy with rfl | hy
        · rw [ih2 (y 1) (fun z hz => hnotin z hz)]
          simp only [S', Function.update_self, hx1, List.append_nil]
        · rw [ih1 y hy]
          have hne : y 0 ≠ x 1 := hsrc y (List.mem_cons_of_mem _ hy) x
            (List.mem_cons_self ..) |>.symm
          simp only [S', Function.update_of_ne hne]
      · intro j hj
        change apply S' xs j = S j
        rw [ih2 j (fun z hz => hj z (List.mem_cons_of_mem _ hz))]
        have hne : j ≠ x 1 := fun h => hj x (List.mem_cons_self ..) h.symm
        simp only [S', Function.update_of_ne hne]

/-- Under the fresh-target conditions the cost is the sum of the source
lengths, with a fixed per-copy overhead. -/
def freshCost (S : K → List Bool) : List (Fin 3 ↪ K) → Nat
  | [] => 1
  | x :: xs => (2 * (S (x 0)).length + 3) + freshCost S xs

theorem freshCost_update (c : K) (v : List Bool) :
    ∀ (xs : List (Fin 3 ↪ K)) (S : K → List Bool),
      (∀ y ∈ xs, y 0 ≠ c) →
      freshCost (Function.update S c v) xs = freshCost S xs
  | [], _, _ => rfl
  | y :: ys, S, h => by
      have hne : y 0 ≠ c := h y (List.mem_cons_self ..)
      simp only [freshCost, Function.update_of_ne hne,
        freshCost_update c v ys S (fun z hz => h z (List.mem_cons_of_mem _ hz))]

theorem cost_fresh : ∀ (xs : List (Fin 3 ↪ K)) (S : K → List Bool),
    (∀ x ∈ xs, ∀ y ∈ xs, y 1 ≠ x 0) →
    cost S xs = freshCost S xs
  | [], _, _ => rfl
  | x :: xs, S, hsrc => by
      have hrest := cost_fresh xs (Function.update S (x 1) (S (x 0) ++ S (x 1)))
        (fun a ha b hb => hsrc a (List.mem_cons_of_mem _ ha) b
          (List.mem_cons_of_mem _ hb))
      have hsame := freshCost_update (x 1) (S (x 0) ++ S (x 1)) xs S
        (fun y hy => (hsrc y (List.mem_cons_of_mem _ hy) x
          (List.mem_cons_self ..)).symm)
      simp only [cost, freshCost, hrest, hsame]
      omega

#print axioms run
#print axioms apply_fresh
#print axioms cost_fresh

end Paper2.CopyList
