import Paper2.GeneratorCode
import Paper2.EncodedSamplerAlgebra
import Paper2.RecursiveSamplingCapped

/-! Operational correspondence for the explicit first-order generator stack.
These semantics do not claim a physical bit-machine implementation. -/
namespace Paper2.GeneratorCode

open RecursiveSamplingProgram RecursiveLabelCodecScratch

theorem concat_pure_left (xs : List Bool) (p : Program (List Bool)) :
    concat (.pure xs) p = Program.map (fun ys => xs ++ ys) p := rfl

theorem concat_pure_nil_right (p : Program (List Bool)) :
    concat p (.pure []) = p := by
  simp only [concat, Program.map_pure, List.append_nil]
  exact EncodedSamplerAlgebra.Program.bind_pure_right p

theorem concat_assoc (p q r : Program (List Bool)) :
    concat (concat p q) r = concat p (concat q r) := by
  simp only [concat, EncodedSamplerAlgebra.Program.bind_assoc,
    EncodedSamplerAlgebra.Program.bind_map, EncodedSamplerAlgebra.Program.map_bind,
    EncodedSamplerAlgebra.Program.map_map, Function.comp_def, List.append_assoc]

theorem prefix_concat (xs : List Bool) (p q : Program (List Bool)) :
    Program.map (fun ys => xs ++ ys) (concat p q) =
      concat (Program.map (fun ys => xs ++ ys) p) q := by
  simp only [concat, EncodedSamplerAlgebra.Program.map_bind,
    EncodedSamplerAlgebra.Program.bind_map, EncodedSamplerAlgebra.Program.map_map,
    Function.comp_def, List.append_assoc]

theorem admin_meaning (s t : State) (h : admin s = some t) :
    stateMeaning t = stateMeaning s := by
  rcases s with ⟨todo, out⟩
  cases todo with
  | nil => simp [admin] at h
  | cons c cs =>
      cases c with
      | emit bits =>
          simp only [admin, Option.some.injEq] at h
          subst t
          simp only [stateMeaning, stackMeaning, meaning, concat_pure_left,
            EncodedSamplerAlgebra.Program.map_map, Function.comp_def, List.append_assoc]
      | append left right =>
          simp only [admin, Option.some.injEq] at h
          subst t
          simp only [stateMeaning, stackMeaning, meaning, concat_assoc]
      | ticket n =>
          cases n with
          | zero =>
              simp only [admin, Option.some.injEq] at h
              subst t
              simp only [stateMeaning, stackMeaning, meaning, concat_pure_left,
                EncodedSamplerAlgebra.Program.map_map, Function.comp_def, List.nil_append]
          | succ n => simp [admin] at h
      | bit => simp [admin] at h
      | branch3 n a b first second third =>
          cases n with
          | zero =>
              simp only [admin, Option.some.injEq] at h
              subst t
              simp only [stateMeaning, stackMeaning, meaning, concat_pure_left,
                EncodedSamplerAlgebra.Program.map_map, Function.comp_def, List.nil_append]
          | succ n => simp [admin] at h

theorem normalize_meaning (s : State) : stateMeaning (normalize s) = stateMeaning s := by
  induction s using normalize.induct with
  | case1 s h => rw [normalize]; split <;> simp_all
  | case2 s t h ih =>
      rw [normalize]
      split
      · simp_all
      · rename_i t' ht
        have he : t' = t := Option.some.inj (ht.symm.trans h)
        subst t'
        exact ih.trans (admin_meaning s t h)

def administrativeSteps (s : State) : Nat :=
  match h : admin s with
  | none => 0
  | some t => administrativeSteps t + 1
termination_by weight s
decreasing_by exact admin_weight_lt s t h

theorem administrativeSteps_le (s : State) : administrativeSteps s ≤ weight s := by
  induction s using administrativeSteps.induct with
  | case1 s h => rw [administrativeSteps]; split <;> simp_all
  | case2 s t h ih =>
      rw [administrativeSteps]
      split
      · simp_all
      · rename_i t' ht
        have he : t' = t := Option.some.inj (ht.symm.trans h)
        subst t'
        have := admin_weight_lt s t h
        omega

/-- The next scalar request, read from explicit syntax. A finished state
retains the source interpreter's singleton padding request. -/
def request (s : State) : Nat :=
  match s.todo with
  | .ticket (n + 1) :: _ => n + 1
  | .bit :: _ => 2
  | .branch3 (n + 1) _ _ _ _ _ :: _ => n + 1
  | _ => 1

theorem request_pos (s : State) : 0 < request s := by
  rcases s with ⟨todo, out⟩
  cases todo with
  | nil => simp [request]
  | cons c cs =>
      cases c <;> simp only [request]
      all_goals first | omega | (split <;> omega)

/-- Advance by the supplied accepted ticket; this is a data update rather
than a function-valued continuation. Bounds are checked by the later bridge. -/
def advance (s : State) (i : Nat) : State :=
  match s.todo with
  | .ticket (n + 1) :: cs => ⟨cs, s.output ++ (List.replicate i true ++ [false])⟩
  | .bit :: cs => ⟨cs, s.output ++ [decide (i = 1)]⟩
  | .branch3 (n + 1) a b first second third :: cs =>
      ⟨(if i < a then first else if i < b then second else third) :: cs, s.output⟩
  | _ => s

theorem ready_request (s : State) (hr : admin s = none) :
    RecursiveSamplingCapped.denominator (stateMeaning s) = request s := by
  rcases s with ⟨todo, out⟩
  cases todo with
  | nil => rfl
  | cons c cs =>
      cases c with
      | emit bits => simp [admin] at hr
      | append left right => simp [admin] at hr
      | ticket n =>
          cases n with
          | zero => simp [admin] at hr
          | succ n => rfl
      | bit => rfl
      | branch3 n a b first second third =>
          cases n with
          | zero => simp [admin] at hr
          | succ n => rfl

theorem ready_step (s : State) (hr : admin s = none) (i : Fin (request s)) :
    stateMeaning (advance s i.val) =
      RecursiveSamplingCapped.step (stateMeaning s)
        ⟨i.val, by rw [ready_request s hr]; exact i.isLt⟩ := by
  rcases s with ⟨todo, out⟩
  cases todo with
  | nil => rfl
  | cons c cs =>
      cases c with
      | emit bits => simp [admin] at hr
      | append left right => simp [admin] at hr
      | ticket n =>
          cases n with
          | zero => simp [admin] at hr
          | succ n =>
              simp only [advance, stateMeaning, stackMeaning, meaning, concat,
                Program.uniform, Program.map_draw, Program.map_pure, Program.bind_draw,
                Program.bind_pure, RecursiveSamplingCapped.step,
                EncodedSamplerAlgebra.Program.map_map, Function.comp_def]
              simp [finCodec, List.append_assoc]
      | bit =>
          simp only [advance, stateMeaning, stackMeaning, meaning, concat,
            RecursiveSamplingSeed.bit, Program.uniform, Program.map_draw,
            Program.map_pure, Program.bind_draw, Program.bind_pure,
            RecursiveSamplingCapped.step, EncodedSamplerAlgebra.Program.map_map,
            Function.comp_def]
          simp [boolCodec, RecursiveSamplingSeed.bitEquiv, List.append_assoc]
      | branch3 n a b first second third =>
          cases n with
          | zero => simp [admin] at hr
          | succ n =>
              simp only [stateMeaning, stackMeaning, meaning, concat,
                Program.bind_draw, Program.map_draw, RecursiveSamplingCapped.step]
              by_cases ha : i.val < a
              · simp [advance, ha, stateMeaning, stackMeaning, concat]
              · by_cases hb : i.val < b
                · simp [advance, ha, hb, stateMeaning, stackMeaning, concat]
                · simp [advance, ha, hb, stateMeaning, stackMeaning, concat]

#print axioms admin_meaning
#print axioms normalize_meaning
#print axioms administrativeSteps_le
#print axioms ready_request
#print axioms ready_step

end Paper2.GeneratorCode
