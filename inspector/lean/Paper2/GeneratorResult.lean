import Paper2.GeneratorCapped

namespace Paper2.GeneratorCode

open RecursiveSamplingProgram

/-- Output is read from the data state only when its pending syntax is empty. -/
def readReady (s : State) : Option (List Bool) :=
  match s.todo with
  | [] => some s.output
  | _ => none

theorem ready_read (s : State) (hr : admin s = none) :
    readReady s = RecursiveSamplingCapped.readResult (stateMeaning s) := by
  rcases s with ⟨todo, out⟩
  cases todo with
  | nil => simp [readReady, stateMeaning, stackMeaning, RecursiveSamplingCapped.readResult]
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

def read (s : State) : Option (List Bool) := readReady (normalize s)

theorem read_eq (s : State) :
    read s = RecursiveSamplingCapped.readResult (stateMeaning s) := by
  rw [read, ready_read _ (normalize_ready s), normalize_meaning]

def run {M : Nat} (B R : Nat) (hMB : Nat.clog 2 M ≤ B)
    (N : Nat) (s : BoundedState M) (t : CappedSampler.Adaptive.Tape B R N) :
    Option (List Bool) := (capped B R hMB N s t).bind (fun u => read u.val)

theorem run_eq {M : Nat} (B R : Nat) (hMB : Nat.clog 2 M ≤ B)
    (N : Nat) (s : BoundedState M) (t : CappedSampler.Adaptive.Tape B R N) :
    run B R hMB N s t = RecursiveSamplingCapped.run B R hMB N (semantic s) t := by
  rw [run, RecursiveSamplingCapped.run, ← capped_semantic]
  cases hc : capped B R hMB N s t with
  | none => rfl
  | some u => exact read_eq u.val

def initial (c : Code) : State := ⟨[c], []⟩

theorem initial_meaning (c : Code) : stateMeaning (initial c) = meaning c := by
  simp only [initial, stateMeaning, stackMeaning, List.nil_append,
    concat_pure_nil_right]
  exact EncodedSamplerAlgebra.Program.map_id _

#print axioms ready_read
#print axioms read_eq
#print axioms run_eq
#print axioms initial_meaning

end Paper2.GeneratorCode
