import Paper2.RecursiveSamplingSeed
import Paper2.RecursiveLabelCodec

/-! First-order data for the actual finite-choice label generators.
The denotation is mathematical semantics, not a unit-cost interpreter. -/

namespace Paper2.GeneratorCode

open RecursiveSamplingProgram RecursiveLabelCodecScratch

inductive Code where
  | emit (bits : List Bool)
  | ticket (alphabet : Nat)
  | bit
  | append (left right : Code)
  | branch3 (alphabet firstCut secondCut : Nat) (first second third : Code)
  deriving DecidableEq, Repr

def concat (p q : Program (List Bool)) : Program (List Bool) :=
  Program.bind p (fun xs => Program.map (fun ys => xs ++ ys) q)

def meaning : Code → Program (List Bool)
  | .emit bits => .pure bits
  | .ticket 0 => .pure []
  | .ticket (n + 1) =>
      Program.map (finCodec (n + 1)).encode
        (Program.uniform (n + 1) (by omega))
  | .bit => Program.map boolCodec.encode RecursiveSamplingSeed.bit
  | .append left right => concat (meaning left) (meaning right)
  | .branch3 0 _ _ _ _ _ => .pure []
  | .branch3 (n + 1) a b first second third =>
      .draw (n + 1) (by omega) (fun i =>
        if i.val < a then meaning first
        else if i.val < b then meaning second else meaning third)

def copies (n : Nat) (c : Code) : Code :=
  match n with
  | 0 => .emit []
  | n + 1 => .append c (copies n c)

def nodes : Code → Nat
  | .emit _ | .ticket _ | .bit => 1
  | .append left right => 1 + nodes left + nodes right
  | .branch3 _ _ _ first second third =>
      1 + nodes first + nodes second + nodes third

theorem nodes_pos (c : Code) : 0 < nodes c := by
  cases c <;> simp [nodes]

theorem meaning_ticket (n : Nat) (hn : 0 < n) :
    meaning (.ticket n) =
      Program.map (finCodec n).encode (Program.uniform n hn) := by
  cases n with
  | zero => omega
  | succ n => rfl

theorem copies_nodes (n : Nat) (c : Code) :
    nodes (copies n c) = n * (nodes c + 1) + 1 := by
  induction n with
  | zero => simp [copies, nodes]
  | succ n ih => simp [copies, nodes, ih, Nat.add_mul]; omega

/-- An explicit stack of syntax trees and already-produced bits.
No field of this configuration is a function or a proof certificate. -/
structure State where
  todo : List Code
  output : List Bool
  deriving DecidableEq, Repr

def stackMeaning : List Code → Program (List Bool)
  | [] => .pure []
  | c :: cs => concat (meaning c) (stackMeaning cs)

def stateMeaning (s : State) : Program (List Bool) :=
  Program.map (fun bits => s.output ++ bits) (stackMeaning s.todo)

def weight (s : State) : Nat := (s.todo.map nodes).sum

/-- One deterministic administrative operation; draw requests are left at
the head of the explicit stack. Its actual bit-machine cost is not assumed. -/
def admin (s : State) : Option State :=
  match s.todo with
  | .emit bits :: cs => some ⟨cs, s.output ++ bits⟩
  | .append left right :: cs => some ⟨left :: right :: cs, s.output⟩
  | .ticket 0 :: cs => some ⟨cs, s.output⟩
  | .branch3 0 _ _ _ _ _ :: cs => some ⟨cs, s.output⟩
  | _ => none

theorem admin_weight_lt (s t : State) (h : admin s = some t) :
    weight t < weight s := by
  rcases s with ⟨todo, out⟩
  cases todo with
  | nil => simp [admin] at h
  | cons c cs =>
      cases c with
      | emit bits =>
          simp only [admin, Option.some.injEq] at h
          subst t
          simp [weight, nodes]
      | ticket n =>
          cases n with
          | zero =>
              simp only [admin, Option.some.injEq] at h
              subst t
              simp [weight, nodes]
          | succ n => simp [admin] at h
      | bit => simp [admin] at h
      | append left right =>
          simp only [admin, Option.some.injEq] at h
          subst t
          simp [weight, nodes]
          omega
      | branch3 n a b first second third =>
          cases n with
          | zero =>
              simp only [admin, Option.some.injEq] at h
              subst t
              simp [weight, nodes]
          | succ n => simp [admin] at h

def normalize (s : State) : State :=
  match h : admin s with
  | none => s
  | some t => normalize t
termination_by weight s
decreasing_by exact admin_weight_lt s t h

theorem normalize_ready (s : State) : admin (normalize s) = none := by
  induction s using normalize.induct with
  | case1 s h => rw [normalize]; split <;> simp_all
  | case2 s t h ih => rw [normalize]; split <;> simp_all

end Paper2.GeneratorCode
