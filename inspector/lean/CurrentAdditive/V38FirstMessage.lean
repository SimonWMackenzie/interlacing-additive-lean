import CurrentAdditive.V38RestrictionProfiles

/-!
The actual first message of an arbitrary-speaker deterministic protocol.
This is a private v38 building block. The two cases are exhaustive even when
the speaker depends on the transcript: at the root it is one or the other.
An empty child remains allowed; callers must establish positive mass before
using a lower bound there.
-/

namespace Paper2.V38SmallBlocks

open Workspace.Types.CommComplexity Workspace.Types.Protocol

variable {A B : Type*} [Fintype A] [Fintype B]

theorem firstMessage_split (F : A → B → Bool) (hpos : 1 ≤ D F) :
    (∃ a : A → Bool,
      ∀ b : Bool, D (fun (x : {x : A // a x = b}) (y : B) => F x.1 y) ≤ D F - 1) ∨
    (∃ b : B → Bool,
      ∀ t : Bool, D (fun (x : A) (y : {y : B // b y = t}) => F x y.1) ≤ D F - 1) := by
  classical
  obtain ⟨P, hcost, hcomp⟩ :=
    Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty F)
  cases P with
  | leaf z =>
      change 0 = D F at hcost
      omega
  | aNode a l r =>
      left
      refine ⟨a, ?_⟩
      intro b
      cases b with
      | false =>
          have hcalc : (Workspace.UpperBound.Protocol.comap
              (fun x : {x : A // a x = false} => x.1) id l).Computes
              (fun (x : {x : A // a x = false}) (y : B) => F x.1 y) := by
            intro x y
            have hh := hcomp x.1 y
            simpa [Workspace.UpperBound.Protocol.comap_eval,
              Protocol.eval, x.2] using hh
          have hle : D (fun (x : {x : A // a x = false}) (y : B) => F x.1 y) ≤
              l.cost := by
            apply Nat.sInf_le
            exact ⟨_, Workspace.UpperBound.Protocol.comap_cost .., hcalc⟩
          have hc : l.cost ≤ D F - 1 := by
            change 1 + max l.cost r.cost = D F at hcost
            omega
          exact hle.trans hc
      | true =>
          have hcalc : (Workspace.UpperBound.Protocol.comap
              (fun x : {x : A // a x = true} => x.1) id r).Computes
              (fun (x : {x : A // a x = true}) (y : B) => F x.1 y) := by
            intro x y
            have hh := hcomp x.1 y
            simpa [Workspace.UpperBound.Protocol.comap_eval,
              Protocol.eval, x.2] using hh
          have hle : D (fun (x : {x : A // a x = true}) (y : B) => F x.1 y) ≤
              r.cost := by
            apply Nat.sInf_le
            exact ⟨_, Workspace.UpperBound.Protocol.comap_cost .., hcalc⟩
          have hc : r.cost ≤ D F - 1 := by
            change 1 + max l.cost r.cost = D F at hcost
            omega
          exact hle.trans hc
  | bNode b l r =>
      right
      refine ⟨b, ?_⟩
      intro t
      cases t with
      | false =>
          have hcalc : (Workspace.UpperBound.Protocol.comap id
              (fun y : {y : B // b y = false} => y.1) l).Computes
              (fun (x : A) (y : {y : B // b y = false}) => F x y.1) := by
            intro x y
            have hh := hcomp x y.1
            simpa [Workspace.UpperBound.Protocol.comap_eval,
              Protocol.eval, y.2] using hh
          have hle : D (fun (x : A) (y : {y : B // b y = false}) => F x y.1) ≤
              l.cost := by
            apply Nat.sInf_le
            exact ⟨_, Workspace.UpperBound.Protocol.comap_cost .., hcalc⟩
          have hc : l.cost ≤ D F - 1 := by
            change 1 + max l.cost r.cost = D F at hcost
            omega
          exact hle.trans hc
      | true =>
          have hcalc : (Workspace.UpperBound.Protocol.comap id
              (fun y : {y : B // b y = true} => y.1) r).Computes
              (fun (x : A) (y : {y : B // b y = true}) => F x y.1) := by
            intro x y
            have hh := hcomp x y.1
            simpa [Workspace.UpperBound.Protocol.comap_eval,
              Protocol.eval, y.2] using hh
          have hle : D (fun (x : A) (y : {y : B // b y = true}) => F x y.1) ≤
              r.cost := by
            apply Nat.sInf_le
            exact ⟨_, Workspace.UpperBound.Protocol.comap_cost .., hcalc⟩
          have hc : r.cost ≤ D F - 1 := by
            change 1 + max l.cost r.cost = D F at hcost
            omega
          exact hle.trans hc

#print axioms firstMessage_split

end Paper2.V38SmallBlocks
