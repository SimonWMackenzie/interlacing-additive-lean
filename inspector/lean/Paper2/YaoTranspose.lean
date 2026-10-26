import Paper2.YaoModel

/-!
# Transposing strictly alternating protocols

Frozen v12 Section 7, final proof of `yao:bpp`: Bob-starting complexity
of the transposed table equals Alice-starting complexity of the original.
This is a concrete protocol symmetry, not a consequence of the hardness
result or of the one-bit starter comparison.
-/

namespace Paper2.Yao

open Workspace.Types.Protocol Workspace.Types.CommComplexity

variable {X Y : Type*}

theorem alternates_transpose (P : Protocol X Y Bool) (s : Turn)
    (h : Alternates s P) :
    Alternates s.other (Workspace.UpperBound.Protocol.transpose P) := by
  induction P generalizing s with
  | leaf b => cases s <;> trivial
  | aNode a l r ihl ihr =>
    cases s with
    | alice => exact ⟨ihl .bob h.1, ihr .bob h.2⟩
    | bob => exact h.elim
  | bNode b l r ihl ihr =>
    cases s with
    | alice => exact h.elim
    | bob => exact ⟨ihl .alice h.1, ihr .alice h.2⟩

namespace StrictProtocol

def transpose {s : Turn} (P : StrictProtocol X Y s) : StrictProtocol Y X s.other :=
  ⟨Workspace.UpperBound.Protocol.transpose P.toProtocol,
    alternates_transpose P.toProtocol s P.alternates⟩

theorem transpose_cost {s : Turn} (P : StrictProtocol X Y s) :
    P.transpose.cost = P.cost := Workspace.UpperBound.Protocol.transpose_cost _

theorem transpose_eval {s : Turn} (P : StrictProtocol X Y s) (y : Y) (x : X) :
    P.transpose.eval y x = P.eval x y :=
  Workspace.UpperBound.Protocol.transpose_eval _ y x

theorem transpose_computes {s : Turn} (P : StrictProtocol X Y s)
    (F : X → Y → Bool) (h : P.Computes F) :
    P.transpose.Computes (fun y x => F x y) := by
  intro y x
  rw [transpose_eval]
  exact h x y

end StrictProtocol

theorem Dalt_transpose_le [Fintype X] [Fintype Y]
    (s : Turn) (F : X → Y → Bool) :
    Dalt s.other (fun y x => F x y) ≤ Dalt s F := by
  obtain ⟨P, hp, hP⟩ := exists_optimal s F
  have h := Dalt_le_cost P.transpose (P.transpose_computes F hP)
  simpa only [StrictProtocol.transpose_cost, hp] using h

theorem Dalt_transpose [Fintype X] [Fintype Y]
    (s : Turn) (F : X → Y → Bool) :
    Dalt s.other (fun y x => F x y) = Dalt s F := by
  apply le_antisymm (Dalt_transpose_le s F)
  simpa using Dalt_transpose_le s.other (fun y x => F x y)

theorem Dfree_transpose [Fintype X] [Fintype Y] (F : X → Y → Bool) :
    Dfree (fun y x => F x y) = Dfree F := by
  have ha := Dalt_transpose .bob F
  have hb := Dalt_transpose .alice F
  simp only [Turn.other] at ha hb
  simp only [Dfree, ha, hb, min_comm]

end Paper2.Yao
