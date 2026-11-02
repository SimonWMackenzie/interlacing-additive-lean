import Paper2.SourceProjection

/-! v39 robustness.tex, res:alignment: at a final owner's actual residual
protocol, a near-full original source projection forces that owner to miss
strictly more than eta of its own source-copy law. Representatives are
chosen only inside the one actual retained tuple event. -/

namespace CurrentAdditive.V39OwnerSourceCost

open Paper2

variable {C A S I : Type*} [Fintype C] [Fintype A] [Fintype S]

def projection (decode : S → I → A) (Y : Set S) (i : I) : Set A :=
  {a | ∃ t ∈ Y, decode t i=a}

theorem owner_misses_source_mass
    (μ : FiniteLaw C) (ν : FiniteLaw A) (F : C → A → Bool)
    (decode : S → I → A) (Y : Set S) (R : Set (I × C)) (i : I)
    (P : Workspace.Types.Protocol.Protocol (I × C) S Bool) (η : ℝ) (H : ℕ)
    (hnearfull : ∀ (U : Set C) (V : Set A),
      1-η ≤ μ.prob (· ∈ U) → 1-η ≤ ν.prob (· ∈ V) →
      H ≤ Compression.restrictionD F U V)
    (hprojection : 1-η ≤ ν.prob (· ∈ projection decode Y i))
    (hcompute : ∀ c, (i,c) ∈ R → ∀ t ∈ Y, P.eval (i,c) t=F c (decode t i))
    (hbudget : P.cost < H) :
    η < 1-μ.prob (fun c => (i,c) ∈ R) := by
  classical
  by_contra! hn
  let U : Set C := {c | (i,c) ∈ R}
  let V := projection decode Y i
  have hU : 1-η ≤ μ.prob (· ∈ U) := by
    change 1-η ≤ μ.prob (fun c => (i,c) ∈ R)
    linarith
  have hlower := hnearfull U V hU hprojection
  let rep : V → S := fun a => Classical.choose a.property
  have hrep (a : V) : rep a ∈ Y ∧ decode (rep a) i=a.val :=
    Classical.choose_spec a.property
  let Q := Workspace.UpperBound.Protocol.comap
    (fun c : U => (i,c.val)) rep P
  have hQ : Q.Computes (fun (c : U) (a : V) => F c.val a.val) := by
    intro c a
    have h := hcompute c.val c.property (rep a) (hrep a).1
    simpa [Q, Workspace.UpperBound.Protocol.comap_eval, (hrep a).2] using h
  have hupper : Compression.restrictionD F U V ≤ Q.cost := Nat.sInf_le ⟨Q,rfl,hQ⟩
  have hcost : Q.cost=P.cost := Workspace.UpperBound.Protocol.comap_cost _ _ P
  omega

end CurrentAdditive.V39OwnerSourceCost

#print axioms CurrentAdditive.V39OwnerSourceCost.projection
#print axioms CurrentAdditive.V39OwnerSourceCost.owner_misses_source_mass
