import CurrentAdditive.IndexedIncomingRectangle

/-! Reindex original flattened selector coordinates by `Fin (w*q₂)` so the
proved conditioning and rare-boost theorems apply without changing labels. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2

private theorem dwise_reindex
    {I J Z S : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype Z] [Fintype S]
    (D : ℕ) (source : FiniteLaw S) (μ : FiniteLaw Z)
    (decode : S → J → Z) (e : I → J) (he : Function.Injective e)
    (hwise : IsDWise D source decode μ) :
    IsDWise D source (fun s i => decode s (e i)) μ := by
  classical
  intro u hu A
  let t : Finset J := u.image e
  let f : u → t := fun i =>
    ⟨e i.val, Finset.mem_image.mpr ⟨i.val, i.property, rfl⟩⟩
  have hf : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    exact he (congrArg Subtype.val h)
  have ht : t.card ≤ D := by
    rw [show t.card = u.card from Finset.card_image_of_injective u he]
    exact hu
  have h := hwise t ht (fun y : t → Z => A (fun i => y (f i)))
  have hpi := FiniteLaw.pi_prob_restrict (fun _ : t => μ) f hf A
  calc
    source.prob (fun s => A (fun i : u => decode s (e i.val))) =
        (FiniteLaw.pi (fun _ : t => μ)).prob
          (fun y => A (fun i => y (f i))) := by
      simpa only [f] using h
    _ = (FiniteLaw.pi (fun _ : u => μ)).prob A := by
      simpa only using hpi

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : Sources.InternalStreams src μI w)

def incomingCoord : Fin (w*q₂) ≃ Fin w × Fin q₂ :=
  (finProdFinEquiv : Fin w × Fin q₂ ≃ Fin (w*q₂)).symm

def incomingDecode (sel : streams.selectorStream.Label)
    (a : Fin (w*q₂)) : Fin q₁ × X :=
  src.inner.decode (streams.selectorStream.decode sel
    (incomingCoord (q₂ := q₂) (w := w) a).1)
    (incomingCoord (q₂ := q₂) (w := w) a).2

theorem incoming_fin_dwise :
    IsDWise D streams.selectorStream.law.toFiniteLaw
      (incomingDecode src streams)
      (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw) := by
  exact dwise_reindex D streams.selectorStream.law.toFiniteLaw
    (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
    (fun sel (p : Fin w × Fin q₂) =>
      src.inner.decode (streams.selectorStream.decode sel p.1) p.2)
    (incomingCoord (q₂ := q₂) (w := w))
    (incomingCoord (q₂ := q₂) (w := w)).injective
    (selector_flatten_dwise src streams)

#print axioms incoming_fin_dwise

end CurrentAdditive.DeterministicIndexedMatrix
