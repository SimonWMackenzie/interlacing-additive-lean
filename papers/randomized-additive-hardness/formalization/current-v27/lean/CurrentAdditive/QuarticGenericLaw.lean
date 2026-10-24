import Paper2.E6Join

/-!
A machine's pointwise split-output identity transfers its acceptance law to
an independently sampled constructor tape and estimator block.  This is
source-agnostic and can be instantiated with the literal v27 experiment.
-/

noncomputable section

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2
open Paper2.Unit4Shell.Definitions (uniformTape)

theorem output_law_of_split {τ : Type} [Fintype τ]
    (μ : Paper2.FiniteLaw τ) (bits : τ → List Bool) (r : ℕ)
    (hF : ∀ F : List Bool → Prop,
      μ.prob (fun a => F (bits a)) =
        (uniformTape r).prob (fun v => F (List.ofFn v)))
    (dec : List Bool → τ) (hdec : ∀ a, dec (bits a) = a)
    (L s R : ℕ) (hrL : r ≤ L) (hLR : L + s ≤ R)
    (out : (Fin R → Bool) → List Bool)
    (eval : τ → List Bool → List Bool)
    (hout : ∀ t, out t = eval (dec ((List.ofFn t).take r))
      (((List.ofFn t).drop L).take s))
    (E : List Bool → Prop) :
    (uniformTape R).prob (fun t => E (out t)) =
      (μ.prod (uniformTape s)).prob (fun y => E (eval y.1 (List.ofFn y.2))) := by
  have hsplit := Paper2.AEth5.split_law μ bits r hF dec hdec hrL hLR
    (fun y => E (eval y.1 (List.ofFn y.2)))
  rw [← hsplit]
  congr 1
  funext t
  rw [hout t]
  have hblock : (((List.ofFn t).drop L).take s).length = s := by
    rw [List.length_take, List.length_drop, List.length_ofFn]
    omega
  rw [Paper2.AEth5.ofFn_vecOf _ _ hblock]

#print axioms output_law_of_split

end Paper2.CurrentAdditive.QuarticClassEndpoint
