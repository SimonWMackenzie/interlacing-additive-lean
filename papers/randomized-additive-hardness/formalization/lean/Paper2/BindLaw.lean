import Paper2.BindEnvelope
import Paper2.AModelTape

/-!
# Exact law of two independent selected-tape blocks

The first block has A's exact monomial tape length. The remaining suffix is
independent and long enough for B on every possible A output. Its used prefix
is uniform even though its required length depends on A's output. This file
is probability algebra only; the raw-tape physical splitter is separate.
-/

noncomputable section

namespace Paper2.SelectedTape.Bind

open Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions

def mixedOutput (A B : Algorithm) (x first second : List Bool) : List Bool :=
  B.output (A.output x first)
    (second.take (B.tapeLength (A.output x first)))

theorem classifier_prefix_prob (A B : Algorithm) (x : List Bool)
    (first : Fin (A.tapeLength x) → Bool) (E : List Bool → Prop) :
    (uniformTape (suffixLength A B x.length)).prob
      (fun t => E (mixedOutput A B x (List.ofFn first) (List.ofFn t))) =
    B.prob (A.output x (List.ofFn first)) E := by
  let y := A.output x (List.ofFn first)
  have hlen : B.tapeLength y ≤ suffixLength A B x.length :=
    classifier_le_suffix A B x first
  simpa [mixedOutput, Algorithm.prob, y] using
    Paper2.AModel.uniformTape_take_prob hlen
      (fun second => E (B.output y second))

theorem mixture_prob (A B : Algorithm) (x : List Bool)
    (E : List Bool → Prop) :
    (uniformTape (outerLength A B x.length)).prob (fun t =>
      E (mixedOutput A B x
        ((List.ofFn t).take (A.tapeLength x))
        ((List.ofFn t).drop (A.tapeLength x)))) =
    ∑ first : Fin (A.tapeLength x) → Bool,
      (uniformTape (A.tapeLength x)).weight first *
        B.prob (A.output x (List.ofFn first)) E := by
  classical
  let ra := A.tapeLength x
  let rb := suffixLength A B x.length
  have hsum : ra + rb = outerLength A B x.length :=
    source_plus_suffix A B x.length
  calc
    _ = ((uniformTape ra).prod (uniformTape rb)).prob
        (fun p => E (mixedOutput A B x (List.ofFn p.1) (List.ofFn p.2))) := by
          rw [← hsum]
          exact Paper2.AModel.uniformTape_take_drop_prob ra rb
            (fun first second => E (mixedOutput A B x first second))
    _ = ∑ first : Fin ra → Bool,
        (uniformTape ra).weight first *
          (uniformTape rb).prob
            (fun second => E (mixedOutput A B x (List.ofFn first) (List.ofFn second))) :=
      FiniteLaw.prod_prob (uniformTape ra) (uniformTape rb)
        (fun first second => E (mixedOutput A B x (List.ofFn first) (List.ofFn second)))
    _ = ∑ first : Fin (A.tapeLength x) → Bool,
        (uniformTape (A.tapeLength x)).weight first *
          B.prob (A.output x (List.ofFn first)) E := by
      apply Finset.sum_congr rfl
      intro first _
      rw [classifier_prefix_prob A B x first E]

#print axioms classifier_prefix_prob
#print axioms mixture_prob

end Paper2.SelectedTape.Bind
