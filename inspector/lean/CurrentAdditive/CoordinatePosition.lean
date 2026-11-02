import CurrentAdditive.CoordinateSelect

namespace CurrentAdditive.FiniteFieldCoordinate

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoLookup Paper2.YaoSourceCodec
open Paper2.UnaryFieldListParserScratch

noncomputable def selected (S : Stack → List Bool) (F : Fin 12 → List Bool) : Stack → List Bool :=
  bank selectorSlots (staged S) F

theorem selected_at_position (S : Stack → List Bool)
    (F : Fin 12 → List Bool) (k : Fin 13) :
    selected S F (positionSlots k) = staged S (positionSlots k) := by
  apply bank_outside
  fin_cases k <;> decide

theorem selected_digit (S : Stack → List Bool) (F : Fin 12 → List Bool) :
    selected S F 17 = F 8 := by
  simpa [selected, selectorSlots] using
    (bank_at selectorSlots (staged S) F (8 : Fin 12))

theorem selected_at_payload_fresh (S : Stack → List Bool)
    (F : Fin 12 → List Bool) (k : Fin 6)
    (hk : k = 0 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) :
    selected S F (payloadSlots k) = staged S (payloadSlots k) := by
  apply bank_outside
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide

def positionClock (t a vertex : ℕ) (body : List Bool) : ℕ :=
  (2 * body.length + 2) + (2 * a + 2) +
  (2 * arity t + 2) +
  (a * (2 * arity t + 3) + 1 +
    (arity t + 1)) +
  (2 * arity t + 2) +
  (2 * (a * arity t) +
    5 * body.length +
    arity t * (3 * vertex + 6) +
    arity t + 6) + 5

/-- The incidence scanner reads its four copied inputs; selector scratch is foreign. -/
theorem position_run40 {v e t : ℕ}
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (a : Fin (paddedEdgeCount e)) (vertex : Fin v)
    (S : Stack → List Bool) (F : Fin 12 → List Bool)
    (ha : S 3 = List.replicate a.val true)
    (hv : S 4 = List.replicate vertex.val true)
    (hbody : S 5 = tokens (List.ofFn (flatten edges)))
    (hK : S 6 = List.replicate (2 ^ t * 2 ^ t) true)
    (hblank : ∀ k : Stack, 7 ≤ k.val → S k = []) :
    ∃ steps ≤ positionClock t a.val vertex.val
        (tokens (List.ofFn (flatten edges))),
      ∃ c',
        ((advance (Paper2.YaoPositionFull.program positionSlots))^[steps])
          (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
            Paper2.YaoPositionFull.startControl, selected S F⟩ :
            TM2.Cfg (fun _ : Stack => Bool) _ _) =
          ⟨none, c', Function.update (selected S F) 29
            (List.replicate
              (position (le_paddedEdgeCount e) edges a vertex).val true)⟩ := by
  obtain ⟨h8,h10,h9,h21,h23,h20,h22,h33⟩ := staged_at_target S
  have h0 : (selected S F) (positionSlots 0) =
      tokens (List.ofFn (flatten edges)) := by
    rw [selected_at_position]
    simpa [positionSlots] using h20.trans hbody
  have h1 : (selected S F) (positionSlots 1) = List.replicate a.val true := by
    rw [selected_at_position]
    simpa [positionSlots] using h21.trans ha
  have h2 : (selected S F) (positionSlots 2) =
      List.replicate (arity t) true := by
    rw [selected_at_position]
    simpa [positionSlots, arity] using h22.trans hK
  have h3 : (selected S F) (positionSlots 3) =
      List.replicate vertex.val true := by
    rw [selected_at_position]
    simpa [positionSlots] using h23.trans hv
  have he : ∀ k : Fin 13, 4 ≤ k.val →
      (selected S F) (positionSlots k) = [] := by
    intro k hk
    rw [selected_at_position]
    fin_cases k <;> simp_all [positionSlots, staged, jobs,
      EthInapproximability.CurrentPaper.CopyFill.fill, hblank]
  obtain ⟨steps,ht,c',hr⟩ := physical_canonical_position
    positionSlots (selected S F) edges a vertex h0 h1 h2 h3 he
  refine ⟨steps, ?_, c', ?_⟩
  · simpa [positionClock] using ht
  · simpa [positionSlots] using hr

end CurrentAdditive.FiniteFieldCoordinate
