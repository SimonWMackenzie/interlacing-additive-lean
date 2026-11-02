import CurrentAdditive.EdgeIndexFacts
import CurrentAdditive.ScanDecodeDependency

/-! A fixed physical decoder for current edge-only numeric coordinates.
There is no incidence tag and no division by three. The source input and
item group in the frame cell are preserved. -/

namespace CurrentAdditive.LiteralEdgeDecodeMachine

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open LiteralEdgeDecodeDependency (K u dv div_phase)
open BitMachineRawSequence (leftLabel)

def placement₁ : Fin 6 ↪ K :=
  ⟨![0, 1, 9, 11, 4, 10], by decide⟩

def placement₂ : Fin 6 ↪ K :=
  ⟨![4, 2, 9, 8, 7, 10], by decide⟩

def initialBank (a r m ig : ℕ) : K → List Bool :=
  ![u a, u r, u m, [], [], [], [], [], [], [], [], [], u ig, []]

def middleBank (a r m ig : ℕ) : K → List Bool :=
  ![[], u r, u m, [], u (a / r), [], [], [], [], [], [], u (a % r), u ig, []]

def finalBank (a r m ig : ℕ) : K → List Bool :=
  ![[], u r, u m, [], [], [], [], u (a / r / m), u (a / r % m),
    [], [], u (a % r), u ig, []]

def program := BitMachineRawSequence.program
  (dv placement₁) (dv placement₂) .start false false

def clock (a r m : ℕ) :=
  MatrixUnaryDivision.totalTime a r +
    MatrixUnaryDivision.totalTime (a / r) m + 1

theorem clock_le (a r m : ℕ) : clock a r m ≤ 16*a + 3*r + 3*m + 19 := by
  have h₁ := MatrixUnaryDivision.totalTime_bound a r
  have h₂ := MatrixUnaryDivision.totalTime_bound (a / r) m
  have h₃ := Nat.div_le_self a r
  unfold clock
  omega

theorem first_run (a r m ig : ℕ) :
    ((advance (dv placement₁))^[MatrixUnaryDivision.totalTime a r])
      (⟨some .start, false, initialBank a r m ig⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, false, middleBank a r m ig⟩ := by
  rw [div_phase placement₁ (initialBank a r m ig) a r rfl rfl rfl rfl rfl rfl]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem second_run (a r m ig : ℕ) :
    ((advance (dv placement₂))^[MatrixUnaryDivision.totalTime (a / r) m])
      (⟨some .start, false, middleBank a r m ig⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, false, finalBank a r m ig⟩ := by
  rw [div_phase placement₂ (middleBank a r m ig) (a / r) m rfl rfl rfl rfl rfl rfl]
  congr 1
  funext j
  fin_cases j <;> rfl

/-- Both divisors may be zero. Every bank cell and step is accounted for. -/
theorem decode_run (a r m ig : ℕ) :
    ∃ t ≤ clock a r m,
      ((advance program)^[t])
        (⟨some (leftLabel .start), (false, false), initialBank a r m ig⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, (false, false), finalBank a r m ig⟩ := by
  exact BitMachineRawSequence.runs (dv placement₁) (dv placement₂)
    .start .start false false false false
    (initialBank a r m ig) (middleBank a r m ig) (finalBank a r m ig)
    _ _ (first_run a r m ig) (second_run a r m ig)

/-- On the actual public number of an unpadded edge coordinate, the fixed
machine outputs precisely its group, edge-occurrence, and copy labels. -/
theorem decode_edge_run {s m r : ℕ} (g : Fin (4*s)) (e : Fin m)
    (rep : Fin r) (ig : ℕ) :
    let a := LiteralEdgeEncoder.coordinateNumber s m r (.inl (g,e),rep)
    ∃ t ≤ clock a.val r m,
      ((advance program)^[t])
        (⟨some (leftLabel .start), (false, false), initialBank a.val r m ig⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, (false, false),
          ![[], u r, u m, [], [], [], [], u g.val, u e.val,
            [], [], u rep.val, u ig, []]⟩ := by
  dsimp only
  obtain ⟨t, ht, hr⟩ := decode_run
    (LiteralEdgeEncoder.coordinateNumber s m r (.inl (g,e),rep)).val r m ig
  refine ⟨t, ht, hr.trans ?_⟩
  obtain ⟨hg, he, hrep⟩ := LiteralEdgeEncoder.coordinate_decode_edge g e rep
  simp only [finalBank, hg, he, hrep]

#print axioms first_run
#print axioms second_run
#print axioms decode_run
#print axioms clock_le
#print axioms decode_edge_run

end

end CurrentAdditive.LiteralEdgeDecodeMachine
