import CurrentAdditive.GaussConcreteGridPolynomial
import CurrentAdditive.GaussCellPolynomialClock

namespace CurrentAdditive.GaussConcreteGridPolynomialBound
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

open GaussConcreteGridPolynomial
open GaussCellPolynomialClock
open EthInapproximability.CurrentPaper

attribute [local irreducible] GaussFetchedArithmetic.M
  GaussFixedArithmeticClock.coefficient GaussUniformMatrixRun.exponent
  GaussRequestGrowth64.requestPush GaussFetchPolynomial64.coefficient
  UnaryBinaryEncoding.coefficient

attribute [local irreducible] PolynomialBound

theorem invocation_polynomial (M : EthInapproximability.CurrentPaper.BitMachine.Machine)
    {f g : Nat → Nat → Nat} (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun s n => invocation M (f s n) (g s n)) := by
  simpa only [invocation,MinimumRatioContext.MachineInvokeFull.uniformBound,
    List.length_replicate] using uniform_invocation M hf hg

theorem frame_polynomial {f : Nat → Nat → Nat} (hf : PolynomialBound f) :
    PolynomialBound (fun s n => frame (f s n)) :=
  invocation_polynomial V2FieldContext.W hf
    (mul (constant _) (power (add hf (constant 1)) 2))

theorem header_polynomial : PolynomialBound (fun _ n => header n) :=
  add (add (invocation_polynomial GaussCountHeader.W second
    (mul (constant _) (power (add second (constant 1)) 2)))
    (add (mul (constant 2) second) (constant 1))) (constant 3)

theorem request_polynomial : PolynomialBound (fun _ n => request n) :=
  add (add (add (mul (constant _)
    (power (add (mul (constant 3) second) (constant 2)) 3))
    (add (mul (constant 2) second) (constant 5)))
    (mul (constant 2) packet_polynomial)) (constant 4)

theorem raw_polynomial : PolynomialBound (fun _ n => raw n) :=
  add (add (add (add (add (mul (constant 14) second) (constant 30))
    request_polynomial) GaussCellPolynomialClock.invocation_polynomial)
    (add (mul (constant 52)
      (add (add (add second second) (constant 1))
        (mul request_polynomial (constant _)))) (constant 54))) (constant 3)

theorem cell_polynomial : PolynomialBound (fun _ n => cell n) :=
  add (add (add raw_polynomial (mul (constant 4) answer_polynomial))
    (frame_polynomial answer_polynomial)) (constant 10)

theorem cellBytes_polynomial : PolynomialBound (fun _ n => cellBytes n) :=
  add (mul (constant 3) answer_polynomial) (constant 1)

theorem rowValues_polynomial : PolynomialBound (fun _ n => rowValues n) :=
  mul (mul second second) cellBytes_polynomial

theorem rowBytes_polynomial : PolynomialBound (fun _ n => rowBytes n) :=
  add (add (mul (constant 2) second) (constant 1))
    (mul second rowValues_polynomial)

theorem rowWriter_polynomial : PolynomialBound (fun _ n =>
    GaussWordRowTraversal.writerBound n (cell n) (rowValues n)) := by
  unfold GaussWordRowTraversal.writerBound
  exact add (mul second
    (add (add cell_polynomial (mul (constant 2) rowValues_polynomial))
      (constant 5))) (constant 5)

theorem row_polynomial : PolynomialBound (fun _ n => row n) :=
  add (add (add (add (add header_polynomial rowWriter_polynomial)
    (add (mul (constant 2) second) (constant 1)))
    (mul (constant 4) rowBytes_polynomial))
    (frame_polynomial rowBytes_polynomial)) (constant 11)

theorem gridValues_polynomial : PolynomialBound (fun _ n => gridValues n) :=
  mul second (add (mul (constant 3) rowBytes_polynomial) (constant 1))

theorem gridWriter_polynomial : PolynomialBound (fun _ n =>
    GaussWordGridTraversal.writerBound n 1 (row n) (gridValues n)) := by
  unfold GaussWordGridTraversal.writerBound
  exact add (mul second
    (add (add (mul (constant 1)
      (add (add row_polynomial (mul (constant 2) gridValues_polynomial))
        (constant 2))) (mul (constant 4) (constant 1))) (constant 8))) (constant 5)

theorem clock_polynomial : PolynomialBound (fun _ n => clock n) := by
  exact add (add (add header_polynomial gridWriter_polynomial)
    (add (mul (constant 2) second) (constant 1))) (constant 1)

/-- One coefficient and exponent work for every matrix and every selected
pivot. They bound an actual run of the same complete matrix printer and are
chosen before the matrix, dimensions or coordinates. -/
theorem uniform_physical_grid : ∃ C e : Nat,
    ∀ {m k : Nat} (B : Fin m → Fin k → ℚ)
      (r pivot : Fin m) (c : Fin k), B pivot c≠0 →
    ∃ t≤C*(GaussConcreteCellEntry.dataCap B+1)^e,
      ∃ v : GaussConcreteGrid.Control,
      ((EthInapproximability.CurrentPaper.BitMachineEncoding.advance GaussConcreteGrid.program)^[t])
        (⟨some GaussConcreteGrid.start,GaussConcreteGrid.control,
          (GaussConcreteGrid.initialData B r pivot c).contents⟩ :
            Turing.TM2.Cfg (fun _ : GaussConcreteGrid.Stack => Bool)
              GaussConcreteGrid.Label GaussConcreteGrid.Control) =
        ⟨none,v,Function.update (GaussConcreteGrid.initialData B r pivot c).contents
          (.inr .output) (GaussPhysical.encodeTypedMatrix
            (SequentialTotality.clearTyped (SequentialTotality.swapTyped B r pivot) r c))⟩ := by
  have hpoly := clock_polynomial
  unfold PolynomialBound at hpoly
  obtain ⟨C,e,hC⟩ := hpoly
  refine ⟨C,e,?_⟩
  intro m k B r pivot c hn
  obtain ⟨t,ht,v,he⟩ := GaussConcreteGridClock.physical_grid_clock B r pivot c hn
  have hp := hC 0 (GaussConcreteCellEntry.dataCap B)
  simp only [Nat.zero_add] at hp
  exact ⟨t,ht.trans ((grid_clock_le B r pivot c hn).trans hp),v,he⟩

#print axioms clock_polynomial
#print axioms uniform_physical_grid
end
end CurrentAdditive.GaussConcreteGridPolynomialBound
