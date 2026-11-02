import CurrentV43.TimeTradeoff.RequestClock
import CurrentV43.TimeTradeoff.ErrorNonnegative
import CurrentAdditive.V40DeterministicRoutedLaw

/-! Deterministic-construction/deterministic-estimator branch of v43
`thm:time-tradeoff`, source main.tex 3238--3287. The fixed sparse router
handles every smaller promised input by its checked finite replacement;
all large original inputs are unchanged. No ETH hypothesis occurs.
The construction constants precede the estimator and arbitrary schedule. -/
namespace CurrentV43.TimeTradeoff
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39FramedNumerical V39PermittedDeterministicExtraction
open V40DeterministicSourcePack
open scoped Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

variable (Src : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Src))

theorem deterministic_caller_clock_poly {ι : Type*} (sz : ι → ℕ) (input : ι → List Bool)
    (G : CurrentV43.ParametricSource.Schedule) (E : Estimator)
    (cs cutoff : ℕ) (hcut : 1 ≤ cutoff)
    (hi : Unit4Shell.Poly.PolyIn sz (fun i=>(input i).length))
    (hp : Unit4Shell.Poly.PolyIn sz (fun i=>(routedRequest Src Bsrc G cs cutoff hcut).clock (input i))) :
    Unit4Shell.Poly.PolyIn sz
      (fun i=>(deterministicCaller Src Bsrc G E cs cutoff hcut).clock (input i)) := by
  let P:=routedRequest Src Bsrc G cs cutoff hcut
  have ho:Unit4Shell.Poly.PolyIn sz (fun i=>(P.result (input i)).length) := by
    apply Unit4Shell.Poly.mono (fun i=>BitMachine.output_length_bound P.machine (P.outputs (input i)))
    exact Unit4Shell.Poly.add hi (Unit4Shell.Poly.mul hp (Unit4Shell.Poly.const _))
  change Unit4Shell.Poly.PolyIn sz (fun i=>P.clock (input i)+2*(P.result (input i)).length+2+
    E.clockCoefficient*((P.result (input i)).length+1)^E.clockDegree)
  exact Unit4Shell.Poly.add (Unit4Shell.Poly.add
    (Unit4Shell.Poly.add hp (Unit4Shell.Poly.mul (Unit4Shell.Poly.const 2) ho))
    (Unit4Shell.Poly.const 2))
    (Unit4Shell.Poly.mul (Unit4Shell.Poly.const E.clockCoefficient)
      (Unit4Shell.Poly.pow (Unit4Shell.Poly.add ho (Unit4Shell.Poly.const 1)) E.clockDegree))

/-- Every physically paid deterministic stage fits a polynomial of S in the
original variables. The polynomial may depend on the estimator and schedule. -/
theorem deterministic_caller_clock_sparse (G : CurrentV43.ParametricSource.Schedule)
    (E : Estimator) (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) :
    ∃ c d N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
      (deterministicCaller Src Bsrc G E cs cutoff hcut).clock (EncodedCNF.encode Φ.val) ≤
        c*(deterministicSize (V42ETHPhysical.amplification Src Bsrc)
          (deterministicSourceConstant Src Bsrc) Φ.val.variables (G.gap Φ.val.variables))^d := by
  obtain ⟨cp,dp,Np,hp⟩:=request_clock_sparse Src Bsrc G cs cutoff hcut
  let N₀:=max Np (28*cs+9)
  let Domain:={Φ : ValidFormula // Φ.val.clauses.length ≤ cs*Φ.val.variables ∧ N₀ ≤ Φ.val.variables}
  let input:Domain→List Bool:=fun x=>EncodedCNF.encode x.val.val
  let size:Domain→ℕ:=fun x=>deterministicSize (V42ETHPhysical.amplification Src Bsrc)
    (deterministicSourceConstant Src Bsrc) x.val.val.variables (G.gap x.val.val.variables)
  have hdom (x:Domain):x.val.val.variables+G.gap x.val.val.variables+2 ≤ size x :=
    deterministicSize_dominates _ _ _ _
      ((by decide : 2 ≤ (2:ℕ)^64).trans (V42GraphRuntime.amplification_ge (V42ActualSource.k0 Src Bsrc)))
      (deterministicSourceConstant_pos Src Bsrc)
  have hi:Unit4Shell.Poly.PolyIn size (fun x=>(input x).length) := by
    refine ⟨1,3,fun x=>?_⟩
    have he:=Unit4Shell.T24RuntimeComposed.encode_length_cube cs x.val x.property.1
      ((le_max_right _ _).trans x.property.2)
    have hb:x.val.val.variables+2 ≤ size x+1:=by have:=hdom x;omega
    have hpow:=Nat.pow_le_pow_left hb 3
    simpa only [one_mul] using (show (input x).length ≤ (size x+1)^3 by dsimp [input];omega)
  have hreq:Unit4Shell.Poly.PolyIn size (fun x=>(routedRequest Src Bsrc G cs cutoff hcut).clock (input x)) :=
    ⟨cp,dp,fun x=>hp x.val x.property.1 ((le_max_left _ _).trans x.property.2)⟩
  obtain ⟨c,d,h⟩:=deterministic_caller_clock_poly Src Bsrc size input G E cs cutoff hcut hi hreq
  refine ⟨c*2^d,d,N₀,fun Φ hsp hN=>?_⟩
  have hd:=hdom ⟨Φ,hsp,hN⟩
  exact (h ⟨Φ,hsp,hN⟩).trans (polynomial_charge (by dsimp [size] at hd ⊢;omega) (le_refl _) c d)

/-- The actual all-input implication, exact on every cs-sparse formula and
running in S(N,k(N))^O(1) in its original N. The source constants are fixed
before the estimator, error function, accuracy threshold and gap program. -/
theorem deterministic_time_tradeoff
    (cs : ℕ) (G : CurrentV43.ParametricSource.Schedule)
    (A : PermittedDeterministicEstimator) (a : ℕ → ℝ) (ha : Monotone a)
    (T₀ : ℕ) (hA : DeterministicSquareAccuracy A a T₀)
    (hgap : ∃ N₁ : ℕ, ∀ N, N₁ ≤ N →
      2*a (deterministicSize (V42ETHPhysical.amplification Src Bsrc)
        (deterministicSourceConstant Src Bsrc) N (G.gap N)) < (G.gap N:ℝ)) :
    ∃ M : PhysicalConcat.Producer,
      (∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs*Φ.val.variables →
        M.result (EncodedCNF.encode Φ.val)=[decide (EncodedCNF.Satisfiable Φ.val)]) ∧
      ∃ c d N₀ : ℕ, ∀ Φ : ValidFormula,
        Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
        M.clock (EncodedCNF.encode Φ.val) ≤
          c*(deterministicSize (V42ETHPhysical.amplification Src Bsrc)
            (deterministicSourceConstant Src Bsrc) Φ.val.variables (G.gap Φ.val.variables))^d := by
  obtain ⟨Ngap,hgap⟩:=hgap
  let cutoff:=max 1 (max Ngap (max (Bsrc.degreeBound*T₀)
    (max (DeterministicETHSourceBridge.graphPolynomialCutoff Src Bsrc (cs+2))
      (max 16 (2^(4*V42ActualSource.k0 Src Bsrc))))))
  have hcut:1 ≤ cutoff:=le_max_left _ _
  let M:=deterministicCaller Src Bsrc G (deterministicEstimator A) cs cutoff hcut
  refine ⟨M,?_,deterministic_caller_clock_sparse Src Bsrc G (deterministicEstimator A) cs cutoff hcut⟩
  intro Φ hsp
  let Ψ:=routedFormula cs cutoff hcut (EncodedCNF.encode Φ.val)
  have hΨ:cutoff ≤ Ψ.val.variables:=AEth4.routed4_variables (cs+2) cutoff _
  have hr1:max Ngap (max (Bsrc.degreeBound*T₀)
    (max (DeterministicETHSourceBridge.graphPolynomialCutoff Src Bsrc (cs+2))
      (max 16 (2^(4*V42ActualSource.k0 Src Bsrc))))) ≤ Ψ.val.variables:=
    (le_max_right _ _).trans hΨ
  have hNgap:Ngap ≤ Ψ.val.variables:=(le_max_left _ _).trans hr1
  have hr2:max (Bsrc.degreeBound*T₀)
    (max (DeterministicETHSourceBridge.graphPolynomialCutoff Src Bsrc (cs+2))
      (max 16 (2^(4*V42ActualSource.k0 Src Bsrc)))) ≤ Ψ.val.variables:=
    (le_max_right _ _).trans hr1
  have hTfloor:Bsrc.degreeBound*T₀ ≤ Ψ.val.variables:=(le_max_left _ _).trans hr2
  have hr3:max (DeterministicETHSourceBridge.graphPolynomialCutoff Src Bsrc (cs+2))
      (max 16 (2^(4*V42ActualSource.k0 Src Bsrc))) ≤ Ψ.val.variables:=
    (le_max_right _ _).trans hr2
  have hgraph:DeterministicETHSourceBridge.graphPolynomialCutoff Src Bsrc (cs+2) ≤ Ψ.val.variables:=
    (le_max_left _ _).trans hr3
  have hr4:max 16 (2^(4*V42ActualSource.k0 Src Bsrc)) ≤ Ψ.val.variables:=
    (le_max_right _ _).trans hr3
  have h16:16 ≤ Ψ.val.variables:=(le_max_left _ _).trans hr4
  have hbase:2^(4*V42ActualSource.k0 Src Bsrc) ≤ Ψ.val.variables:=(le_max_right _ _).trans hr4
  have hs:Ψ.val.clauses.length ≤ (cs+2)*Ψ.val.variables:=
    V40DeterministicETHEndpoint.routed_sparse cs cutoff hcut _
  have hT:T₀ ≤ V42ActualLower.entryCount (V42ActualSource.run Src Bsrc Ψ (G.gap Ψ.val.variables)) :=
    deterministic_source_entries_large Src Bsrc Ψ T₀ _ hTfloor
  have hS:=deterministic_source_size Src Bsrc (cs+2) Ψ (G.gap Ψ.val.variables) hs
    hgraph h16 hbase
  have hg:=hgap Ψ.val.variables hNgap
  have hc:=deterministic_source_classification Src Bsrc A a ha T₀ _
    (G.gap Ψ.val.variables) hA Ψ hT hS hg
  have hsat:EncodedCNF.Satisfiable Ψ.val ↔ EncodedCNF.Satisfiable Φ.val:=
    V40DeterministicETHEndpoint.routed_sat_iff cs cutoff hcut Φ hsp
  change (deterministicEstimator A).run (V42ActualSource.request Src Bsrc Ψ (G.gap Ψ.val.variables))=_
  simpa only [hsat] using hc

#print axioms deterministic_caller_clock_sparse
#print axioms deterministic_time_tradeoff
end
end CurrentV43.TimeTradeoff
