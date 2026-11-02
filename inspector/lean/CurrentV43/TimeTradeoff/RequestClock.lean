import CurrentV43.TimeTradeoff.DeterministicCaller
import Paper2.A4T24RuntimeComposed

/-! Complete paid sparse clock for the actual deterministic arbitrary-gap
request machine of v43 `thm:time-tradeoff`. The base size constant uses only
the constructor/source; schedule and estimator enter only polynomial degrees. -/
namespace CurrentV43.TimeTradeoff
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V40DeterministicSourcePack
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

variable (Src : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Src))

def requestSourceExponent : ℕ := (Src.sizeExponent+4)*CurrentV43.MixedCaller.requestExponent Src Bsrc

theorem requestTime_source_bound (cs : ℕ) (Φ : ValidFormula) (K : ℕ)
    (hsp : Φ.val.clauses.length ≤ cs*Φ.val.variables)
    (hcut : DeterministicETHSourceBridge.graphPolynomialCutoff Src Bsrc cs ≤ Φ.val.variables)
    (hN : 16 ≤ Φ.val.variables)
    (hbase : 2^(4*V42ActualSource.k0 Src Bsrc) ≤ Φ.val.variables) :
    CurrentV43.MixedCaller.requestTime Src Bsrc Φ K ≤
      (deterministicSize (V42ETHPhysical.amplification Src Bsrc)
        (deterministicSourceConstant Src Bsrc) Φ.val.variables K)^(requestSourceExponent Src Bsrc) := by
  let n:=Φ.val.variables
  let e:=Src.sizeExponent+3
  let g:=t10Graph Src Bsrc Φ
  let A:=V42ETHPhysical.amplification Src Bsrc
  let C:=deterministicSourceConstant Src Bsrc
  let Q:=requestSourceExponent Src Bsrc
  have hgraph:g.vertices ≤ n^e :=
    DeterministicETHSourceBridge.sparse_graph_vertices_polynomial Src Bsrc cs Φ hsp hcut
  have hpublic:V42RuntimePrefix.N (V42ActualSource.k0 Src Bsrc) g ≤ n^(e+1) :=
    V42ETHNumerics.selected_polynomial (V42ActualSource.k0 Src Bsrc) n e g
      hN (by unfold e;omega) hgraph hbase
  have hC:1 ≤ C:=deterministicSourceConstant_pos Src Bsrc
  change (V42RuntimePrefix.N (V42ActualSource.k0 Src Bsrc) g)^
    (CurrentV43.MixedCaller.requestExponent Src Bsrc*A^K) ≤ ((n+2)^(C*A^K))^Q
  calc
    _ ≤ (n^(e+1))^(CurrentV43.MixedCaller.requestExponent Src Bsrc*A^K) :=
      Nat.pow_le_pow_left hpublic _
    _ = n^(Q*A^K) := by rw [←pow_mul]; congr 1; unfold Q requestSourceExponent e; ring
    _ ≤ (n+2)^(Q*A^K) := Nat.pow_le_pow_left (by omega) _
    _ ≤ (n+2)^((C*A^K)*Q) := Nat.pow_le_pow_right (by omega) (by
      calc Q*A^K=A^K*Q:=by ring
           _ ≤ (C*A^K)*Q:=Nat.mul_le_mul_right Q (Nat.le_mul_of_pos_left _ hC))
    _ = _ := by rw [←pow_mul]

/-- General caller accounting on an arbitrary input family. The premises
are separate source/gap/request resource bounds, never a finished SAT clock. -/
theorem request_clock_poly {ι : Type*} (sz : ι → ℕ) (input : ι → List Bool)
    (G : CurrentV43.ParametricSource.Schedule) (cs cutoff : ℕ) (hcut : 1 ≤ cutoff)
    (hi : Unit4Shell.Poly.PolyIn sz (fun i=>(input i).length))
    (hphi : Unit4Shell.Poly.PolyIn sz (fun i=>
      (EncodedCNF.encode (routedFormula cs cutoff hcut (input i)).val).length))
    (hk : Unit4Shell.Poly.PolyIn sz (fun i=>
      (G.producer.result (EncodedCNF.encode (routedFormula cs cutoff hcut (input i)).val)).length))
    (hgap : Unit4Shell.Poly.PolyIn sz (fun i=>
      G.producer.clock (EncodedCNF.encode (routedFormula cs cutoff hcut (input i)).val)))
    (hmain : Unit4Shell.Poly.PolyIn sz (fun i=>
      CurrentV43.MixedCaller.requestTime Src Bsrc (routedFormula cs cutoff hcut (input i))
        (routedGap G cs cutoff hcut (input i)))) :
    Unit4Shell.Poly.PolyIn sz (fun i=>(routedRequest Src Bsrc G cs cutoff hcut).clock (input i)) := by
  have hfront:Unit4Shell.Poly.PolyIn sz (fun i=>(deterministicFront Src Bsrc G).clock
      (EncodedCNF.encode (routedFormula cs cutoff hcut (input i)).val)) := by
    apply Unit4Shell.Poly.mono (fun i=>deterministicFront_clock Src Bsrc G _)
    exact Unit4Shell.Poly.mul (Unit4Shell.Poly.const _)
      (Unit4Shell.Poly.pow (Unit4Shell.Poly.add
        (Unit4Shell.Poly.add (Unit4Shell.Poly.add hphi hk) hgap)
        (Unit4Shell.Poly.const 1)) _)
  have hgraph:Unit4Shell.Poly.PolyIn sz (fun i=>(routedGraphInput Src Bsrc G cs cutoff hcut (input i)).length) := by
    apply Unit4Shell.Poly.mono (fun i=>BitMachine.output_length_bound
      (deterministicFront Src Bsrc G).machine
      (deterministicFront_outputs Src Bsrc G (routedFormula cs cutoff hcut (input i))
        (hcut.trans (AEth4.routed4_variables (cs+2) cutoff (input i)))))
    exact Unit4Shell.Poly.add hphi (Unit4Shell.Poly.mul hfront (Unit4Shell.Poly.const _))
  change Unit4Shell.Poly.PolyIn sz (fun i=>
    (sparseRoute cs cutoff hcut).coefficient*((input i).length+1)^(sparseRoute cs cutoff hcut).degree+
    2*(EncodedCNF.encode (routedFormula cs cutoff hcut (input i)).val).length+2+
    (deterministicFront Src Bsrc G).clock (EncodedCNF.encode (routedFormula cs cutoff hcut (input i)).val)+
    2*(routedGraphInput Src Bsrc G cs cutoff hcut (input i)).length+2+
    CurrentV43.MixedCaller.requestTime Src Bsrc (routedFormula cs cutoff hcut (input i))
      (routedGap G cs cutoff hcut (input i)))
  have hr:=Unit4Shell.Poly.mul
    (Unit4Shell.Poly.const (sparseRoute cs cutoff hcut).coefficient)
    (Unit4Shell.Poly.pow (Unit4Shell.Poly.add hi (Unit4Shell.Poly.const 1))
      (sparseRoute cs cutoff hcut).degree)
  exact Unit4Shell.Poly.add (Unit4Shell.Poly.add (Unit4Shell.Poly.add
    (Unit4Shell.Poly.add (Unit4Shell.Poly.add (Unit4Shell.Poly.add hr
      (Unit4Shell.Poly.mul (Unit4Shell.Poly.const 2) hphi))
        (Unit4Shell.Poly.const 2)) hfront)
      (Unit4Shell.Poly.mul (Unit4Shell.Poly.const 2) hgraph))
      (Unit4Shell.Poly.const 2)) hmain

/-- The physically executed request machine has its claimed S-polynomial
clock, uniformly over the arbitrary paid schedule. No estimator is involved. -/
theorem request_clock_sparse (G : CurrentV43.ParametricSource.Schedule)
    (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) :
    ∃ c d N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
      (routedRequest Src Bsrc G cs cutoff hcut).clock (EncodedCNF.encode Φ.val) ≤
        c*(deterministicSize (V42ETHPhysical.amplification Src Bsrc)
          (deterministicSourceConstant Src Bsrc) Φ.val.variables (G.gap Φ.val.variables)+1)^d := by
  obtain ⟨cg,dg,hpaid⟩:=G.paid cs
  let N₀:=max cutoff (max (DeterministicETHSourceBridge.graphPolynomialCutoff Src Bsrc cs)
    (max 16 (max (2^(4*V42ActualSource.k0 Src Bsrc)) (28*cs+9))))
  let Domain:={Φ : ValidFormula // Φ.val.clauses.length ≤ cs*Φ.val.variables ∧ N₀ ≤ Φ.val.variables}
  let input:Domain→List Bool:=fun x=>EncodedCNF.encode x.val.val
  let size:Domain→ℕ:=fun x=>deterministicSize (V42ETHPhysical.amplification Src Bsrc)
    (deterministicSourceConstant Src Bsrc) x.val.val.variables (G.gap x.val.val.variables)
  have hroute (x:Domain):routedFormula cs cutoff hcut (input x)=x.val :=
    routedFormula_original cs cutoff hcut x.val x.property.1 ((le_max_left _ _).trans x.property.2)
  have hdom (x:Domain):x.val.val.variables+G.gap x.val.val.variables+2 ≤ size x :=
    deterministicSize_dominates _ _ _ _
      ((by decide : 2 ≤ (2:ℕ)^64).trans (V42GraphRuntime.amplification_ge (V42ActualSource.k0 Src Bsrc)))
      (deterministicSourceConstant_pos Src Bsrc)
  have hi:Unit4Shell.Poly.PolyIn size (fun x=>(input x).length) := by
    refine ⟨1,3,fun x=>?_⟩
    have hlarge:=x.property.2
    have hc:28*cs+9 ≤ x.val.val.variables:=by dsimp [N₀] at hlarge;omega
    have he:=Unit4Shell.T24RuntimeComposed.encode_length_cube cs x.val x.property.1 hc
    have hb:x.val.val.variables+2 ≤ size x+1:=by have:=hdom x;omega
    have hp:=Nat.pow_le_pow_left hb 3
    simpa only [one_mul] using (show (input x).length ≤ (size x+1)^3 by dsimp [input];omega)
  have hphi:Unit4Shell.Poly.PolyIn size (fun x=>
      (EncodedCNF.encode (routedFormula cs cutoff hcut (input x)).val).length) := by
    simpa only [hroute] using hi
  have hk:Unit4Shell.Poly.PolyIn size (fun x=>
      (G.producer.result (EncodedCNF.encode (routedFormula cs cutoff hcut (input x)).val)).length) := by
    refine ⟨1,1,fun x=>?_⟩
    change (G.producer.result (EncodedCNF.encode (routedFormula cs cutoff hcut (input x)).val)).length ≤ _
    rw [hroute,G.correct,List.length_replicate]
    simpa only [pow_one,one_mul] using (show G.gap x.val.val.variables ≤ size x+1 by have:=hdom x;omega)
  have hg:Unit4Shell.Poly.PolyIn size (fun x=>
      G.producer.clock (EncodedCNF.encode (routedFormula cs cutoff hcut (input x)).val)) := by
    refine ⟨cg,dg,fun x=>?_⟩
    change G.producer.clock (EncodedCNF.encode (routedFormula cs cutoff hcut (input x)).val) ≤ _
    rw [hroute]
    apply (hpaid x.val x.property.1).trans
    exact Nat.mul_le_mul_left cg (Nat.pow_le_pow_left (by have:=hdom x;omega) dg)
  have hm:Unit4Shell.Poly.PolyIn size (fun x=>
      CurrentV43.MixedCaller.requestTime Src Bsrc (routedFormula cs cutoff hcut (input x))
        (routedGap G cs cutoff hcut (input x))) := by
    refine ⟨1,requestSourceExponent Src Bsrc,fun x=>?_⟩
    have hlarge:=x.property.2
    have hgc:DeterministicETHSourceBridge.graphPolynomialCutoff Src Bsrc cs ≤ x.val.val.variables:=by dsimp [N₀] at hlarge;omega
    have hn:16 ≤ x.val.val.variables:=by dsimp [N₀] at hlarge;omega
    have hb:2^(4*V42ActualSource.k0 Src Bsrc) ≤ x.val.val.variables:=by dsimp [N₀] at hlarge;omega
    simp only [routedGap,hroute]
    exact (requestTime_source_bound Src Bsrc cs x.val _ x.property.1 hgc hn hb).trans
      (by simpa only [one_mul] using Nat.pow_le_pow_left (Nat.le_add_right (size x) 1) (requestSourceExponent Src Bsrc))
  obtain ⟨c,d,h⟩:=request_clock_poly Src Bsrc size input G cs cutoff hcut hi hphi hk hg hm
  exact ⟨c,d,N₀,fun Φ hsp hN=>h ⟨Φ,hsp,hN⟩⟩

#print axioms requestTime_source_bound
#print axioms request_clock_poly
#print axioms request_clock_sparse
end
end CurrentV43.TimeTradeoff
