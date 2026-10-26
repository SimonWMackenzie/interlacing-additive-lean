import Paper2.SSSchedIndep

/-! Lane owner:a-sched-space-1, WP-SCHED segment (4): the `BitMachine.Machine` form.

`schedMachine Δ γ o = BitMachineEncoding.ofFinite inCell o (schedStart Δ γ) (schedCtl Δ γ) (sched Δ γ)`:
the SAME fixed program `SSSched.sched Δ γ`, renamed to finite indices by the admitted `ofFinite`, with input stack
the byte cell (so `Machine.init (encode g)` is exactly the admitted start bank `G0 g`, literal bytes, no packet
codec) and output stack any chosen cell `o`.  `schedMachine_outputs`: for every cell `o` the machine outputs
exactly that cell of the stated final bank within `2^E·(|encode g|+1)^E`, `E = 45·cF Δ γ`.
`schedule_values_polytime`: the seven designations print exactly unary `L`, `s`, `q₁`, `q₂`, `w`, `Q` and `[bit]`,
`bit = true ↔ Checks`.  Admitted tool: `BitMachineEncoding.outputsWithin_of_raw_run`. -/

namespace SSSchedMachine

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2
open Paper2.A3Assembly
open Paper2.CountFront (J2 LK QK jc lc qc gB G0 LFacts QFacts)
open SSSched

abbrev labOf {K L σ : Type*} (_ : L → TM2.Stmt (fun _ : K => Bool) L σ) : Type _ := L
abbrev ctlOf {K L σ : Type*} (_ : L → TM2.Stmt (fun _ : K => Bool) L σ) : Type _ := σ

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxSize 131072 in
set_option synthInstance.maxHeartbeats 4000000 in
noncomputable def ftKS : Fintype KS := inferInstance

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxSize 131072 in
set_option synthInstance.maxHeartbeats 4000000 in
noncomputable def ftL (Δ : ℕ) (γ : ℚ) : Fintype (labOf (sched Δ γ)) := inferInstance

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxSize 131072 in
set_option synthInstance.maxHeartbeats 4000000 in
noncomputable def ftC (Δ : ℕ) (γ : ℚ) : Fintype (ctlOf (sched Δ γ)) := inferInstance

/-- The byte cell (the machine's input stack). -/
def inCell : KS := .inl gB

/-- **The schedule machine as a `BitMachine.Machine`**, output designation `o`. -/
def schedMachine (Δ : ℕ) (γ : ℚ) (o : KS) : BitMachine.Machine :=
  @ofFinite KS _ _ ftKS (ftL Δ γ) (ftC Δ γ) inCell o (schedStart Δ γ) (schedCtl Δ γ) (sched Δ γ)

/-- The stated final bank. -/
def finalBank (g : EncodedGraph.Graph) (hg : g.Valid) (FL : LK → List Bool) (FQ : QK → List Bool) (bit : Bool) :
    KS → List Bool :=
  Function.update (Function.update (Sum.elim (gExit g hg FL FQ) (fun _ => [bit])) sA []) sB []

theorem rawInit_eq (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) :
    rawInit inCell (schedStart Δ γ) (schedCtl Δ γ) (EncodedGraph.encode g) =
      (⟨some (schedStart Δ γ), schedCtl Δ γ, Sum.elim (G0 g) (fun _ => [])⟩ :
        TM2.Cfg (fun _ : KS => Bool) _ _) := by
  simp only [rawInit]
  congr 1
  funext k
  rcases k with k | k
  · by_cases h : k = gB
    · subst h; simp [inCell, G0]
    · simp [inCell, G0, h, Function.update_of_ne h]
  · simp [inCell]

theorem schedMachine_outputs (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) :
    ∃ bit : Bool, ∃ FL : LK → List Bool, ∃ FQ : QK → List Bool,
      LFacts g.vertices FL ∧
      QFacts γ.num.toNat γ.den Δ g.vertices g.edges.length (Nat.clog 2 g.vertices)
        (2 ^ (16 + (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1))))
        (2 ^ ((Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)) * (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)))) FQ ∧
      FL LProducer.sC = LProducer.u (SourceProfileParameters.width (Nat.clog 2 g.vertices)) ∧
      FL LProducer.q1C = LProducer.u (SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2) ∧
      FL LProducer.q2C = LProducer.u (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices)) ∧
      FL LProducer.wC = LProducer.u (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices)) ∧
      FQ (.inl 2) = QProducer.u (Nat.clog 2 g.vertices) ∧
      FQ (.inl 24) = QProducer.u
        (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) ∧
      (bit = true ↔ CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) Δ γ) ∧
      ∀ o : KS, (schedMachine Δ γ o).OutputsWithin (EncodedGraph.encode g) (finalBank g hg FL FQ bit o)
        (2 ^ (FrontClock13.cF Δ γ * 45) * ((EncodedGraph.encode g).length + 1) ^ (FrontClock13.cF Δ γ * 45)) := by
  obtain ⟨T, hT, u, bit, FL, FQ, hr, hLF, hQF, -, hs, hq1, hq2, hw, hL, hQ, hbit⟩ :=
    SSSchedClock.schedule_machine Δ γ hγ hΔ g hg hn hinc hdeg
  refine ⟨bit, FL, FQ, hLF, hQF, hs, hq1, hq2, hw, hL, hQ, hbit, fun o => ?_⟩
  have hrun := hr
  rw [← rawInit_eq Δ γ g] at hrun
  exact @outputsWithin_of_raw_run KS _ _ ftKS (ftL Δ γ) (ftC Δ γ) _ inCell o (schedStart Δ γ) (schedCtl Δ γ)
    (sched Δ γ) (EncodedGraph.encode g) (finalBank g hg FL FQ bit o) T _ hT
    (by rw [hrun]) (by rw [hrun]; rfl)

theorem final_inl (g : EncodedGraph.Graph) (hg : g.Valid) (FL : LK → List Bool) (FQ : QK → List Bool)
    (bit : Bool) (x : J2) (hA : (Sum.inl x : KS) ≠ sA) (hB : (Sum.inl x : KS) ≠ sB) :
    finalBank g hg FL FQ bit (.inl x) = gExit g hg FL FQ x := by
  unfold finalBank
  rw [Function.update_of_ne hB, Function.update_of_ne hA]
  rfl

theorem final_sO (g : EncodedGraph.Graph) (hg : g.Valid) (FL : LK → List Bool) (FQ : QK → List Bool)
    (bit : Bool) : finalBank g hg FL FQ bit sO = [bit] := by
  unfold finalBank
  rw [Function.update_of_ne (Ne.symm sB_sO), Function.update_of_ne (Ne.symm sA_sO)]
  rfl

/-- The output cells of the schedule values. -/
def cL : KS := .inl (jc (qc (.inl 2)))
def cS : KS := .inl (jc (lc LProducer.sC))
def cQ1 : KS := .inl (jc (lc LProducer.q1C))
def cQ2 : KS := .inl (jc (lc LProducer.q2C))
def cW : KS := .inl (jc (lc LProducer.wC))
def cQ : KS := .inl (jc (qc (.inl 24)))

/-- **WP-SCHED, BitMachine form.** For each schedule value, the fixed machine (same program, output designation
the value's cell) prints exactly its unary encoding from the literal graph bytes; the flag designation prints the
Checks bit; one polynomial `2^E·(|encode g|+1)^E`, `E = 45·cF Δ γ`, independent of any repetition count. -/
theorem schedule_values_polytime (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) :
    let B := 2 ^ (FrontClock13.cF Δ γ * 45) * ((EncodedGraph.encode g).length + 1) ^ (FrontClock13.cF Δ γ * 45)
    let L := Nat.clog 2 g.vertices
    (schedMachine Δ γ cL).OutputsWithin (EncodedGraph.encode g) (List.replicate L true) B ∧
    (schedMachine Δ γ cS).OutputsWithin (EncodedGraph.encode g)
      (List.replicate (SourceProfileParameters.width L) true) B ∧
    (schedMachine Δ γ cQ1).OutputsWithin (EncodedGraph.encode g)
      (List.replicate (SourceProfileParameters.width L - 2) true) B ∧
    (schedMachine Δ γ cQ2).OutputsWithin (EncodedGraph.encode g)
      (List.replicate (SourceProfileParameters.outerWidth L) true) B ∧
    (schedMachine Δ γ cW).OutputsWithin (EncodedGraph.encode g)
      (List.replicate (ParameterizedCanonicalSource.restorationWidth L) true) B ∧
    (schedMachine Δ γ cQ).OutputsWithin (EncodedGraph.encode g)
      (List.replicate (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length L Δ γ) true) B ∧
    ∃ bit : Bool, (schedMachine Δ γ sO).OutputsWithin (EncodedGraph.encode g) [bit] B ∧
      (bit = true ↔ CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length) L Δ γ) := by
  intro B L
  obtain ⟨bit, FL, FQ, -, -, hs, hq1, hq2, hw, hL, hQ, hbit, hout⟩ :=
    schedMachine_outputs Δ γ hγ hΔ g hg hn hinc hdeg
  have nA : ∀ x : J2, x ≠ jc (lc LProducer.nC) → (Sum.inl x : KS) ≠ sA := fun x h e => h (Sum.inl_injective e)
  have nB : ∀ x : J2, x ≠ jc (qc (.inl 1)) → (Sum.inl x : KS) ≠ sB := fun x h e => h (Sum.inl_injective e)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, bit, ?_, hbit⟩
  · have h := hout cL
    rw [cL, final_inl g hg FL FQ bit _ (nA _ (by simp [jc, lc, qc])) (nB _ (by simp [jc, qc]))] at h
    simpa [gExit, jc, qc, hL, QProducer.u] using h
  · have h := hout cS
    rw [cS, final_inl g hg FL FQ bit _ (nA _ (by simp [jc, lc, LProducer.c])) (nB _ (by simp [jc, lc, qc]))] at h
    simpa [gExit, jc, lc, hs, LProducer.u] using h
  · have h := hout cQ1
    rw [cQ1, final_inl g hg FL FQ bit _ (nA _ (by simp [jc, lc, LProducer.c])) (nB _ (by simp [jc, lc, qc]))] at h
    simpa [gExit, jc, lc, hq1, LProducer.u] using h
  · have h := hout cQ2
    rw [cQ2, final_inl g hg FL FQ bit _ (nA _ (by simp [jc, lc, LProducer.c])) (nB _ (by simp [jc, lc, qc]))] at h
    simpa [gExit, jc, lc, hq2, LProducer.u] using h
  · have h := hout cW
    rw [cW, final_inl g hg FL FQ bit _ (nA _ (by simp [jc, lc, LProducer.c])) (nB _ (by simp [jc, lc, qc]))] at h
    simpa [gExit, jc, lc, hw, LProducer.u] using h
  · have h := hout cQ
    rw [cQ, final_inl g hg FL FQ bit _ (nA _ (by simp [jc, lc, qc])) (nB _ (by simp [jc, qc]))] at h
    simpa [gExit, jc, qc, hQ, QProducer.u] using h
  · have h := hout sO
    rwa [final_sO] at h

end

end SSSchedMachine

#print axioms SSSchedMachine.schedMachine_outputs
#print axioms SSSchedMachine.schedule_values_polytime
