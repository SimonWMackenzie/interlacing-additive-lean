import Paper2.RepJoin

/-! Unit 3, segment (1), join: the run of the prefix `RepJoin.preProg`. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.RepJoin

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.HeaderJoin (JH)
open Paper2.SuccessXfer (OS JT)
open Paper2.SuccessInstall (mC preJH0 auxPre0 master0)
open Paper2.SuccessGraph (JT2 preJHm zG zM gIn mOut PS)
open Paper2.ThrJoin (JT3)

def vC (s q₂ m : ℕ) : Fin 3 → ℕ := ![m, s, q₂]

theorem pre_run (n p s q₁ q₂ w Q k mX mY : ℕ) (word : List Bool) (g : EncodedGraph.Graph)
    (hg : g.Valid) (output : List Bool) :
    ∃ t ≤ preBd g s q₂, ∃ v, ∃ c : ETHParameterScaleMachineLogCopy.logMachine.Config,
      ((advance preProg)^[t])
          (⟨some preStart, preCtl,
            Sum.elim (Y n p s q₁ q₂ w Q k mX mY word g 0 output) (fun _ => [])⟩ :
            TM2.Cfg (fun _ : JT5 => Bool) _ _) =
        ⟨none, v, Sum.elim (Y n p s q₁ q₂ w Q k mX mY word g (quot s q₂ g.edges.length) output)
          (MSfin g hg s q₂ c)⟩ := by
  -- (A) copy the literal graph bytes into the side endpoint region
  let T0 : JT5 → List Bool := Sum.elim (Y n p s q₁ q₂ w Q k mX mY word g 0 output) (fun _ => [])
  have hG : T0 (hj (mC zG)) = EncodedGraph.encode g := by
    change preJHm g 0 0 output (mC zG) = _
    rw [preJHm, Function.update_of_ne SuccessGraph.zG_ne_zM, SuccessGraph.preJH0_zG]
  obtain ⟨t1, ht1, v1, hr1⟩ := CopyAll.all_run cpA
    (by intro i j h; fin_cases i; fin_cases j; cases h)
    (by intro i j h; fin_cases i; fin_cases j; cases h)
    (by intro i j _; fin_cases i; fin_cases j; rfl)
    T0 (by intro i; fin_cases i; rfl) (EncodedGraph.encode g).length
    (by intro i; fin_cases i; exact le_of_eq (congrArg List.length hG)) none
  have hD1 : CopyAll.done cpA 1 T0 =
      Sum.elim (Y n p s q₁ q₂ w Q k mX mY word g 0 output)
        (Sum.elim (PublicGraphEndpointMachine.initialBank (EncodedGraph.encode g))
          (fun _ => [])) := by
    funext x
    by_cases hx : x = ps gIn
    · subst hx
      change CopyAll.done cpA 1 T0 (cpA 0 1) = _
      rw [CopyAll.done_dst cpA (by intro i j _; fin_cases i; fin_cases j; rfl) T0 0]
      change T0 (hj (mC zG)) ++ [] = _
      rw [hG, List.append_nil]
      rfl
    · rw [CopyAll.done_off cpA T0 x (by intro j h; fin_cases j; exact hx h.symm)]
      rcases x with x | (x | x)
      · rfl
      · change [] = PublicGraphEndpointMachine.initialBank (EncodedGraph.encode g) x
        rcases x with (y | y) | y
        · fin_cases y
          · exact absurd rfl hx
          all_goals rfl
        · fin_cases y <;> rfl
        · fin_cases y <;> rfl
      · rfl
  rw [hD1] at hr1
  -- (B) the admitted public-graph endpoint machine on the side region
  obtain ⟨t2, ht2, hr2⟩ := PublicGraphEndpointMachine.physical_run_public g hg
  have r2 := BitMachineStackRun.run ιPS
    (Sum.elim (Y n p s q₁ q₂ w Q k mX mY word g 0 output)
      (Sum.elim (PublicGraphEndpointMachine.initialBank (EncodedGraph.encode g)) (fun _ => [])))
    PublicGraphEndpointMachine.program (PublicGraphEndpointMachine.start (EncodedGraph.encode g))
    t2
  change _ = stackCfg ιPS _ (PublicGraphEndpointMachine.run t2 _) at r2
  rw [hr2] at r2
  simp only [stackCfg, PublicGraphEndpointMachine.start] at r2
  rw [bank_PS, bank_PS] at r2
  obtain ⟨a1, ha1, R1⟩ := BitMachineRawSequence.runs (CopyAll.prog cpA) graphP
    (.inl ⟨0, by omega⟩) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (none : Option Bool) v1 SuccessGraph.gCtl _ _ _ _ t1 t2 hr1 r2
  -- (C) copies of unary m, s, q₂ into the producer inputs
  let T2 : JT5 → List Bool := Sum.elim (Y n p s q₁ q₂ w Q k mX mY word g 0 output)
    (Sum.elim (PublicGraphEndpointMachine.resultBank g hg) (fun _ => []))
  have hval : ∀ i : Fin 3, T2 (cpC i 0) = List.replicate (vC s q₂ g.edges.length i) true := by
    intro i
    fin_cases i
    · rfl
    · exact (SamplerParameterJoin.nrSrc_value n p s q₁ q₂ w Q k mX mY word 0).trans rfl
    · exact (SamplerParameterJoin.nrSrc_value n p s q₁ q₂ w Q k mX mY word 2).trans rfl
  have hdst : ∀ i : Fin 3, T2 (cpC i 1) = [] := by
    intro i; fin_cases i <;> rfl
  have hsd : ∀ i j, cpC i 0 ≠ cpC j 1 := by
    intro i j h
    fin_cases i <;> fin_cases j <;> cases h
  have hzd : ∀ i j, cpC i 2 ≠ cpC j 1 := by
    intro i j h
    fin_cases i <;> fin_cases j <;> cases h
  have hdd : ∀ i j, cpC i 1 = cpC j 1 → i = j := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | cases h
  obtain ⟨t3, ht3, v3, hr3⟩ := CopyAll.all_run cpC hsd hzd hdd T2 (fun i => by fin_cases i <;> rfl)
    (g.edges.length + s + q₂)
    (by
      intro i
      rw [hval, List.length_replicate]
      fin_cases i <;> simp [vC] <;> omega) none
  have hD3 : CopyAll.done cpC 3 T2 =
      Sum.elim (Y n p s q₁ q₂ w Q k mX mY word g 0 output)
        (Sum.elim (PublicGraphEndpointMachine.resultBank g hg)
          (Sum.elim (RepProducer.R0 s q₂ g.edges.length) (fun _ => []))) := by
    funext z
    by_cases hz' : ∃ j, cpC j 1 = z
    · obtain ⟨j, rfl⟩ := hz'
      rw [CopyAll.done_dst cpC hdd T2 j, hval j, hdst j, List.append_nil]
      fin_cases j <;> rfl
    · rw [CopyAll.done_off cpC T2 z (fun j h => hz' ⟨j, h⟩)]
      rcases z with z | (z | (z | z))
      · rfl
      · rfl
      · change [] = RepProducer.R0 s q₂ g.edges.length z
        rcases z with i | x
        · fin_cases i
          · exact absurd ⟨1, rfl⟩ hz'
          · exact absurd ⟨2, rfl⟩ hz'
          · exact absurd ⟨0, rfl⟩ hz'
          all_goals rfl
        · rfl
      · rfl
  rw [hD3] at hr3
  obtain ⟨a2, ha2, R2⟩ := BitMachineRawSequence.runs e1 (CopyAll.prog cpC)
    (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)) (.inl ⟨0, by omega⟩)
    f1 _ (none : Option Bool) v3 _ _ _ a1 t3 R1 hr3
  -- (D) the repetition-factor producer on its region
  obtain ⟨t4, ht4, vc, c, hr4, -, -⟩ := RepProducer.rep_run s q₂ g.edges.length
  have r4 := BitMachineStackRun.run ιRK
    (Sum.elim (Y n p s q₁ q₂ w Q k mX mY word g 0 output)
      (Sum.elim (PublicGraphEndpointMachine.resultBank g hg)
        (Sum.elim (RepProducer.R0 s q₂ g.edges.length) (fun _ => []))))
    RepProducer.repProg
    (⟨some RepProducer.repStart, RepProducer.repCtl, RepProducer.R0 s q₂ g.edges.length⟩ :
      TM2.Cfg (fun _ : RepProducer.RK => Bool) _ _) t4
  rw [hr4] at r4
  simp only [stackCfg] at r4
  rw [bank_RK, bank_RK] at r4
  obtain ⟨a3, ha3, R3⟩ := BitMachineRawSequence.runs e2 repL
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)))
    RepProducer.repStart f2 _ RepProducer.repCtl vc _ _ _ a2 t4 R2 r4
  -- (E) install the quotient in the master decode cell 1
  let T4 : JT5 → List Bool := Sum.elim (Y n p s q₁ q₂ w Q k mX mY word g 0 output)
    (Sum.elim (PublicGraphEndpointMachine.resultBank g hg)
      (Sum.elim (Sum.elim (RepProducer.fin1 s q₂ g.edges.length)
        (ETHParameterScaleMachineLogCopy.afterLog
          (RepProducer.u (12 * s * g.edges.length)) c).stk) (fun _ => [])))
  have hsrc : T4 (cpE 0 0) = List.replicate (quot s q₂ g.edges.length) true := rfl
  have hdE : T4 (cpE 0 1) = [] := by
    change preJHm g 0 0 output (mC zR) = []
    rw [preJHm_zR]; rfl
  obtain ⟨t5, ht5, v5, hr5⟩ := CopyAll.all_run cpE
    (by intro i j h; fin_cases i; fin_cases j; cases h)
    (by intro i j h; fin_cases i; fin_cases j; cases h)
    (by intro i j _; fin_cases i; fin_cases j; rfl)
    T4 (by intro i; fin_cases i; rfl) (quot s q₂ g.edges.length)
    (by intro i; fin_cases i; show (T4 (cpE 0 0)).length ≤ _; rw [hsrc, List.length_replicate]) none
  have hD5 : CopyAll.done cpE 1 T4 =
      Sum.elim (Y n p s q₁ q₂ w Q k mX mY word g (quot s q₂ g.edges.length) output)
        (MSfin g hg s q₂ c) := by
    funext x
    by_cases hx : x = hj (mC zR)
    · subst hx
      change CopyAll.done cpE 1 T4 (cpE 0 1) = _
      rw [CopyAll.done_dst cpE (by intro i j _; fin_cases i; fin_cases j; rfl) T4 0, hsrc, hdE,
        List.append_nil]
      change _ = preJHm g (quot s q₂ g.edges.length) 0 output (mC zR)
      rw [preJHm_zR]
    · rw [CopyAll.done_off cpE T4 x (by intro j h; fin_cases j; exact hx h.symm)]
      rcases x with (((o | (a | f)) | pq) | tk) | ms
      · change SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word o =
          SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word o
        rfl
      · change preJHm g 0 0 output a = preJHm g (quot s q₂ g.edges.length) 0 output a
        exact preJHm_off g _ 0 output a (fun h => hx (by rw [h]; rfl))
      · change ([] : List Bool) = []
        rfl
      · change ([] : List Bool) = []
        rfl
      · change ([] : List Bool) = []
        rfl
      · change MSfin g hg s q₂ c ms = MSfin g hg s q₂ c ms
        rfl
  rw [hD5] at hr5
  obtain ⟨a4, ha4, R4⟩ := BitMachineRawSequence.runs e3 (CopyAll.prog cpE)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)))) (.inl ⟨0, by omega⟩)
    f3 _ (none : Option Bool) v5 _ _ _ a3 t5 R3 hr5
  refine ⟨a4, ?_, _, c, R4⟩
  unfold preBd
  omega

end

#print axioms preJH0_zR
#print axioms preJHm_zR
#print axioms preJH0_off
#print axioms preJHm_off
#print axioms pre_run

end Paper2.RepJoin
