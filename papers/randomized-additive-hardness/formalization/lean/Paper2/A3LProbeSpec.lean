import Paper2.A3LProbe

/-!
# Unit 3 lift, segment 1 (spec): hProbe = `Run.DecideSpec` for the generator-outcome bit, Mid1 ∧ Checks → Mid2

Lane `owner:a-h-a3-lift-2` (private, 26 September 2026). Paper A, lock v12.
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.A3Assembly.Lift

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2
open SourceProfileParameters SourceRecursiveNoSampling TotalFiniteConstructorScratch

/-- A lifted run, with the exact exit bank described cell by cell. -/
theorem lift_run {K J L V : Type} [DecidableEq K] [DecidableEq J] (ι : K ↪ J) (foreign : J → List Bool)
    (P : L → TM2.Stmt (fun _ : K => Bool) L V) (l0 : Option L) (v0 : V) (T0 : K → List Bool) (t : ℕ)
    (l1 : Option L) (v1 : V) (T1 : K → List Bool)
    (h : ((advance P)^[t]) ⟨l0, v0, T0⟩ = ⟨l1, v1, T1⟩) (hT : ∀ k, T0 k = foreign (ι k)) :
    ∃ U : J → List Bool, ((advance (liftP ι P))^[t]) ⟨l0, v0, foreign⟩ = ⟨l1, v1, U⟩ ∧
      (∀ j, (¬ ∃ k, ι k = j) → U j = foreign j) ∧ (∀ k, U (ι k) = T1 k) := by
  have hr := BitMachineStackRun.run ι foreign P ⟨l0, v0, T0⟩ t
  rw [h] at hr
  simp only [stackCfg] at hr
  rw [bank_eq_self ι foreign T0 hT] at hr
  exact ⟨bank ι foreign T1, hr, fun j hj => bank_outside ι foreign T1 j hj,
    fun k => bank_at ι foreign T1 k⟩

variable (FS : Type) [Fintype FS] [DecidableEq FS]

theorem cpP_sd (i j : Fin NS) : cpP FS i 0 ≠ cpP FS j 1 := by
  simp [cpP, ιOS, ιPO, (pos_injective FS).eq_iff]

theorem cpP_zd (i j : Fin NS) : cpP FS i 2 ≠ cpP FS j 1 := by
  simp [cpP, ιPO, flag₂, (pos_injective FS).eq_iff]

theorem cpP_dd (i j : Fin NS) (h : cpP FS i 1 = cpP FS j 1) : i = j := by
  have h' : ιPO FS (eS.symm i) = ιPO FS (eS.symm j) := h
  exact eS.symm.injective ((ιPO FS).injective h')

theorem cpP_dst (x : SuccessOrient.Stack) : cpP FS (eS x) 1 = ιPO FS x := by
  show ιPO FS (eS.symm (eS x)) = _
  rw [Equiv.symm_apply_apply]

theorem cpP_src (x : SuccessOrient.Stack) : cpP FS (eS x) 0 = ιOS FS x := by
  show ιOS FS (eS.symm (eS x)) = _
  rw [Equiv.symm_apply_apply]

/-- The probe's exit predicate: Mid2 (A3LLayout, unchanged) together with the `Checks` condition that held on
entry (carried so that the none branch, whose precondition is `Mid2C ∧ ¬ Good`, still knows `Checks`). -/
def Mid2C (Δ : ℕ) (γ : ℚ) (CM EM : ℕ) : Run.Pred Δ γ (a FS) := fun g hg hn k t S =>
  Mid2 FS Δ γ CM EM g hg hn k t S ∧ Run.ChecksCond Δ γ g hg hn k t

theorem ιPO_ne_flag₂ (y : SuccessOrient.Stack) : ιPO FS y ≠ flag₂ FS := by
  simp [ιPO, flag₂, (pos_injective FS).eq_iff]

/-- **Segment 1 (hProbe).** Under Mid1 and `Checks`, the fixed probe program halts within
`PC·(n+2)^(PE(k+1))` with the ACTUAL generator-outcome bit `b₂` (read from the admitted run's final control)
at the head of `flag₂`, `b₂ = true ↔ Good`, and exit bank exactly Mid2 (flag₂ = [b₂], probe region blank,
everything else as in Mid1), with encoded size within the same bound. -/
theorem hProbe_spec (Δ : ℕ) (γ : ℚ) (CM EM : ℕ) :
    Run.DecideSpec Δ γ (a FS) (pProg FS) pStart pCtl (flag₂ FS)
      (fun g hg hn k t S => Mid1 FS Δ γ CM EM g hg hn k t S ∧ Run.ChecksCond Δ γ g hg hn k t)
      (Mid2C FS Δ γ (PC FS CM) (PE EM)) (Good Δ γ) (PC FS CM) (PE EM) := by
  intro g hg hn k hH t S hpre
  obtain ⟨⟨⟨b, Z, hS⟩, hsz⟩, hc⟩ := hpre
  haveI : NeZero g.vertices := ⟨by omega⟩
  -- the bank S, cell by cell
  have hSf : S (flag₂ FS) = [] := by
    rw [hS]
    exact layoutBank_inl FS (Wrap.inputBank Δ γ g hg hn k t)
      (region FS (startCanon Δ γ g hg hn k t) ![[b], [], []] Z) (.inl 1)
  have hSOS : ∀ x, S (ιOS FS x) = startCanon Δ γ g hg hn k t x := by
    intro x
    rw [hS]
    exact layoutBank_inl FS (Wrap.inputBank Δ γ g hg hn k t)
      (region FS (startCanon Δ γ g hg hn k t) ![[b], [], []] Z) (.inr (.inl x))
  have hSPO : ∀ x, S (ιPO FS x) = [] := by
    intro x
    rw [hS]
    exact layoutBank_inl FS (Wrap.inputBank Δ γ g hg hn k t)
      (region FS (startCanon Δ γ g hg hn k t) ![[b], [], []] Z) (.inr (.inr (.inl x)))
  obtain ⟨I, hIdef⟩ : ∃ I, I = (BitMachineBankCodec.encode S).length := ⟨_, rfl⟩
  -- stage 1: the copies master → probe region
  obtain ⟨tc, htc, vc, hcopy⟩ := CopyAll.all_run (cpP FS) (cpP_sd FS) (cpP_zd FS) (cpP_dd FS) S
    (fun _ => hSf) I (fun i => hIdef ▸ BitMachineBankCodec.word_length_le_encode S _) none
  obtain ⟨S1, hS1def⟩ : ∃ S1, S1 = CopyAll.done (cpP FS) NS S := ⟨_, rfl⟩
  rw [← hS1def] at hcopy
  have hS1PO : ∀ x, S1 (ιPO FS x) = startCanon Δ γ g hg hn k t x := by
    intro x
    rw [hS1def, ← cpP_dst FS x, CopyAll.done_dst (cpP FS) (cpP_dd FS) S (eS x), cpP_src, cpP_dst,
      hSOS, hSPO, List.append_nil]
  have hS1off : ∀ j, (∀ y, ιPO FS y ≠ j) → S1 j = S j := by
    intro j hj
    rw [hS1def]
    exact CopyAll.done_off (cpP FS) S j (fun i => hj _) NS
  -- stage 2: the admitted decision run on the physical tape, lifted into the probe region
  obtain ⟨td, htd, d, G, -, -, hrun, hout⟩ := SamplerFallbackJoin.every_tape_halts_no_preload
    g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
    (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
    (outerWidth (Nat.clog 2 g.vertices))
    (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
    (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k
    (sourceRows (Nat.clog 2 g.vertices)
      (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
    (sourceCols (Nat.clog 2 g.vertices)
      (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
    hn (pos_p _) (SourceProfiles.width_ge_four _) (pos_q1 _) (pos_q2 _) (pos_w _) (pos_Q _ _ _ _ _)
    (tapeOf Δ γ g hg hn k hc t)
  rw [tapeOf_word] at hrun
  obtain ⟨T2, hL2, hT2out, -⟩ := lift_run (ιPP FS) S1 SamplerFallbackJoin.program _ _ _ _ _ _ _ hrun
    (fun x => by rw [ιPP_apply, hS1PO]; rfl)
  obtain ⟨tsp, htsp, hsp⟩ := Dispatch.sp_run (liftP (ιPP FS) SamplerFallbackJoin.program)
    SuccessOrient.status (flag₂ FS) _ _ _ _ _ _ hL2
  obtain ⟨T3, hT3def⟩ : ∃ T3, T3 = Function.update T2 (flag₂ FS)
      (SuccessOrient.status (SamplerParameterJoin.startControl,
        (CodeFallbackFullJoin.prepControl, d.var)) :: T2 (flag₂ FS)) := ⟨_, rfl⟩
  rw [← hT3def] at hsp
  have hT2f : T2 (flag₂ FS) = [] := by
    rw [hT2out _ (by rintro ⟨p, hp⟩; exact ιPO_ne_flag₂ FS _ hp),
      hS1off _ (fun y => ιPO_ne_flag₂ FS y), hSf]
  -- stage 3: clear the probe region
  obtain ⟨tcl, htcl, vcl, hclr⟩ := ClearAll.all_run (csP FS) (csP_inj FS)
    (BitMachineBankCodec.encode T3).length T3
    (fun _ => BitMachineBankCodec.word_length_le_encode T3 _) none
  obtain ⟨S', hS'def⟩ : ∃ S', S' = ClearAll.clearFrom (csP FS) 0 T3 := ⟨_, rfl⟩
  rw [← hS'def] at hclr
  -- composition (two charged handoffs)
  obtain ⟨t23, ht23, h23⟩ := BitMachineRawSequence.runs (dProg FS) (ClearAll.prog (csP FS))
    (.inl SamplerFallbackJoin.startLabel) (⟨0, by omega⟩ : Fin (NS + 1))
    SamplerFallbackJoin.startControl _ (none : Option Bool) vcl S1 T3 S' tsp tcl hsp hclr
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs (CopyAll.prog (cpP FS)) (tailP FS)
    (.inl ⟨0, by omega⟩) (BitMachineRawSequence.leftLabel (.inl SamplerFallbackJoin.startLabel))
    (none : Option Bool) vc (SamplerFallbackJoin.startControl, (none : Option Bool)) _ S S1 S'
    tc t23 hcopy h23
  have hr' : ((advance (pProg FS))^[T]) ⟨some pStart, pCtl, S⟩ =
      ⟨none, ((none : Option Bool), (SamplerFallbackJoin.startControl, vcl)), S'⟩ := hr
  -- the exit bank
  have hclr_in : ∀ y, S' (ιPO FS y) = [] := by
    intro y
    rw [hS'def]
    simp only [ClearAll.clearFrom]
    rw [if_pos ⟨eS y, Nat.zero_le _, by simp [csP]⟩]
  have hclr_out : ∀ j, (∀ y, ιPO FS y ≠ j) → S' j = T3 j := by
    intro j hj
    rw [hS'def]
    simp only [ClearAll.clearFrom]
    rw [if_neg]
    rintro ⟨i, -, hi⟩
    exact hj _ hi
  have hPOne : ∀ (x : W FS ⊕ Fin 3), (∀ y, x ≠ .inl (.inr (.inr (.inl y)))) →
      ∀ y, ιPO FS y ≠ pos FS x := by
    intro x hx y h
    exact hx y ((pos_injective FS) h).symm
  have hoff : ∀ (x : W FS ⊕ Fin 3), (∀ y, x ≠ .inl (.inr (.inr (.inl y)))) →
      x ≠ .inl (.inl 1) → S' (pos FS x) = S (pos FS x) := by
    intro x hx h1
    have hk := hPOne x hx
    rw [hclr_out _ hk, hT3def, Function.update_of_ne (show pos FS x ≠ flag₂ FS from fun h => h1 ((pos_injective FS) h))]
    rw [hT2out _ (by rintro ⟨p, hp⟩; exact hk _ hp), hS1off _ hk]
  have hflag : S' (flag₂ FS) = [SuccessOrient.status (SamplerParameterJoin.startControl,
      (CodeFallbackFullJoin.prepControl, d.var))] := by
    rw [hclr_out _ (fun y => ιPO_ne_flag₂ FS y), hT3def, Function.update_self, hT2f]
  have key : ∀ x, S' (pos FS x) = layoutBank FS (Wrap.inputBank Δ γ g hg hn k t)
      (region FS (startCanon Δ γ g hg hn k t) ![[b], [SuccessOrient.status
        (SamplerParameterJoin.startControl, (CodeFallbackFullJoin.prepControl, d.var))], []] Z)
      (pos FS x) := by
    intro x
    rcases x with (c | y | y | y | y | y | z) | i
    · fin_cases c
      · rw [hoff _ (by intro y h; cases h) (by simp), hS, layoutBank_inl, layoutBank_inl]; rfl
      · rw [layoutBank_inl]; exact hflag
      · rw [hoff _ (by intro y h; cases h) (by simp), hS, layoutBank_inl, layoutBank_inl]; rfl
    · rw [hoff _ (by intro y h; cases h) (by intro h; cases h), hS, layoutBank_inl, layoutBank_inl]; rfl
    · rw [layoutBank_inl]; exact hclr_in y
    · rw [hoff _ (by intro y h; cases h) (by intro h; cases h), hS, layoutBank_inl, layoutBank_inl]; rfl
    · rw [hoff _ (by intro y h; cases h) (by intro h; cases h), hS, layoutBank_inl, layoutBank_inl]; rfl
    · rw [hoff _ (by intro y h; cases h) (by intro h; cases h), hS, layoutBank_inl, layoutBank_inl]; rfl
    · rw [hoff _ (by intro y h; cases h) (by intro h; cases h), hS, layoutBank_inl, layoutBank_inl]; rfl
    · rw [hoff _ (by intro y h; cases h) (by intro h; cases h), hS, layoutBank_inr, layoutBank_inr]
  -- the outcome bit is the actual outcome
  have hstat : SuccessOrient.status (SamplerParameterJoin.startControl,
      (CodeFallbackFullJoin.prepControl, d.var)) = (genOut Δ γ g hg hn k hc t).isSome := by
    change CodeFallbackAllOutcomes.Outcome _ _ (genOut Δ γ g hg hn k hc t) d at hout
    cases hres : genOut Δ γ g hg hn k hc t with
    | none =>
      rw [hres] at hout
      obtain ⟨a', wc, hd⟩ := hout
      subst hd
      rfl
    | some bytes =>
      rw [hres] at hout
      obtain ⟨a', hd, -, -⟩ := hout
      subst hd
      rfl
  have hiff : SuccessOrient.status (SamplerParameterJoin.startControl,
      (CodeFallbackFullJoin.prepControl, d.var)) = true ↔ Good Δ γ g hg hn k t := by
    rw [hstat]
    constructor
    · intro h; exact ⟨hc, h⟩
    · rintro ⟨hc', h⟩; exact h
  -- clock and size
  have hN : 1 ≤ g.vertices + 2 := by omega
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = (g.vertices + 2) ^ (PE EM * (k + 1)) := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by rw [hQdef]; exact Nat.one_le_pow _ _ hN
  have hMQ : (g.vertices + 2) ^ (EM * (k + 1)) ≤ Q := by
    rw [hQdef]; exact Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (le_max_left _ _))
  have hIQ : I ≤ CM * Q := by rw [hIdef]; exact hsz.trans (Nat.mul_le_mul_left _ hMQ)
  have htdQ : td ≤ Q := by
    have hpc := Clocks.probe_clock_HA3 (n := g.vertices) (m := g.edges.length) Δ γ hc k
    have hp2 : (g.vertices + 2) ^ ((2 * FallbackNoPreloadRun.noPreloadExponent) * (k + 1)) ≤ Q := by
      rw [hQdef]; exact Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (le_max_right _ _))
    have := htd.trans hpc
    omega
  have htspQ : tsp ≤ 2 * Q := by omega
  have htcQ : tc ≤ Ac CM * Q := by
    unfold Ac
    exact lin1 tc I (2 * NS) (3 * NS + 1) CM Q hQ1 hIQ (htc.trans (le_of_eq (by ring)))
  have hS1Q : (BitMachineBankCodec.encode S1).length ≤ A1 FS CM * Q := by
    unfold A1
    apply lin2 _ I tc (2 * (a FS + 3) * PSc FS) CM (Ac CM) Q hIQ htcQ
    have h := size_run (CopyAll.prog (cpP FS)) ⟨some (.inl ⟨0, by omega⟩), none, S⟩ tc
    rw [hcopy] at h
    rw [hIdef]
    unfold PSc
    calc _ ≤ _ := h
      _ = _ := by ring
  have hT3Q : (BitMachineBankCodec.encode T3).length ≤ A3 FS CM * Q := by
    unfold A3
    apply lin2 _ _ tsp (2 * (a FS + 3) * PSd FS) (A1 FS CM) 2 Q hS1Q htspQ
    have h := size_run (Dispatch.spProg (liftP (ιPP FS) SamplerFallbackJoin.program)
      SuccessOrient.status (flag₂ FS)) ⟨some (.inl SamplerFallbackJoin.startLabel),
      SamplerFallbackJoin.startControl, S1⟩ tsp
    rw [hsp] at h
    unfold PSd dProg
    calc _ ≤ _ := h
      _ = _ := by ring
  have htclQ : tcl ≤ Al FS CM * Q := by
    unfold Al
    exact lin1 tcl _ NS (NS + 1) (A3 FS CM) Q hQ1 hT3Q (htcl.trans (le_of_eq (by ring)))
  have hTQ : T ≤ AT FS CM * Q := by
    unfold AT
    rw [add_mul, add_mul]
    generalize Ac CM * Q = X at htcQ ⊢
    generalize Al FS CM * Q = Y at htclQ ⊢
    omega
  have hS'Q : (BitMachineBankCodec.encode S').length ≤ PC FS CM * Q := by
    have h1 : (BitMachineBankCodec.encode S').length ≤ (CM + 2 * (a FS + 3) * PSp FS * AT FS CM) * Q := by
      apply lin2 _ I T (2 * (a FS + 3) * PSp FS) CM (AT FS CM) Q hIQ hTQ
      have h := size_run (pProg FS) ⟨some pStart, pCtl, S⟩ T
      rw [hr'] at h
      rw [hIdef]
      unfold PSp
      calc _ ≤ _ := h
        _ = _ := by ring
    refine h1.trans (Nat.mul_le_mul_right _ ?_)
    unfold PC; omega
  have hTPC : T ≤ PC FS CM * Q := hTQ.trans (Nat.mul_le_mul_right _ (by unfold PC; omega))
  rw [← hQdef]
  refine ⟨T, _, S', SuccessOrient.status (SamplerParameterJoin.startControl,
    (CodeFallbackFullJoin.prepControl, d.var)), hTPC, hr', ?_, hiff, ?_⟩
  · rw [hflag]; rfl
  · refine ⟨⟨⟨b, _, Z, bank_ext FS _ _ key⟩, ?_⟩, hc⟩
    rw [← hQdef]
    exact hS'Q

end

end Paper2.A3Assembly.Lift

#print axioms Paper2.A3Assembly.Lift.lift_run
#print axioms Paper2.A3Assembly.Lift.hProbe_spec
