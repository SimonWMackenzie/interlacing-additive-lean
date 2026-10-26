import Paper2.A3LSucc

/-!
# Unit 3 lift, segment 2 (spec): hSucc = `Run.BranchSpec` of the success chain from Mid2 ∧ Good

Lane `owner:a-h-a3-lift-2` (private, 26 September 2026). Paper A, lock v12.
-/

set_option maxHeartbeats 32000000
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
open Paper2.HeaderJoin (JH wOut)
open Paper2.SuccessInstall (mC)
open Paper2.SuccessGraph (preJHm zG zM)

variable (FS : Type) [Fintype FS] [DecidableEq FS]

theorem cpS_sd (i j : Fin 1) : cpS FS i 0 ≠ cpS FS j 1 := by
  simp [cpS, pk, ιS, sMap, RepJoin.hj, mCzG_ne_wOut, (pos_injective FS).eq_iff]

theorem cpS_zd (i j : Fin 1) : cpS FS i 2 ≠ cpS FS j 1 := by
  simp [cpS, ιS, sMap, sReg, RepJoin.hj, RepJoin.sc5, mCzG_ne_wOut, (pos_injective FS).eq_iff]

theorem cpS_dd (i j : Fin 1) (_ : cpS FS i 1 = cpS FS j 1) : i = j := Subsingleton.elim _ _

/-- **Segment 2 (hSucc).** Under Mid2 and Good (the success outcome), the fixed success program halts within
`SC·(n+2)^(SE(k+1))` with `outputBits` in the common output cell and final encoded bank within the same bound. -/
theorem hSucc_spec (Δ : ℕ) (γ : ℚ) (CM EM : ℕ) :
    Run.BranchSpec Δ γ (a FS) (sProg FS) sStart sCtl (outJ FS)
      (fun g hg hn k t S => Mid2C FS Δ γ CM EM g hg hn k t S ∧ Good Δ γ g hg hn k t)
      (SC FS CM) (SE EM) := by
  intro g hg hn k hH t S hpre
  obtain ⟨⟨⟨⟨b₁, b₂, Z, hS⟩, hsz⟩, -⟩, ⟨hc, hsome⟩⟩ := hpre
  haveI : NeZero g.vertices := ⟨by omega⟩
  haveI : NeZero (width (Nat.clog 2 g.vertices)) :=
    ⟨by have := SourceProfiles.width_ge_four (Nat.clog 2 g.vertices); omega⟩
  haveI : NeZero (width (Nat.clog 2 g.vertices) - 2) := ⟨(pos_q1 _).ne'⟩
  haveI : NeZero (outerWidth (Nat.clog 2 g.vertices)) := ⟨(pos_q2 _).ne'⟩
  haveI : NeZero (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices)) :=
    ⟨(pos_w _).ne'⟩
  haveI : NeZero (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ) := ⟨(pos_Q _ _ _ _ _).ne'⟩
  obtain ⟨bytes, hbytes⟩ := Option.isSome_iff_exists.mp hsome
  have hR := RepJoin.success_run_rep g hg hn Δ γ k hc t bytes [] hbytes
  obtain ⟨ys, xs, -, hbeq, -, tR, htR, v, d, G, F, Fk, c, hrun, hF, -, -, -, -, -, -⟩ := hR
  subst hbeq
  -- the bank S, cell by cell
  have hS0 : S (pk FS 0) = EncodedGraph.encode g := by
    rw [hS, pk, layoutBank_inr]; rfl
  have hSout : S (outJ FS) = [] := by
    rw [hS]
    exact layoutBank_inl FS (Wrap.inputBank Δ γ g hg hn k t)
      (region FS (startCanon Δ γ g hg hn k t) ![[b₁], [b₂], []] Z) (.inl 2)
  have hSOS : ∀ o, S (ιOS FS o) = startCanon Δ γ g hg hn k t o := by
    intro o
    rw [hS]
    exact layoutBank_inl FS (Wrap.inputBank Δ γ g hg hn k t)
      (region FS (startCanon Δ γ g hg hn k t) ![[b₁], [b₂], []] Z) (.inr (.inl o))
  have hSreg : ∀ x, S (pos FS (.inl (sReg FS x))) = [] := by
    intro x
    rw [hS]
    exact layoutBank_inl FS (Wrap.inputBank Δ γ g hg hn k t)
      (region FS (startCanon Δ γ g hg hn k t) ![[b₁], [b₂], []] Z) (sReg FS x)
  obtain ⟨I, hIdef⟩ : ∃ I, I = (BitMachineBankCodec.encode S).length := ⟨_, rfl⟩
  have hgI : (EncodedGraph.encode g).length ≤ I := by
    rw [hIdef, ← hS0]; exact BitMachineBankCodec.word_length_le_encode S _
  -- stage 1: the single charged copy
  have hGne : RepJoin.hj (mC zG) ≠ RepJoin.hj wOut := by
    intro h; exact mCzG_ne_wOut (by simpa [RepJoin.hj] using h)
  have hSG : S (ιS FS (RepJoin.hj (mC zG))) = [] := by
    rw [ιS_hj FS _ mCzG_ne_wOut]; exact hSreg _
  obtain ⟨tc, htc, vc, hcopy⟩ := CopyAll.all_run (cpS FS) (cpS_sd FS) (cpS_zd FS) (cpS_dd FS) S
    (fun _ => hSreg RepJoin.sc5) I (fun _ => hIdef ▸ BitMachineBankCodec.word_length_le_encode S _)
    none
  obtain ⟨S2, hS2def⟩ : ∃ S2, S2 = CopyAll.done (cpS FS) 1 S := ⟨_, rfl⟩
  rw [← hS2def] at hcopy
  have hS2G : S2 (ιS FS (RepJoin.hj (mC zG))) = EncodedGraph.encode g := by
    rw [hS2def]
    change CopyAll.done (cpS FS) 1 S (cpS FS 0 1) = _
    rw [CopyAll.done_dst (cpS FS) (cpS_dd FS) S 0]
    change S (pk FS 0) ++ S (ιS FS (RepJoin.hj (mC zG))) = _
    rw [hS0, hSG, List.append_nil]
  have hS2off : ∀ x, x ≠ RepJoin.hj (mC zG) → S2 (ιS FS x) = S (ιS FS x) := by
    intro x hx
    rw [hS2def]
    exact CopyAll.done_off (cpS FS) S _ (fun _ h => hx ((ιS FS).injective h).symm) 1
  -- stage 2: the admitted success chain, lifted
  have hT : ∀ x, (Sum.elim (Sum.elim (Sum.elim (Sum.elim
      (SuccessOrient.startBank g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
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
        ((select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t))
      (Sum.elim (preJHm g 0 0 []) (fun _ => []))) (fun _ => [])) (fun _ => []))
      (fun _ => []) : RepJoin.JT5 → List Bool) x = S2 (ιS FS x) := by
    intro x
    rcases x with (((o | (a' | y)) | p) | tk) | ms
    · rw [show (Sum.inl (Sum.inl (Sum.inl (Sum.inl o))) : RepJoin.JT5) = RepJoin.os o from rfl,
        hS2off _ (by simp [RepJoin.os, RepJoin.hj]), ιS_os, hSOS]
      rfl
    · by_cases haG : a' = mC zG
      · subst haG
        change preJHm g 0 0 [] (mC zG) = S2 (ιS FS (RepJoin.hj (mC zG)))
        rw [hS2G, preJHm_zG]
      · change preJHm g 0 0 [] a' = S2 (ιS FS (RepJoin.hj a'))
        rw [preJHm_blank g a' haG,
          hS2off _ (by intro h; exact haG (by simpa [RepJoin.hj] using h))]
        by_cases haw : a' = wOut
        · subst haw; rw [ιS_out]; exact hSout.symm
        · rw [ιS_hj FS a' haw]; exact (hSreg _).symm
    · rw [hS2off _ (by simp [RepJoin.hj])]
      exact (hSreg _).symm
    · rw [hS2off _ (by simp [RepJoin.hj])]
      exact (hSreg _).symm
    · rw [hS2off _ (by simp [RepJoin.hj])]
      exact (hSreg _).symm
    · rw [hS2off _ (by simp [RepJoin.hj])]
      exact (hSreg _).symm
  obtain ⟨U, hL2, -, hUin⟩ := lift_run (ιS FS) S2 RepJoin.repFull _ _ _ _ _ _ _ hrun hT
  obtain ⟨T, hT', hr⟩ := BitMachineRawSequence.runs (CopyAll.prog (cpS FS))
    (liftP (ιS FS) RepJoin.repFull) (.inl ⟨0, by omega⟩)
    (BitMachineRawSequence.leftLabel RepJoin.preStart) (none : Option Bool) vc
    (RepJoin.preCtl, RepJoin.fullCtl) v S S2 U tc tR hcopy hL2
  have hr' : ((advance (sProg FS))^[T]) ⟨some sStart, sCtl, S⟩ =
      ⟨none, ((none : Option Bool), v), U⟩ := hr
  have hout : U (outJ FS) = EncodedSelectedOutput.outputBits hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t := by
    rw [← ιS_out FS, hUin]
    exact hF.trans (List.append_nil _)
  -- clock
  have hN : 1 ≤ g.vertices + 2 := by omega
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = (g.vertices + 2) ^ (SE EM * (k + 1)) := ⟨_, rfl⟩
  obtain ⟨Q1, hQ1def⟩ : ∃ Q1, Q1 = (g.vertices + 2) ^ (max EM 14 * (k + 1)) := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by rw [hQdef]; exact Nat.one_le_pow _ _ hN
  have hQ11 : 1 ≤ Q1 := by rw [hQ1def]; exact Nat.one_le_pow _ _ hN
  have hQ1Q : Q1 ^ 4 ≤ Q := by
    rw [hQ1def, hQdef, ← pow_mul]
    apply Nat.pow_le_pow_right hN
    have : 4 * max EM 14 ≤ SE EM := le_max_left _ _
    nlinarith
  have hQ1le : Q1 ≤ Q := by
    have : Q1 ≤ Q1 ^ 4 := by
      calc Q1 = Q1 ^ 1 := (pow_one _).symm
        _ ≤ Q1 ^ 4 := Nat.pow_le_pow_right hQ11 (by norm_num)
    omega
  have hMQ1 : (g.vertices + 2) ^ (EM * (k + 1)) ≤ Q1 := by
    rw [hQ1def]; exact Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (le_max_left _ _))
  have hIQ1 : I ≤ CM * Q1 := by rw [hIdef]; exact hsz.trans (Nat.mul_le_mul_left _ hMQ1)
  have hIQ : I ≤ CM * Q := hIQ1.trans (Nat.mul_le_mul_left _ hQ1le)
  obtain ⟨-, -, hs7, -, hq7, -, -, hm7, -⟩ := Paper2.SuccessClock.scalar_caps
    (n := g.vertices) (m := g.edges.length) (Nat.clog 2 g.vertices) Δ γ hc
  have h7 : 2 ^ (7 * Nat.clog 2 g.vertices) ≤ Q1 := by
    have h := Paper2.A3Assembly.Clock.two_pow_mul_clog_le 7 0 g.vertices
    simp only [zero_add, mul_one] at h
    refine h.trans ?_
    rw [hQ1def]
    apply Nat.pow_le_pow_right hN
    have : 14 ≤ max EM 14 := le_max_right _ _
    calc 2 * 7 = 14 * 1 := by norm_num
      _ ≤ max EM 14 * (k + 1) := Nat.mul_le_mul this (by omega)
  obtain ⟨B, hBdef⟩ : ∃ B, B = I + 3 * 2 ^ (7 * Nat.clog 2 g.vertices) + 1 := ⟨_, rfl⟩
  have hBQ1 : B ≤ (CM + 4) * Q1 := by
    rw [hBdef, add_mul]
    generalize CM * Q1 = X at hIQ1
    omega
  have hpre := preBd_le g (width (Nat.clog 2 g.vertices)) (outerWidth (Nat.clog 2 g.vertices)) B
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hB4 : PBc * B ^ 4 ≤ PBc * (CM + 4) ^ 4 * Q := by
    have h1 : B ^ 4 ≤ ((CM + 4) * Q1) ^ 4 := Nat.pow_le_pow_left hBQ1 4
    rw [mul_pow] at h1
    have h2 : (CM + 4) ^ 4 * Q1 ^ 4 ≤ (CM + 4) ^ 4 * Q := Nat.mul_le_mul_left _ hQ1Q
    calc PBc * B ^ 4 ≤ PBc * ((CM + 4) ^ 4 * Q) := Nat.mul_le_mul_left _ (h1.trans h2)
      _ = PBc * (CM + 4) ^ 4 * Q := by ring
  have hcs := Clocks.success_full_clock_HA3 (Nat.clog 2 g.vertices) Δ γ g hg hc
    (ParameterizedCanonicalSource.rep (Nat.clog 2 g.vertices) g.edges.length)
    (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep (Nat.clog 2 g.vertices)
      (Fin g.edges.length) hc.1)
    (CanonicalDefaultSource.canonicalDefaultTails (Nat.clog 2 g.vertices) g.vertices
      (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ)
      hn (NeZero.pos _) (NeZero.pos _))
    k xs ys rfl
  have hES : (g.vertices + 2) ^ ((2 * (FallbackNoPreloadRun.noPreloadExponent +
      Paper2.SuccessClock2Pre.preExponent + Paper2.SuccessClock.entryExponent 2601 + 65)) * (k + 1)) ≤ Q := by
    rw [hQdef]
    exact Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (le_max_right (4 * max EM 14) _))
  have hcs' : _ ≤ Q := le_trans hcs (by rw [one_mul]; exact hES)
  have hTk : T ≤ SCk CM * Q := by
    have e : SCk CM * Q = 2 * (CM * Q) + PBc * (CM + 4) ^ 4 * Q + 8 * Q := by unfold SCk; ring
    rw [e]
    generalize PBc * (CM + 4) ^ 4 * Q = X at hB4
    generalize CM * Q = Y at hIQ
    generalize RepJoin.preBd g (width (Nat.clog 2 g.vertices)) (outerWidth (Nat.clog 2 g.vertices)) = P
      at hpre htR
    generalize PBc * B ^ 4 = P4 at hpre hB4
    omega
  -- size
  have hsize := size_run (sProg FS) ⟨some sStart, sCtl, S⟩ T
  rw [hr'] at hsize
  rw [← hQdef]
  refine ⟨T, _, U, ?_, hr', hout, ?_⟩
  · exact hTk.trans (Nat.mul_le_mul_right _ (by unfold SC; omega))
  · have h1 : (BitMachineBankCodec.encode U).length ≤ (CM + 2 * (a FS + 3) * PSs FS * SCk CM) * Q := by
      apply lin2 _ I T (2 * (a FS + 3) * PSs FS) CM (SCk CM) Q hIQ hTk
      rw [hIdef]
      unfold PSs
      calc _ ≤ _ := hsize
        _ = _ := by ring
    exact h1.trans (Nat.mul_le_mul_right _ (by unfold SC; omega))

end

end Paper2.A3Assembly.Lift

#print axioms Paper2.A3Assembly.Lift.preJHm_blank
#print axioms Paper2.A3Assembly.Lift.preBd_le
#print axioms Paper2.A3Assembly.Lift.hSucc_spec
