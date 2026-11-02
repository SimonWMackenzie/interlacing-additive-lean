import CurrentAdditive.QuarticNumericRawPoints
import CurrentAdditive.QuarticPrepSize
import Paper2.CopyAll

/-! A private physical lift of the v27 numeric packet into the H_A3 work bank. -/

namespace Paper2.CurrentAdditive.QuarticFrontLift

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 16384

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticNumericFront
open Paper2.CurrentAdditive.QuarticDispatchSpec
open Paper2.CurrentAdditive.QuarticLayout

abbrev FS := Packet27.Stack
noncomputable instance : Fintype FS := inferInstance

abbrev K := Fin (Lift.a FS + 3)

def packetCopies (i : Fin 3) : Fin 3 ↪ K :=
  ⟨![Lift.pk FS i, Lift.ιFS FS (Packet27.packet i),
      Lift.ιFS FS Packet27.scratch], by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp_all [Lift.pk, Lift.ιFS, Packet27.packet,
        Packet27.scratch]⟩

noncomputable def soCopies (i : Fin (Fintype.card SuccessOrient.Stack)) :
    Fin 3 ↪ K :=
  ⟨![Lift.ιFS FS (Packet27.so ((Fintype.equivFin SuccessOrient.Stack).symm i)),
      Lift.ιOS FS ((Fintype.equivFin SuccessOrient.Stack).symm i),
      Lift.ιFS FS Packet27.scratch], by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp_all [Lift.ιFS, Lift.ιOS, Lift.pos, Packet27.so,
        Packet27.scratch]⟩

def input (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) : K → List Bool :=
  Wrap.widen (Lift.a FS) (FullFront.X0 g k word)

def loaded (P : Fin 3 → List Bool) : K → List Bool :=
  Lift.layoutBank FS P
    (Lift.region FS (fun _ => []) ![[], [], []] (Packet27.initial P))

theorem packet_src_ne_dst (i j : Fin 3) :
    packetCopies i 0 ≠ packetCopies j 1 := by
  intro h
  have hs : (packetCopies i 0).val = Lift.a FS + i.val := by
    simp [packetCopies, Lift.pk, Lift.pos, finSumFinEquiv_apply_right]
  have hd : (packetCopies j 1).val < Lift.a FS := by
    simp [packetCopies, Lift.ιFS, Lift.pos, finSumFinEquiv_apply_left]
  have hv := congrArg Fin.val h
  omega

theorem packet_scratch_ne_dst (i j : Fin 3) :
    packetCopies i 2 ≠ packetCopies j 1 := by
  intro h
  have hh : Packet27.scratch = Packet27.packet j :=
    (Lift.ιFS FS).injective (by simpa only [packetCopies] using h)
  cases hh

theorem packet_dst_inj (i j : Fin 3)
    (h : packetCopies i 1 = packetCopies j 1) : i = j := by
  have hh : Packet27.packet i = Packet27.packet j :=
    (Lift.ιFS FS).injective (by simpa only [packetCopies] using h)
  simpa [Packet27.packet] using hh

theorem packet_copy_run (P : Fin 3 → List Bool) :
    ∃ t ≤ 3 * (2 * (BitMachineBankCodec.encode P).length + 3) + 1,
      ∃ v,
      ((advance (CopyAll.prog packetCopies))^[t])
        (⟨some (.inl ⟨0, by omega⟩), none,
          Wrap.widen (Lift.a FS) P⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, v, CopyAll.done packetCopies 3 (Wrap.widen (Lift.a FS) P)⟩ := by
  apply CopyAll.all_run packetCopies packet_src_ne_dst packet_scratch_ne_dst
    packet_dst_inj (Wrap.widen (Lift.a FS) P)
  · intro i
    change (Wrap.widen (Lift.a FS) P)
      (Lift.ιFS FS Packet27.scratch) = []
    rw [Lift.widen_eq FS P]
    change Lift.layoutBank FS P (fun _ => []) (Lift.pos FS (.inl _)) = []
    rw [Lift.layoutBank_inl]
  · intro i
    change ((Wrap.widen (Lift.a FS) P) (Lift.pk FS i)).length ≤
      (BitMachineBankCodec.encode P).length
    rw [Lift.widen_eq FS P]
    change (Lift.layoutBank FS P (fun _ => []) (Lift.pos FS (.inr i))).length ≤ _
    rw [Lift.layoutBank_inr]
    exact BitMachineBankCodec.word_length_le_encode P i

theorem loaded_packet (P : Fin 3 → List Bool) (i : Fin 3) :
    loaded P (Lift.pk FS i) = P i := by
  exact Lift.layoutBank_inr FS P _ i

theorem loaded_raw (P : Fin 3 → List Bool) (x : FS) :
    loaded P (Lift.ιFS FS x) = Packet27.initial P x := by
  simpa only [loaded, Lift.ιFS, Lift.region] using
    (Lift.layoutBank_inl FS P
      (Lift.region FS (fun _ => []) ![[], [], []] (Packet27.initial P))
      (.inr (.inr (.inr (.inr (.inr (.inr x)))))))

theorem loaded_master (P : Fin 3 → List Bool) (x : SuccessOrient.Stack) :
    loaded P (Lift.ιOS FS x) = [] := by
  simpa only [loaded, Lift.ιOS, Lift.region] using
    (Lift.layoutBank_inl FS P
      (Lift.region FS (fun _ => []) ![[], [], []] (Packet27.initial P))
      (.inr (.inl x)))

theorem packet_initial_off (P : Fin 3 → List Bool) (x : FS)
    (hx : ∀ i : Fin 3, Packet27.packet i ≠ x) :
    Packet27.initial P x = [] := by
  rcases x with x | (x | (x | (x | x)))
  · rfl
  · rfl
  · rfl
  · exfalso
    exact hx x rfl
  · rfl

theorem packet_copied_raw (P : Fin 3 → List Bool) (x : FS) :
    CopyAll.done packetCopies 3 (Wrap.widen (Lift.a FS) P)
      (Lift.ιFS FS x) = Packet27.initial P x := by
  by_cases hx : ∃ i : Fin 3, Packet27.packet i = x
  · obtain ⟨i, rfl⟩ := hx
    have h := CopyAll.done_dst packetCopies packet_dst_inj
      (Wrap.widen (Lift.a FS) P) i
    change CopyAll.done packetCopies 3 (Wrap.widen (Lift.a FS) P)
      (Lift.ιFS FS (Packet27.packet i)) =
        (Wrap.widen (Lift.a FS) P) (Lift.pk FS i) ++
          (Wrap.widen (Lift.a FS) P) (Lift.ιFS FS (Packet27.packet i)) at h
    rw [h, Lift.widen_eq FS P]
    have hsrc := Lift.layoutBank_inr FS P (fun _ => []) i
    have hdst := Lift.layoutBank_inl FS P (fun _ => [])
      (.inr (.inr (.inr (.inr (.inr (.inr (Packet27.packet i)))))))
    rw [show Lift.pk FS i = Lift.pos FS (.inr i) from rfl, hsrc]
    rw [show Lift.ιFS FS (Packet27.packet i) =
      Lift.pos FS (.inl (.inr (.inr (.inr (.inr (.inr (.inr (Packet27.packet i))))))))
      from rfl, hdst]
    simp [Packet27.initial, Packet27.packet]
  · have hoff : ∀ i, packetCopies i 1 ≠ Lift.ιFS FS x := by
      intro i h
      apply hx
      refine ⟨i, ?_⟩
      exact (Lift.ιFS FS).injective (by simpa only [packetCopies] using h)
    rw [CopyAll.done_off packetCopies _ _ hoff 3]
    rw [Lift.widen_eq FS P]
    have hblank := Lift.layoutBank_inl FS P (fun _ => [])
      (.inr (.inr (.inr (.inr (.inr (.inr x))))))
    change Lift.layoutBank FS P (fun _ => []) (Lift.ιFS FS x) = [] at hblank
    rw [hblank]
    exact (packet_initial_off P x (by intro i h; exact hx ⟨i, h⟩)).symm

def workRaw (x : FS) : Lift.W FS :=
  .inr (.inr (.inr (.inr (.inr (.inr x)))))

theorem loaded_work (P : Fin 3 → List Bool) (x : Lift.W FS) :
    loaded P (Lift.pos FS (.inl x)) =
      Lift.region FS (fun _ => []) ![[], [], []] (Packet27.initial P) x := by
  exact Lift.layoutBank_inl FS P _ x

theorem loaded_work_off (P : Fin 3 → List Bool) (x : Lift.W FS)
    (hx : ∀ i : Fin 3, workRaw (Packet27.packet i) ≠ x) :
    loaded P (Lift.pos FS (.inl x)) = [] := by
  rw [loaded_work]
  rcases x with x | (x | (x | (x | (x | (x | x)))))
  · fin_cases x <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact packet_initial_off P x (by intro i h; exact hx i (by simp [workRaw, h]))

theorem packet_loaded (P : Fin 3 → List Bool) :
    CopyAll.done packetCopies 3 (Wrap.widen (Lift.a FS) P) = loaded P := by
  apply Lift.bank_ext FS
  intro x
  rcases x with x | i
  · by_cases hx : ∃ j : Fin 3, workRaw (Packet27.packet j) = x
    · obtain ⟨j, rfl⟩ := hx
      change CopyAll.done packetCopies 3 (Wrap.widen (Lift.a FS) P)
        (Lift.ιFS FS (Packet27.packet j)) =
          loaded P (Lift.ιFS FS (Packet27.packet j))
      rw [packet_copied_raw, loaded_raw]
    · have hoff : ∀ j, packetCopies j 1 ≠ Lift.pos FS (.inl x) := by
        intro j h
        have hh : workRaw (Packet27.packet j) = x := by
          have hpos : Lift.pos FS (.inl (workRaw (Packet27.packet j))) =
              Lift.pos FS (.inl x) := by
            simpa only [packetCopies, Lift.ιFS, workRaw] using h
          exact Sum.inl.inj (Lift.pos_injective FS hpos)
        exact hx ⟨j, hh⟩
      rw [CopyAll.done_off packetCopies _ _ hoff 3]
      rw [Lift.widen_eq FS P, Lift.layoutBank_inl]
      exact (loaded_work_off P x (by intro j h; exact hx ⟨j, h⟩)).symm
  · have hoff : ∀ j, packetCopies j 1 ≠ Lift.pk FS i := by
      intro j h; exact packet_src_ne_dst i j h.symm
    change CopyAll.done packetCopies 3 (Wrap.widen (Lift.a FS) P)
      (Lift.pk FS i) = loaded P (Lift.pk FS i)
    rw [CopyAll.done_off packetCopies _ _ hoff 3]
    rw [Lift.widen_eq FS P]
    change Lift.layoutBank FS P (fun _ => []) (Lift.pos FS (.inr i)) = _
    rw [Lift.layoutBank_inr]
    exact (loaded_packet P i).symm

def afterRaw (P : Fin 3 → List Bool) (B : FS → List Bool) : K → List Bool :=
  Lift.layoutBank FS P (Lift.region FS (fun _ => []) ![[], [], []] B)

theorem after_raw_cell (P : Fin 3 → List Bool) (B : FS → List Bool) (x : FS) :
    afterRaw P B (Lift.ιFS FS x) = B x := by
  exact Lift.layoutBank_inl FS P _ (workRaw x)

theorem after_raw_master (P : Fin 3 → List Bool) (B : FS → List Bool)
    (x : SuccessOrient.Stack) : afterRaw P B (Lift.ιOS FS x) = [] := by
  simpa only [afterRaw, Lift.ιOS, Lift.region] using
    (Lift.layoutBank_inl FS P
      (Lift.region FS (fun _ => []) ![[], [], []] B) (.inr (.inl x)))

theorem after_raw_bank (P : Fin 3 → List Bool) (B : FS → List Bool) :
    bank (Lift.ιFS FS) (loaded P) B = afterRaw P B := by
  apply Lift.bank_ext FS
  intro x
  rcases x with x | i
  · rcases x with x | (x | (x | (x | (x | (x | x)))))
    · rw [bank_outside (Lift.ιFS FS) (loaded P) B]
      · rw [loaded_work, afterRaw, Lift.layoutBank_inl]
        fin_cases x <;> rfl
      · rintro ⟨y, hy⟩
        exact nomatch Lift.pos_injective FS hy
    · rw [bank_outside (Lift.ιFS FS) (loaded P) B]
      · rw [loaded_work, afterRaw, Lift.layoutBank_inl]
        rfl
      · rintro ⟨y, hy⟩
        exact nomatch Lift.pos_injective FS hy
    · rw [bank_outside (Lift.ιFS FS) (loaded P) B]
      · rw [loaded_work, afterRaw, Lift.layoutBank_inl]
        rfl
      · rintro ⟨y, hy⟩
        exact nomatch Lift.pos_injective FS hy
    · rw [bank_outside (Lift.ιFS FS) (loaded P) B]
      · rw [loaded_work, afterRaw, Lift.layoutBank_inl]
        rfl
      · rintro ⟨y, hy⟩
        exact nomatch Lift.pos_injective FS hy
    · rw [bank_outside (Lift.ιFS FS) (loaded P) B]
      · rw [loaded_work, afterRaw, Lift.layoutBank_inl]
        rfl
      · rintro ⟨y, hy⟩
        exact nomatch Lift.pos_injective FS hy
    · rw [bank_outside (Lift.ιFS FS) (loaded P) B]
      · rw [loaded_work, afterRaw, Lift.layoutBank_inl]
        rfl
      · rintro ⟨y, hy⟩
        exact nomatch Lift.pos_injective FS hy
    · change bank (Lift.ιFS FS) (loaded P) B (Lift.ιFS FS x) =
        afterRaw P B (Lift.ιFS FS x)
      rw [bank_at (Lift.ιFS FS) (loaded P) B x]
      exact after_raw_cell P B x |>.symm
  · rw [bank_outside (Lift.ιFS FS) (loaded P) B]
    · change loaded P (Lift.pk FS i) = afterRaw P B (Lift.pk FS i)
      rw [loaded_packet]
      exact (Lift.layoutBank_inr FS P _ i).symm
    · rintro ⟨y, hy⟩
      exact nomatch Lift.pos_injective FS hy

def rawProg (Δ : ℕ) (γ : ℚ) :=
  Lift.liftP (Lift.ιFS FS) (Raw27.program Δ γ)

theorem raw_lift_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length) (k : ℕ)
    (tape : (QuarticConstructor.select27 hn
      (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    let P := inputBank27 Δ γ g hg hn k tape
    ∃ T ≤ Raw27.clock g Δ γ k (P 2), ∃ vc, ∃ B : FS → List Bool,
      ((advance (rawProg Δ γ))^[T])
        (⟨some (Raw27.startLabel Δ γ), Raw27.initialControl, loaded P⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, (Packet27.initialControl, (Tail27.ctlBC, vc)), afterRaw P B⟩ ∧
      (∀ x, B (Packet27.so x) =
        QuarticLayout.startCanon27 Δ γ g hg hn k tape x) ∧
      B RawPoints27.nCell = List.replicate g.vertices true ∧
      B RawPoints27.mCell = List.replicate g.edges.length true ∧
      B Packet27.scratch = [] := by
  intro P
  obtain ⟨T, hT, vc, B, hr, hmaster, hnB, hmB, hscratch, -⟩ :=
    RawPoints27.run g hg Δ γ hγ hΔ hn hm k tape
  have hLift := BitMachineStackRun.run (Lift.ιFS FS) (loaded P)
    (Raw27.program Δ γ)
    (⟨some (Raw27.startLabel Δ γ), Raw27.initialControl,
      Packet27.initial (FullFront.X0 g k (P 2))⟩ :
      TM2.Cfg (fun _ : FS => Bool) _ _) T
  have hP : FullFront.X0 g k (P 2) = P := by
    funext i
    fin_cases i <;> rfl
  have hWord : P 2 =
      (QuarticConstructor.select27 hn
        (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits tape := rfl
  rw [← hWord] at hr
  rw [hP] at hr hLift
  rw [hr] at hLift
  have hstart : bank (Lift.ιFS FS) (loaded P) (Packet27.initial P) =
      loaded P := by
    apply bank_eq_self
    intro x
    exact (loaded_raw P x).symm
  have hfinish := after_raw_bank P B
  refine ⟨T, hT, vc, B, ?_, hmaster, hnB, hmB, hscratch⟩
  simpa only [rawProg, stackCfg, hstart, hfinish] using hLift

theorem so_src_ne_dst (i j : Fin (Fintype.card SuccessOrient.Stack)) :
    soCopies i 0 ≠ soCopies j 1 := by
  intro h
  have hh :
      Lift.pos FS (.inl (workRaw
        (Packet27.so ((Fintype.equivFin SuccessOrient.Stack).symm i)))) =
      Lift.pos FS (.inl (.inr (.inl
        ((Fintype.equivFin SuccessOrient.Stack).symm j)))) := by
    simpa only [soCopies, Lift.ιFS, Lift.ιOS, workRaw] using h
  exact nomatch Lift.pos_injective FS hh

theorem so_scratch_ne_dst (i j : Fin (Fintype.card SuccessOrient.Stack)) :
    soCopies i 2 ≠ soCopies j 1 := by
  intro h
  have hh :
      Lift.pos FS (.inl (workRaw Packet27.scratch)) =
      Lift.pos FS (.inl (.inr (.inl
        ((Fintype.equivFin SuccessOrient.Stack).symm j)))) := by
    simpa only [soCopies, Lift.ιFS, Lift.ιOS, workRaw] using h
  exact nomatch Lift.pos_injective FS hh

theorem so_dst_inj (i j : Fin (Fintype.card SuccessOrient.Stack))
    (h : soCopies i 1 = soCopies j 1) : i = j := by
  have hh : (Fintype.equivFin SuccessOrient.Stack).symm i =
      (Fintype.equivFin SuccessOrient.Stack).symm j :=
    (Lift.ιOS FS).injective (by simpa only [soCopies] using h)
  exact (Fintype.equivFin SuccessOrient.Stack).symm.injective hh

theorem so_copy_run (P : Fin 3 → List Bool) (B : FS → List Bool)
    (hscratch : B Packet27.scratch = []) :
    ∃ t ≤ Fintype.card SuccessOrient.Stack *
      (2 * (BitMachineBankCodec.encode (afterRaw P B)).length + 3) + 1,
      ∃ v,
      ((advance (CopyAll.prog soCopies))^[t])
        (⟨some (.inl ⟨0, by omega⟩), none, afterRaw P B⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, v, CopyAll.done soCopies (Fintype.card SuccessOrient.Stack)
          (afterRaw P B)⟩ := by
  apply CopyAll.all_run soCopies so_src_ne_dst so_scratch_ne_dst
    so_dst_inj (afterRaw P B)
  · intro i
    change afterRaw P B (Lift.ιFS FS Packet27.scratch) = []
    rw [after_raw_cell]
    exact hscratch
  · intro i
    change (afterRaw P B (Lift.ιFS FS
      (Packet27.so ((Fintype.equivFin SuccessOrient.Stack).symm i)))).length ≤
        (BitMachineBankCodec.encode (afterRaw P B)).length
    exact BitMachineBankCodec.word_length_le_encode (afterRaw P B) _

theorem so_done_master (P : Fin 3 → List Bool) (B : FS → List Bool)
    (x : SuccessOrient.Stack) :
    CopyAll.done soCopies (Fintype.card SuccessOrient.Stack) (afterRaw P B)
      (Lift.ιOS FS x) = B (Packet27.so x) := by
  let i := (Fintype.equivFin SuccessOrient.Stack) x
  have h := CopyAll.done_dst soCopies so_dst_inj (afterRaw P B) i
  have hi : (Fintype.equivFin SuccessOrient.Stack).symm i = x := by
    exact Equiv.symm_apply_apply _ _
  change CopyAll.done soCopies (Fintype.card SuccessOrient.Stack) (afterRaw P B)
      (Lift.ιOS FS ((Fintype.equivFin SuccessOrient.Stack).symm i)) =
      afterRaw P B (Lift.ιFS FS
        (Packet27.so ((Fintype.equivFin SuccessOrient.Stack).symm i))) ++
      afterRaw P B (Lift.ιOS FS
        ((Fintype.equivFin SuccessOrient.Stack).symm i)) at h
  rw [hi, after_raw_cell, after_raw_master, List.append_nil] at h
  exact h

def afterMaster (P : Fin 3 → List Bool) (B : FS → List Bool)
    (st : SuccessOrient.Stack → List Bool) : K → List Bool :=
  Lift.layoutBank FS P (Lift.region FS st ![[], [], []] B)

theorem so_done_layout (P : Fin 3 → List Bool) (B : FS → List Bool)
    (st : SuccessOrient.Stack → List Bool)
    (hmaster : ∀ x, B (Packet27.so x) = st x) :
    CopyAll.done soCopies (Fintype.card SuccessOrient.Stack)
      (afterRaw P B) = afterMaster P B st := by
  apply Lift.bank_ext FS
  intro x
  rcases x with x | i
  · rcases x with x | (x | (x | (x | (x | (x | x)))))
    · have hoff : ∀ j, soCopies j 1 ≠ Lift.pos FS (.inl (.inl x)) := by
        intro j h
        have hh : Lift.pos FS (.inl (.inr (.inl
              ((Fintype.equivFin SuccessOrient.Stack).symm j)))) =
            Lift.pos FS (.inl (.inl x)) := by
          simpa only [soCopies, Lift.ιOS] using h
        exact nomatch Lift.pos_injective FS hh
      rw [CopyAll.done_off soCopies _ _ hoff]
      rw [afterRaw, afterMaster, Lift.layoutBank_inl, Lift.layoutBank_inl]
      fin_cases x <;> rfl
    · change CopyAll.done soCopies (Fintype.card SuccessOrient.Stack)
        (afterRaw P B) (Lift.ιOS FS x) =
        afterMaster P B st (Lift.ιOS FS x)
      rw [so_done_master, hmaster]
      change st x = Lift.layoutBank FS P (Lift.region FS st ![[], [], []] B)
        (Lift.pos FS (.inl (.inr (.inl x))))
      rw [Lift.layoutBank_inl]
      rfl
    · have hoff : ∀ j, soCopies j 1 ≠ Lift.pos FS (.inl (.inr (.inr (.inl x)))) := by
        intro j h
        have hh : Lift.pos FS (.inl (.inr (.inl
              ((Fintype.equivFin SuccessOrient.Stack).symm j)))) =
            Lift.pos FS (.inl (.inr (.inr (.inl x)))) := by
          simpa only [soCopies, Lift.ιOS] using h
        exact nomatch Lift.pos_injective FS hh
      rw [CopyAll.done_off soCopies _ _ hoff]
      rw [afterRaw, afterMaster, Lift.layoutBank_inl, Lift.layoutBank_inl]
      rfl
    · have hoff : ∀ j, soCopies j 1 ≠ Lift.pos FS (.inl (.inr (.inr (.inr (.inl x))))) := by
        intro j h
        have hh : Lift.pos FS (.inl (.inr (.inl
              ((Fintype.equivFin SuccessOrient.Stack).symm j)))) =
            Lift.pos FS (.inl (.inr (.inr (.inr (.inl x))))) := by
          simpa only [soCopies, Lift.ιOS] using h
        exact nomatch Lift.pos_injective FS hh
      rw [CopyAll.done_off soCopies _ _ hoff]
      rw [afterRaw, afterMaster, Lift.layoutBank_inl, Lift.layoutBank_inl]
      rfl
    · have hoff : ∀ j, soCopies j 1 ≠ Lift.pos FS (.inl (.inr (.inr (.inr (.inr (.inl x)))))) := by
        intro j h
        have hh : Lift.pos FS (.inl (.inr (.inl
              ((Fintype.equivFin SuccessOrient.Stack).symm j)))) =
            Lift.pos FS (.inl (.inr (.inr (.inr (.inr (.inl x)))))) := by
          simpa only [soCopies, Lift.ιOS] using h
        exact nomatch Lift.pos_injective FS hh
      rw [CopyAll.done_off soCopies _ _ hoff]
      rw [afterRaw, afterMaster, Lift.layoutBank_inl, Lift.layoutBank_inl]
      rfl
    · have hoff : ∀ j, soCopies j 1 ≠ Lift.pos FS (.inl (.inr (.inr (.inr (.inr (.inr (.inl x))))))) := by
        intro j h
        have hh : Lift.pos FS (.inl (.inr (.inl
              ((Fintype.equivFin SuccessOrient.Stack).symm j)))) =
            Lift.pos FS (.inl (.inr (.inr (.inr (.inr (.inr (.inl x))))))) := by
          simpa only [soCopies, Lift.ιOS] using h
        exact nomatch Lift.pos_injective FS hh
      rw [CopyAll.done_off soCopies _ _ hoff]
      rw [afterRaw, afterMaster, Lift.layoutBank_inl, Lift.layoutBank_inl]
      rfl
    · have hoff : ∀ j, soCopies j 1 ≠ Lift.pos FS (.inl (workRaw x)) := by
        intro j h
        have hh : Lift.pos FS (.inl (.inr (.inl
              ((Fintype.equivFin SuccessOrient.Stack).symm j)))) =
            Lift.pos FS (.inl (workRaw x)) := by
          simpa only [soCopies, Lift.ιOS] using h
        exact nomatch Lift.pos_injective FS hh
      change CopyAll.done soCopies (Fintype.card SuccessOrient.Stack)
        (afterRaw P B) (Lift.pos FS (.inl (workRaw x))) =
        afterMaster P B st (Lift.pos FS (.inl (workRaw x)))
      rw [CopyAll.done_off soCopies _ _ hoff]
      rw [afterRaw, afterMaster, Lift.layoutBank_inl, Lift.layoutBank_inl]
      rfl
  · have hoff : ∀ j, soCopies j 1 ≠ Lift.pk FS i := by
      intro j h
      have hh : Lift.pos FS (.inl (.inr (.inl
            ((Fintype.equivFin SuccessOrient.Stack).symm j)))) =
          Lift.pos FS (.inr i) := by
        simpa only [soCopies, Lift.ιOS, Lift.pk] using h
      exact nomatch Lift.pos_injective FS hh
    change CopyAll.done soCopies (Fintype.card SuccessOrient.Stack)
      (afterRaw P B) (Lift.pk FS i) = afterMaster P B st (Lift.pk FS i)
    rw [CopyAll.done_off soCopies _ _ hoff]
    rw [afterRaw, afterMaster]
    change Lift.layoutBank FS P _ (Lift.pos FS (.inr i)) =
      Lift.layoutBank FS P _ (Lift.pos FS (.inr i))
    rw [Lift.layoutBank_inr, Lift.layoutBank_inr]

def firstProg (Δ : ℕ) (γ : ℚ) :=
  BitMachineRawSequence.program (CopyAll.prog packetCopies)
    (rawProg Δ γ) (Raw27.startLabel Δ γ)
    (none : Option Bool) Raw27.initialControl

def firstCtl := ((none : Option Bool), Raw27.initialControl)

def program (Δ : ℕ) (γ : ℚ) :=
  BitMachineRawSequence.program (firstProg Δ γ)
    (CopyAll.prog soCopies) (.inl ⟨0, by omega⟩)
    firstCtl (none : Option Bool)

def startLabel (Δ : ℕ) (γ : ℚ) :=
  FullFront.labelOfP (program Δ γ)
    (.inl (.inl (.inl ⟨0, by omega⟩)))

def initialControl := (firstCtl, (none : Option Bool))

def copyPacketClock (P : Fin 3 → List Bool) : ℕ :=
  3 * (2 * (BitMachineBankCodec.encode P).length + 3) + 1

def copyMasterClock (P : Fin 3 → List Bool) (B : FS → List Bool) : ℕ :=
  Fintype.card SuccessOrient.Stack *
    (2 * (BitMachineBankCodec.encode (afterRaw P B)).length + 3) + 1

def clock (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (P : Fin 3 → List Bool) (B : FS → List Bool) : ℕ :=
  copyPacketClock P + Raw27.clock g Δ γ k (P 2) +
    copyMasterClock P B + 2

theorem physical_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length) (k : ℕ)
    (tape : (QuarticConstructor.select27 hn
      (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    let P := inputBank27 Δ γ g hg hn k tape
    ∃ T, ∃ v, ∃ B : FS → List Bool,
      T ≤ clock g Δ γ k P B ∧
      ((advance (program Δ γ))^[T])
        (⟨some (startLabel Δ γ), initialControl,
          Wrap.widen (Lift.a FS) P⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, v,
          Lift.layoutBank FS P
            (Lift.region FS (QuarticLayout.startCanon27 Δ γ g hg hn k tape)
              ![[], [], []] B)⟩ ∧
      B RawPoints27.nCell = List.replicate g.vertices true ∧
      B RawPoints27.mCell = List.replicate g.edges.length true := by
  intro P
  obtain ⟨tP, htP, vP, hrP⟩ := packet_copy_run P
  rw [packet_loaded P] at hrP
  obtain ⟨tR, htR, vR, B, hrR, hmaster, hnB, hmB, hsB⟩ :=
    raw_lift_run g hg Δ γ hγ hΔ hn hm k tape
  obtain ⟨tS, htS, vS, hrS⟩ := so_copy_run P B hsB
  rw [so_done_layout P B _ hmaster] at hrS
  obtain ⟨tPR, htPR, hrPR⟩ := BitMachineRawSequence.runs
    (CopyAll.prog packetCopies) (rawProg Δ γ)
    (.inl ⟨0, by omega⟩) (Raw27.startLabel Δ γ)
    (none : Option Bool) vP Raw27.initialControl
    (Packet27.initialControl, (Tail27.ctlBC, vR))
    (Wrap.widen (Lift.a FS) P) (loaded P) (afterRaw P B)
    tP tR hrP hrR
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs
    (firstProg Δ γ) (CopyAll.prog soCopies)
    (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩ : CopyAll.Lab 3))
    (.inl ⟨0, by omega⟩)
    firstCtl ((none : Option Bool), (Packet27.initialControl, (Tail27.ctlBC, vR)))
    (none : Option Bool) vS
    (Wrap.widen (Lift.a FS) P) (afterRaw P B)
    (afterMaster P B (QuarticLayout.startCanon27 Δ γ g hg hn k tape))
    tPR tS hrPR hrS
  refine ⟨T, (firstCtl, vS),
    B, ?_, ?_, hnB, hmB⟩
  · change tR ≤ Raw27.clock g Δ γ k (P 2) at htR
    unfold clock copyPacketClock copyMasterClock at *
    omega
  · simpa only [program, startLabel, FullFront.labelOfP,
      initialControl, afterMaster] using hr

end
end Paper2.CurrentAdditive.QuarticFrontLift

#print axioms Paper2.CurrentAdditive.QuarticFrontLift.physical_run
