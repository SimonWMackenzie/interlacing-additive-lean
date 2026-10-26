import CurrentAdditive.QuarticTMFront
import CurrentAdditive.QuarticLayout

/-! Eleven physical copies install the exact quartic numeric values in the
canonical success-orientation start bank. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront.Install27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.RandomizedSchedule
open SourceRecursiveNoSampling

abbrev Stack := Packet27.Stack
abbrev SO := SuccessOrient.Stack

def src (i : Fin 11) : Stack :=
  ![Packet27.graph (Graph27.new (LQ27.wc (.inl LProducer.q2C))),
    Packet27.graph (Graph27.new (LQ27.wc (.inl LProducer.q1C))),
    Packet27.graph (Graph27.new (LQ27.wc (.inl LProducer.sC))),
    Packet27.graph (Graph27.new (LQ27.wc (.inl LProducer.nC))),
    Packet27.graph (Graph27.new (LQ27.wc (.inr (.inl 9)))),
    Packet27.graph (Graph27.new (LQ27.qc (.inl 24))),
    Packet27.graph (Graph27.new (LQ27.wc (.inl LProducer.pC))),
    Packet27.packet 1,
    Packet27.tm (TMFront.mc 13), Packet27.tm (TMFront.mc 10),
    Packet27.packet 2] i

def dst (i : Fin 11) : Stack := Packet27.so (FullFront.dC i)

def copies (i : Fin 11) : Fin 3 ↪ Stack :=
  ⟨![src i, dst i, Packet27.scratch], by
    intro x y h
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      simp_all [src, dst, Packet27.graph, Packet27.tm, Packet27.so,
        Packet27.packet, Packet27.scratch]⟩

theorem src_ne_dst (i j : Fin 11) : copies i 0 ≠ copies j 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [copies, src, dst, Packet27.graph, Packet27.tm,
      Packet27.so, Packet27.packet]

theorem scratch_ne_dst (i j : Fin 11) : copies i 2 ≠ copies j 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [copies, dst, Packet27.scratch, Packet27.so]

theorem dst_injective (i j : Fin 11) (h : copies i 1 = copies j 1) : i = j := by
  have h' : FullFront.dC i = FullFront.dC j := by
    simpa [copies, dst, Packet27.so] using h
  exact FullFront.dC_inj i j h'

def afterInstall (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (FT : TMFront.TK → List Bool) (FM : TMFront.MK → List Bool)
    (n p s q₁ q₂ w Q mX mY : ℕ) : Stack → List Bool :=
  Sum.elim (Packet27.graphExit g hg FLold FQold FLnew FQnew)
    (Sum.elim (Sum.elim FT (Sum.elim FM (fun _ => [])))
      (Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
        (Sum.elim (FullFront.X0 g k word) (fun _ => []))))

theorem doneC (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (FT : TMFront.TK → List Bool) (FM : TMFront.MK → List Bool)
    (n p s q₁ q₂ w Q mX mY : ℕ)
    (hv : ∀ i, TM27.afterTM g hg k word FLold FQold FLnew FQnew FT FM
      (copies i 0) =
        ![List.replicate q₂ true, List.replicate q₁ true,
          List.replicate s true, List.replicate n true,
          List.replicate w true, List.replicate Q true,
          List.replicate p true, List.replicate k true,
          List.replicate mX true, List.replicate mY true, word] i) :
    CopyAll.done copies 11
      (TM27.afterTM g hg k word FLold FQold FLnew FQnew FT FM) =
    afterInstall g hg k word FLold FQold FLnew FQnew FT FM
      n p s q₁ q₂ w Q mX mY := by
  obtain ⟨c12, c16, c17, c18, c31, c32, c63, c64, cX, cY, cD⟩ :=
    StartInstall.startBank_cells n p s q₁ q₂ w Q k mX mY word
  funext z
  by_cases hz : ∃ j, copies j 1 = z
  · obtain ⟨j, rfl⟩ := hz
    rw [CopyAll.done_dst copies dst_injective _ j, hv j]
    have he : TM27.afterTM g hg k word FLold FQold FLnew FQnew FT FM
      (copies j 1) = [] := rfl
    rw [he, List.append_nil]
    change _ = SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word
      (FullFront.dC j)
    fin_cases j
    · exact c12.symm
    · exact c16.symm
    · exact c17.symm
    · exact c18.symm
    · exact c31.symm
    · exact c32.symm
    · exact c63.symm
    · exact c64.symm
    · exact cX.symm
    · exact cY.symm
    · exact cD.symm
  · rw [CopyAll.done_off copies _ z (fun j h => hz ⟨j, h⟩)]
    rcases z with z | (y | (y | (y | y)))
    · rfl
    · rfl
    · show [] = SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word y
      have hy : y ∉ StartInstall.cells := by
        intro hmem
        simp only [StartInstall.cells, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h | h | h | h | h | h | h | h | h | h <;> subst h
        · exact hz ⟨0, rfl⟩
        · exact hz ⟨1, rfl⟩
        · exact hz ⟨2, rfl⟩
        · exact hz ⟨3, rfl⟩
        · exact hz ⟨4, rfl⟩
        · exact hz ⟨5, rfl⟩
        · exact hz ⟨6, rfl⟩
        · exact hz ⟨7, rfl⟩
        · exact hz ⟨8, rfl⟩
        · exact hz ⟨9, rfl⟩
        · exact hz ⟨10, rfl⟩
      rw [StartInstall.startBank_off _ _ _ _ _ _ _ _ _ _ _ y hy,
        StartBlank.blank_nil]
    · rfl
    · rfl

end
end Paper2.CurrentAdditive.QuarticNumericFront.Install27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Install27.doneC
