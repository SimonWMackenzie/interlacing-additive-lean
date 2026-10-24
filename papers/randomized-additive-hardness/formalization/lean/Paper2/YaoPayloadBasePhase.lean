import Paper2.YaoSelectorSingleJoin

/-! Four fixed preserving unary multiply-add phases on the actual Yao scalar
bank: H*stride, ell*(H*stride)+position, selectorCount*Q, and the final
(selectorCount*Q)*b+relative. The operands are mapped to their retained
physical cells; seven new cells hold zero, two temporary backups, and four
successive results. -/

namespace Paper2.YaoEntryParameterJoin

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.YaoParameterBank
open Paper2.YaoLowerBound
open Paper2.YaoLookup

abbrev PayloadStack (t lambda : ℕ) := SelectorStack t lambda ⊕ Fin 7
abbrev PayloadLabel := Fin 4 × MatrixAddressMachine.Label
abbrev PayloadConfig (t lambda : ℕ) :=
  TM2.Cfg (fun _ : PayloadStack t lambda => Bool) PayloadLabel Bool

def fromJoined (t lambda : ℕ) (j : JoinedStack t lambda) : PayloadStack t lambda :=
  .inl (.inl (.inl j))
def fresh (t lambda : ℕ) (j : Fin 7) : PayloadStack t lambda := .inr j

noncomputable def hCell (t lambda : ℕ) : PayloadStack t lambda :=
  fromJoined t lambda (.inl (.inl (.inr (.inl (ScalarB t lambda).input))))
noncomputable def bCell (t lambda : ℕ) : PayloadStack t lambda :=
  fromJoined t lambda (.inl (.inl (.inl bitsCell)))
noncomputable def countCell (t lambda : ℕ) : PayloadStack t lambda :=
  fromJoined t lambda (.inl (.inl (.inr (.inl (ScalarB t lambda).output))))
def ellCell (t lambda : ℕ) : PayloadStack t lambda :=
  fromJoined t lambda (.inl (.inr 2))
def positionCell (t lambda : ℕ) : PayloadStack t lambda :=
  fromJoined t lambda (.inl (.inr 3))
def qCell (t lambda : ℕ) : PayloadStack t lambda :=
  fromJoined t lambda (.inr 0)
def strideCell (t lambda : ℕ) : PayloadStack t lambda :=
  fromJoined t lambda (.inr 1)

noncomputable def payloadSlot (t lambda : ℕ) (phase : Fin 4) :
    Fin 6 ↪ PayloadStack t lambda where
  toFun := ![
    ![hCell t lambda, strideCell t lambda, fresh t lambda 0,
      fresh t lambda 1, fresh t lambda 2, fresh t lambda 3],
    ![ellCell t lambda, fresh t lambda 3, positionCell t lambda,
      fresh t lambda 1, fresh t lambda 2, fresh t lambda 4],
    ![countCell t lambda, qCell t lambda, fresh t lambda 0,
      fresh t lambda 1, fresh t lambda 2, fresh t lambda 5],
    ![fresh t lambda 5, bCell t lambda, fresh t lambda 4,
      fresh t lambda 1, fresh t lambda 2, fresh t lambda 6]] phase
  inj' := by
    fin_cases phase <;> intro a b h <;>
      fin_cases a <;> fin_cases b <;>
      simp_all [hCell,bCell,countCell,ellCell,positionCell,qCell,strideCell,
        fromJoined,fresh,Fin.ext_iff]

def payloadNext (phase : Fin 4) : Option PayloadLabel :=
  if h : phase.val + 1 < 4 then some (⟨phase.val+1, by omega⟩,.outer) else none

noncomputable def payloadProgram (t lambda : ℕ) (l : PayloadLabel) :
    TM2.Stmt (fun _ : PayloadStack t lambda => Bool) PayloadLabel Bool :=
  BitMachineStackEmbedding.stmt (payloadSlot t lambda l.1)
    (fun k => (l.1,k)) id id (payloadNext l.1)
    (MatrixAddressMachine.program l.2)

noncomputable def payloadRun (t lambda n : ℕ) (c : PayloadConfig t lambda) :=
  ((advance (payloadProgram t lambda))^[n]) c

theorem payload_phase_run (t lambda : ℕ) (phase : Fin 4)
    (row width column : ℕ) (s : Bool)
    (S : PayloadStack t lambda → List Bool)
    (hS : ∀ k : Fin 6, S (payloadSlot t lambda phase k) =
      ![List.replicate row true, List.replicate width true,
        List.replicate column true, [], [],
        S (payloadSlot t lambda phase 5)] k) :
    ∃ steps ≤ MatrixAddressMachine.exactTime row width column,
      payloadRun t lambda steps ⟨some (phase,.outer),s,S⟩ =
        ⟨payloadNext phase,false,
          Function.update S (payloadSlot t lambda phase 5)
            (List.replicate (row*width+column) true ++
              S (payloadSlot t lambda phase 5))⟩ := by
  let ι := payloadSlot t lambda phase
  let q := S (ι 5)
  let input := MatrixAddressMachine.cfg (some .outer) s
    (List.replicate row true) (List.replicate width true)
    (List.replicate column true) [] [] q
  let output := MatrixAddressMachine.cfg none false
    (List.replicate row true) (List.replicate width true)
    (List.replicate column true) [] []
    (List.replicate (row*width+column) true ++ q)
  have hr : ((advance MatrixAddressMachine.program)^[
      MatrixAddressMachine.exactTime row width column]) input = output :=
    MatrixAddressMachine.address_run row width column s q
  have hh : (((advance MatrixAddressMachine.program)^[
      MatrixAddressMachine.exactTime row width column]) input).l = none := by
    rw [hr]
    rfl
  obtain ⟨steps,hsteps,he⟩ := BitMachineStackEmbedding.outputs ι S
    (fun k => (phase,k)) id id (by intro x; rfl)
    (payloadNext phase) MatrixAddressMachine.program
    (payloadProgram t lambda) (by intro l; rfl)
    input (MatrixAddressMachine.exactTime row width column) hh
  rw [hr] at he
  have hbank : BitMachineStackEmbedding.bank ι S input.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    have hk := hS k
    fin_cases k <;> simpa [input,MatrixAddressMachine.cfg,ι,q] using hk.symm
  have hlocal : output.stk = Function.update input.stk 5
      (List.replicate (row*width+column) true ++ q) := by
    funext k
    fin_cases k <;> rfl
  have hfinish : BitMachineStackEmbedding.cfg ι S (fun k => (phase,k))
      id (payloadNext phase) output =
      (⟨payloadNext phase,false,
        Function.update S (ι 5)
          (List.replicate (row*width+column) true ++ q)⟩ :
        PayloadConfig t lambda) := by
    have hstk : BitMachineStackEmbedding.bank ι S output.stk =
        Function.update S (ι 5)
          (List.replicate (row*width+column) true ++ q) := by
      rw [hlocal, BitMachineStackEmbedding.bank_update,hbank]
    exact congrArg (fun X : PayloadStack t lambda → List Bool =>
      (⟨payloadNext phase,false,X⟩ : PayloadConfig t lambda)) hstk
  have hstart : BitMachineStackEmbedding.cfg ι S (fun k => (phase,k))
      id (payloadNext phase) input =
      (⟨some (phase,.outer),s,S⟩ : PayloadConfig t lambda) := by
    change (⟨some (phase,.outer),s,BitMachineStackEmbedding.bank ι S input.stk⟩ :
      PayloadConfig t lambda) = _
    rw [hbank]
  exact ⟨steps,hsteps,by
    change ((advance (payloadProgram t lambda))^[steps]) _ = _
    rw [← hstart]
    exact he.trans hfinish⟩

#print axioms payload_phase_run

def payloadBaseValue (t lambda e ell p : ℕ) : ℕ :=
  selectorCount t (paddedEdgeBits e) lambda * fixedQ t * paddedEdgeBits e +
    ell * (paddedEdgeCount e * fixedK t) + p

/-- Four actual in-bank address passes compute the complete payload base.
The only hypotheses identify *source* scalar cells and initially empty
working cells; there is no supplied desired offset or product. -/
theorem physical_payload_base_phase (t lambda e ell p : ℕ)
    (S₀ : PayloadStack t lambda → List Bool)
    (hH : S₀ (hCell t lambda) = List.replicate (paddedEdgeCount e) true)
    (hK : S₀ (strideCell t lambda) = List.replicate (fixedK t) true)
    (hEll : S₀ (ellCell t lambda) = List.replicate ell true)
    (hP : S₀ (positionCell t lambda) = List.replicate p true)
    (hCount : S₀ (countCell t lambda) =
      List.replicate (selectorCount t (paddedEdgeBits e) lambda) true)
    (hQ : S₀ (qCell t lambda) = List.replicate (fixedQ t) true)
    (hB : S₀ (bCell t lambda) = List.replicate (paddedEdgeBits e) true)
    (hFresh : ∀ j : Fin 7, S₀ (fresh t lambda j) = []) :
    ∃ steps ≤
      MatrixAddressMachine.exactTime (paddedEdgeCount e) (fixedK t) 0 +
      MatrixAddressMachine.exactTime ell (paddedEdgeCount e * fixedK t) p +
      MatrixAddressMachine.exactTime
        (selectorCount t (paddedEdgeBits e) lambda) (fixedQ t) 0 +
      MatrixAddressMachine.exactTime
        (selectorCount t (paddedEdgeBits e) lambda * fixedQ t)
        (paddedEdgeBits e)
        (ell * (paddedEdgeCount e * fixedK t) + p),
      let S₁ := Function.update S₀ (fresh t lambda 3)
        (List.replicate (paddedEdgeCount e * fixedK t) true)
      let S₂ := Function.update S₁ (fresh t lambda 4)
        (List.replicate (ell * (paddedEdgeCount e * fixedK t) + p) true)
      let S₃ := Function.update S₂ (fresh t lambda 5)
        (List.replicate
          (selectorCount t (paddedEdgeBits e) lambda * fixedQ t) true)
      let S₄ := Function.update S₃ (fresh t lambda 6)
        (List.replicate (payloadBaseValue t lambda e ell p) true)
      payloadRun t lambda steps ⟨some (0,.outer),false,S₀⟩ =
        ⟨none,false,S₄⟩ ∧
      S₄ (fresh t lambda 6) =
        List.replicate (payloadBaseValue t lambda e ell p) true := by
  let H := paddedEdgeCount e
  let K := fixedK t
  let B := paddedEdgeBits e
  let Q := fixedQ t
  let C := selectorCount t B lambda
  have hFresh' (j : Fin 7) : S₀ (.inr j) = [] := hFresh j
  have hEll' : S₀ (.inl (.inl (.inl (.inl (.inr 2))))) =
      List.replicate ell true := hEll
  have hP' : S₀ (.inl (.inl (.inl (.inl (.inr 3))))) =
      List.replicate p true := hP
  have hCount' : S₀ (countCell t lambda) = List.replicate C true := hCount
  have hQ' : S₀ (qCell t lambda) = List.replicate Q true := hQ
  have hB' : S₀ (bCell t lambda) = List.replicate B true := hB
  simp only [countCell,qCell,bCell,fromJoined] at hCount' hQ' hB'
  let S₁ := Function.update S₀ (fresh t lambda 3)
    (List.replicate (H*K) true)
  let S₂ := Function.update S₁ (fresh t lambda 4)
    (List.replicate (ell*(H*K)+p) true)
  let S₃ := Function.update S₂ (fresh t lambda 5)
    (List.replicate (C*Q) true)
  let S₄ := Function.update S₃ (fresh t lambda 6)
    (List.replicate (payloadBaseValue t lambda e ell p) true)
  have hs₀ : ∀ k : Fin 6, S₀ (payloadSlot t lambda 0 k) =
      ![List.replicate H true,List.replicate K true,[],[],[],
        S₀ (payloadSlot t lambda 0 5)] k := by
    intro k
    fin_cases k <;> simp [payloadSlot,H,K,hH,hK,hFresh]
  obtain ⟨n₀,hn₀,hr₀⟩ := payload_phase_run t lambda 0 H K 0 false S₀ hs₀
  have he₀ : Function.update S₀ (payloadSlot t lambda 0 5)
      (List.replicate (H*K+0) true ++ S₀ (payloadSlot t lambda 0 5)) = S₁ := by
    simp only [S₁]
    congr 1
    simp [payloadSlot,fresh,hFresh']
  rw [he₀] at hr₀
  have hs₁ : ∀ k : Fin 6, S₁ (payloadSlot t lambda 1 k) =
      ![List.replicate ell true,List.replicate (H*K) true,
        List.replicate p true,[],[],S₁ (payloadSlot t lambda 1 5)] k := by
    intro k
    fin_cases k <;> simp [S₁,payloadSlot,fresh,ellCell,positionCell,
      fromJoined,Function.update,H,K,hEll',hP',hFresh']
  obtain ⟨n₁,hn₁,hr₁⟩ :=
    payload_phase_run t lambda 1 ell (H*K) p false S₁ hs₁
  have he₁ : Function.update S₁ (payloadSlot t lambda 1 5)
      (List.replicate (ell*(H*K)+p) true ++ S₁ (payloadSlot t lambda 1 5)) = S₂ := by
    simp only [S₂]
    congr 1
    simp [S₁,payloadSlot,fresh,Function.update,hFresh']
  rw [he₁] at hr₁
  have hs₂ : ∀ k : Fin 6, S₂ (payloadSlot t lambda 2 k) =
      ![List.replicate C true,List.replicate Q true,[],[],[],
        S₂ (payloadSlot t lambda 2 5)] k := by
    intro k
    fin_cases k <;> simp [S₂,S₁,payloadSlot,fresh,countCell,qCell,
      fromJoined,Function.update,C,Q,hCount',hQ',hFresh']
  obtain ⟨n₂,hn₂,hr₂⟩ := payload_phase_run t lambda 2 C Q 0 false S₂ hs₂
  have he₂ : Function.update S₂ (payloadSlot t lambda 2 5)
      (List.replicate (C*Q+0) true ++ S₂ (payloadSlot t lambda 2 5)) = S₃ := by
    simp only [S₃]
    congr 1
    simp [S₂,S₁,payloadSlot,fresh,Function.update,hFresh']
  rw [he₂] at hr₂
  have hs₃ : ∀ k : Fin 6, S₃ (payloadSlot t lambda 3 k) =
      ![List.replicate (C*Q) true,List.replicate B true,
        List.replicate (ell*(H*K)+p) true,[],[],
        S₃ (payloadSlot t lambda 3 5)] k := by
    intro k
    fin_cases k <;> simp [S₃,S₂,S₁,payloadSlot,fresh,bCell,
      fromJoined,Function.update,C,Q,B,H,K,hB',hFresh']
  obtain ⟨n₃,hn₃,hr₃⟩ :=
    payload_phase_run t lambda 3 (C*Q) B (ell*(H*K)+p) false S₃ hs₃
  have he₃ : Function.update S₃ (payloadSlot t lambda 3 5)
      (List.replicate ((C*Q)*B+(ell*(H*K)+p)) true ++
        S₃ (payloadSlot t lambda 3 5)) = S₄ := by
    simp only [S₄]
    congr 1
    simp [S₃,S₂,S₁,payloadSlot,fresh,Function.update,hFresh',
      payloadBaseValue,C,Q,B,H,K,Nat.mul_assoc,Nat.add_assoc]
  rw [he₃] at hr₃
  have hnext₀ : payloadNext 0 = some (1,.outer) := by decide
  have hnext₁ : payloadNext 1 = some (2,.outer) := by decide
  have hnext₂ : payloadNext 2 = some (3,.outer) := by decide
  have hnext₃ : payloadNext 3 = none := by decide
  rw [hnext₀] at hr₀
  rw [hnext₁] at hr₁
  rw [hnext₂] at hr₂
  rw [hnext₃] at hr₃
  have hadd {x y z : PayloadConfig t lambda} {a b : ℕ}
      (h : payloadRun t lambda a x = y)
      (h' : payloadRun t lambda b y = z) :
      payloadRun t lambda (a+b) x = z := by
    rw [payloadRun, show a+b=b+a by omega,
      Function.iterate_add_apply]
    exact congrArg _ h |>.trans h'
  have hrun := hadd (hadd (hadd hr₀ hr₁) hr₂) hr₃
  refine ⟨n₀+n₁+n₂+n₃,by
    simpa only [H,K,B,Q,C] using
      (show n₀+n₁+n₂+n₃ ≤
        MatrixAddressMachine.exactTime H K 0 +
        MatrixAddressMachine.exactTime ell (H*K) p +
        MatrixAddressMachine.exactTime C Q 0 +
        MatrixAddressMachine.exactTime (C*Q) B (ell*(H*K)+p) by omega),?_⟩
  dsimp only
  refine ⟨hrun,?_⟩
  change (Function.update S₃ (fresh t lambda 6)
    (List.replicate (payloadBaseValue t lambda e ell p) true))
      (fresh t lambda 6) = _
  exact Function.update_self _ _ _

#print axioms physical_payload_base_phase

end Paper2.YaoEntryParameterJoin
