import EthInapproximability.CurrentPaper.QSuffixJoin

/-! One fixed six-phase arithmetic controller, from the unary edge-count
word and live writer bin count to the actual q₂ word at writer cell 56. -/

namespace EthInapproximability.CurrentPaper.QArithmeticJoined

open Turing BitMachineEncoding
noncomputable section

def program := BitMachineRawSequence.program
  QProductJoined.program QSuffixJoin.program
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
  QProductJoined.initial QSuffixJoin.initial

def initial := (QProductJoined.initial,QSuffixJoin.initial)

def cost (s e : ℕ) : ℕ :=
  QProductJoined.cost s e + QSuffixJoin.cost (12*s*e) + 1

theorem run (S : QProduct.Stack → List Bool) (s e : ℕ)
    (hs : S QProduct.s = List.replicate s true)
    (he : S QProduct.edge = List.replicate e true)
    (h0 : S (QProduct.temp 0) = [])
    (h1 : S (QProduct.temp 1) = [])
    (h2 : S (QProduct.temp 2) = [])
    (h3 : S (QProduct.temp 3) = [])
    (h4 : S (QProduct.temp 4) = [])
    (h5 : S (QProduct.temp 5) = [])
    (h6 : S (QProduct.temp 6) = [])
    (h7 : S (QProduct.temp 7) = [])
    (h8 : S (QProduct.temp 8) = [])
    (hlog : ∀ k : QLog.Local, S (QLog.logSlots k) = [])
    (hq : S QProduct.q = []) :
    ∃ t ≤ cost s e,
      ∃ F : QProduct.Stack → List Bool,
        ((advance program)^[t])
          (⟨some (BitMachineRawSequence.leftLabel QProductJoined.start),
            initial,S⟩ : TM2.Cfg (fun _ : QProduct.Stack => Bool) _ _) =
          ⟨none,initial,F⟩ ∧
        F QProduct.q =
          List.replicate (2^Nat.clog 2 (12*s*e)) true ∧
        (∀ j : GraphCountBridge.Stack,
          j ≠ (.inr (56 : Fin 64)) → F (.inl j) = S (.inl j)) := by
  let P := QProduct.secondBank S s e
  obtain ⟨tp,htp,hprod⟩ := QProductJoined.run S s e
    hs he h0 h1 h2 h3 h4 h5
  have hn : P (QProduct.temp 5) =
      List.replicate (12*s*e) true := by
    simp [P,QProduct.secondBank]
  have hlogP : ∀ k : QLog.Local, P (QLog.logSlots k) = [] := by
    intro k
    simpa [P,QProduct.secondBank,QProduct.seeded,
      QProduct.firstBank,QProduct.temp,QLog.logSlots,QProduct.log]
      using hlog k
  have h6P : P (QProduct.temp 6) = [] := by
    simpa [P,QProduct.secondBank,QProduct.seeded,
      QProduct.firstBank,QProduct.temp] using h6
  have h7P : P (QProduct.temp 7) = [] := by
    simpa [P,QProduct.secondBank,QProduct.seeded,
      QProduct.firstBank,QProduct.temp] using h7
  have h8P : P (QProduct.temp 8) = [] := by
    simpa [P,QProduct.secondBank,QProduct.seeded,
      QProduct.firstBank,QProduct.temp] using h8
  have hqP : P QProduct.q = [] := by
    simpa [P,QProduct.secondBank,QProduct.seeded,
      QProduct.firstBank,QProduct.temp,QProduct.q] using hq
  obtain ⟨ts,hts,F,hsuffix,hout,hframe⟩ :=
    QSuffixJoin.run P (12*s*e) hn hlogP h6P h7P h8P hqP
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    QProductJoined.program QSuffixJoin.program
    QProductJoined.start
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    QProductJoined.initial QProductJoined.initial
    QSuffixJoin.initial QSuffixJoin.initial
    S P F tp ts
    (by simpa only [P] using hprod)
    (by simpa only [P] using hsuffix)
  refine ⟨t,?_,F,by simpa only [program,initial] using hr,hout,?_⟩
  · dsimp [cost]; omega
  · intro j hj
    have hP : P (.inl j) = S (.inl j) := by
      simp [P,QProduct.secondBank,QProduct.seeded,
        QProduct.firstBank,QProduct.temp]
    exact (hframe j hj).trans hP

#print axioms run

end
end EthInapproximability.CurrentPaper.QArithmeticJoined
