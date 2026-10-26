import EthInapproximability.CurrentPaper.QProduct
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Charged finite-control sequence of both multipliers and the fixed
twelve-push seed. -/

namespace EthInapproximability.CurrentPaper.QProductJoined

open Turing BitMachineEncoding
noncomputable section

namespace Raw
abbrev program := @BitMachineRawSequence.program
abbrev runs := @BitMachineRawSequence.runs
abbrev leftLabel := @BitMachineRawSequence.leftLabel
end Raw
def P12 := Raw.program QProduct.firstProgram QProduct.seedProgram () false ()
def program := Raw.program P12 QProduct.secondProgram
  MatrixAddressMachine.Label.outer (false,()) false

def start : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label MatrixAddressMachine.Label Unit)
    MatrixAddressMachine.Label :=
  Raw.leftLabel (Raw.leftLabel MatrixAddressMachine.Label.outer)
def initial := ((false,()),false)

def cost (s e : ℕ) : ℕ :=
  MatrixAddressMachine.exactTime s e 0 + 1 +
  MatrixAddressMachine.exactTime (s*e) 12 0 + 2

theorem run (S : QProduct.Stack → List Bool) (s e : ℕ)
    (hs : S QProduct.s = List.replicate s true)
    (he : S QProduct.edge = List.replicate e true)
    (h0 : S (QProduct.temp 0) = [])
    (h1 : S (QProduct.temp 1) = [])
    (h2 : S (QProduct.temp 2) = [])
    (h3 : S (QProduct.temp 3) = [])
    (h4 : S (QProduct.temp 4) = [])
    (h5 : S (QProduct.temp 5) = []) :
    ∃ t ≤ cost s e,
      ((advance program)^[t])
        (⟨some start,initial,S⟩ :
          TM2.Cfg (fun _ : QProduct.Stack => Bool) _ _) =
        ⟨none,initial,QProduct.secondBank S s e⟩ := by
  have hr1 := QProduct.first_run S s e hs he h0 h1 h2 h3
  have hseed : (QProduct.firstBank S s e) (QProduct.temp 4) = [] := by
    simpa [QProduct.firstBank,QProduct.temp] using h4
  have hrseed := QProduct.seed_run (QProduct.firstBank S s e) hseed
  obtain ⟨u,hu,hr12⟩ := Raw.runs QProduct.firstProgram QProduct.seedProgram
    MatrixAddressMachine.Label.outer () false false () ()
    S (QProduct.firstBank S s e)
    (QProduct.seeded (QProduct.firstBank S s e))
    (MatrixAddressMachine.exactTime s e 0) 1 hr1 hrseed
  have hr2 := QProduct.second_run S s e h0 h1 h2 h5
  obtain ⟨v,hv,hr123⟩ := Raw.runs P12 QProduct.secondProgram
    (Raw.leftLabel MatrixAddressMachine.Label.outer)
    MatrixAddressMachine.Label.outer
    (false,()) (false,()) false false
    S (QProduct.seeded (QProduct.firstBank S s e))
    (QProduct.secondBank S s e)
    u (MatrixAddressMachine.exactTime (s*e) 12 0)
    (by simpa only [P12] using hr12) hr2
  refine ⟨v,?_,?_⟩
  · dsimp [cost]; omega
  · simpa only [program,start,initial] using hr123

#print axioms run

end
end EthInapproximability.CurrentPaper.QProductJoined
