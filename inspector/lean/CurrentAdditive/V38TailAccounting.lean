import CurrentAdditive.V38AmbientFull

noncomputable section
namespace CurrentAdditive.V38TablePrinter.Ambient

open EthInapproximability.CurrentPaper
open EncodedCommunication
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoLookup Paper2.YaoSourceCodec Paper2.YaoMachine
open Paper2.UnaryFieldListParserScratch

def writerCopyBudget {v e : ℕ} (t d : ℕ)
    (edges : Fin e → Fin (2^t*2^t) ↪ Fin v) : ℕ :=
  let b := paddedEdgeBits e
  let H := 2^b
  let K := 2^t*2^t
  let R2 := (2^d)^2
  2*(H^(2^(t-1))+R2+H+(tokens (List.ofFn (flatten edges))).length+
    K+R2*(H*(K+1))+H*(K+1)+rowCount v b t+columnCount b t d)+18

def headerCopyBudget (v b t d : ℕ) : ℕ :=
  let R := rowCount v b t
  let C := columnCount b t d
  2*(R+C+(2*b+4*t+2)+R*C)+8

def headerRunBudget (v b t d : ℕ) : ℕ :=
  let R := rowCount v b t
  let C := columnCount b t d
  let B := 2*b+4*t+2
  UnaryBinaryEncoding.coefficient*((R+1)^2+(C+1)^2+(B+1)^2)+
    2*(natField R++natField C++natField B).length+5

def preparedBudget {v e : ℕ} (t d : ℕ)
    (edges : Fin e → Fin (2^t*2^t) ↪ Fin v) : ℕ :=
  writerCopyBudget t d edges + canonicalTableClockCoefficient *
    (canonicalCellSize t d edges+1)^12 +
    headerCopyBudget v (paddedEdgeBits e) t d +
    headerRunBudget v (paddedEdgeBits e) t d +5

theorem writer_copy_cost {v e : ℕ} (t N d modulus : ℕ)
    (edges : Fin e → Fin (2^t*2^t) ↪ Fin v)
    (S : Cell t N → List Bool)
    (hcap : S (.selector 1) =
      List.replicate ((2^(paddedEdgeBits e))^(2^(t-1))) true)
    (hR2 : S (.square 3) = List.replicate ((2^d)^2) true)
    (hH : S (.source (sN 6)) = List.replicate (2^(paddedEdgeBits e)) true)
    (hbody : S (.source (sN 1)) = tokens (List.ofFn (flatten edges)))
    (hK : S (.source (sN 9)) = List.replicate (2^t*2^t) true)
    (hfield : S (.field (CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.printerSlots
      CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
      bankBits (paddedEdgeBits e) t d modulus)
    (hn : S (.width 3) =
      List.replicate (2^(paddedEdgeBits e)*(2^t*2^t+1)) true)
    (hr : S (.dimensions 5) = List.replicate (rowCount v (paddedEdgeBits e) t) true)
    (hc : S (.dimensions 7) = List.replicate (columnCount (paddedEdgeBits e) t d) true) :
    CopyFill.fillCost (writerJobs t N) S = writerCopyBudget t d edges := by
  simp [CopyFill.fillCost, writerJobs, hcap,hR2,hH,hbody,hK,hfield,hn,hr,hc,
    bankBits_length, writerCopyBudget] <;> ring

theorem header_copy_cost {v e : ℕ} (t N d modulus : ℕ)
    (edges : Fin e → Fin (2^t*2^t) ↪ Fin v)
    (S : Cell t N → List Bool)
    (hr : S (.dimensions 5) = List.replicate (rowCount v (paddedEdgeBits e) t) true)
    (hc : S (.dimensions 7) = List.replicate (columnCount (paddedEdgeBits e) t d) true)
    (ht : S (.threshold 1) = List.replicate (2*paddedEdgeBits e+4*t+2) true) :
    CopyFill.fillCost (headerJobs t N) (writerOutputBank t N d modulus edges S) =
      headerCopyBudget v (paddedEdgeBits e) t d := by
  obtain ⟨_,_,hR,hC,hB⟩ := writerOutputBank_header_inputs t N d modulus edges S
  have hbits := writerOutputBank_bits t N d modulus edges S
  simp only [CopyFill.fillCost, headerJobs, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  rw [hR, hC, hB, hr, hc, ht, hbits]
  simp [headerCopyBudget, table, CurrentAdditive.V38Executable.table,
    Paper2.YaoMaterialization.tabulate_length] <;> ring

#print axioms writer_copy_cost
#print axioms header_copy_cost
end CurrentAdditive.V38TablePrinter.Ambient
