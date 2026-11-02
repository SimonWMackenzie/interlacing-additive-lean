import CurrentAdditive.PhysicalProducer
import CurrentAdditive.GeneralPolynomialClockBound
import CurrentAdditive.V22EdgeCountMachine

namespace CurrentAdditive.V40GraphConstructorFront
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
open EthInapproximability.CurrentPaper EncodedCommunication PhysicalProducer

/-- The same fixed clock writer and bounded simulator are used on every
graph word. Canonical graph counts are preserved by the native parser run. -/
def counted (M : BitMachine.Machine) : Producer where
  machine := GeneralPolynomialClock.machine 9 M
  result := GeneralPolynomialClock.result 9 M
  coefficient := GeneralPolynomialClock.timeCoefficient 9 M
  degree := GeneralPolynomialClock.exponent 9
  outputs x := BitMachine.outputsWithin_mono _
    (GeneralPolynomialClock.outputs_all 9 M x) (GeneralPolynomialClock.time_le 9 M x)

theorem count_fuel (x : List Bool) :
    100*(x.length+1)^3 ≤ GeneralPolynomialFuelPrefix.clockLength (degree:=9) x := by
  have hcoef : 100 ≤ (x.length+2)^7 := by
    have h := Nat.pow_le_pow_left (show 2≤x.length+2 by omega) 7
    norm_num at h
    omega
  calc
    _ ≤ (x.length+2)^7*(x.length+2)^3 :=
      Nat.mul_le_mul hcoef (Nat.pow_le_pow_left (by omega) 3)
    _ = _ := by rw [← pow_add]; rfl

theorem counted_result (M : BitMachine.Machine) (x y : List Bool)
    (h : M.OutputsWithin x y (100*(x.length+1)^3)) :
    (counted M).result x=y := by
  exact BitMachine.outputsWithin_unique (GeneralPolynomialClock.machine 9 M)
    (GeneralPolynomialClock.outputs_all 9 M x)
    (GeneralPolynomialClock.outputs_valid 9 M x y
      (BitMachine.outputsWithin_mono M h (count_fuel x)))

def vertexCount := counted V22GraphVertexMachine.machine
def edgeCount := counted V22EdgeCountMachine.machine
theorem vertex_result (g : EncodedGraph.Graph) (hg : g.Valid) :
    vertexCount.result (EncodedGraph.encode g)=List.replicate g.vertices true :=
  counted_result _ _ _ (V22GraphVertexMachine.outputs g hg)
theorem edge_result (g : EncodedGraph.Graph) (hg : g.Valid) :
    edgeCount.result (EncodedGraph.encode g)=List.replicate g.edges.length true :=
  counted_result _ _ _ (V22EdgeCountMachine.outputs g hg)

def bank2 (A B : Producer) := concat (compose A field) (compose B field)
def bank3 (A B C : Producer) := concat (compose A field)
  (concat (compose B field) (compose C field))
def bank5 (A B C D E : Producer) := concat (compose A field)
  (concat (compose B field) (concat (compose C field)
    (concat (compose D field) (compose E field))))
theorem bank2_result (A B : Producer) (x : List Bool) :
    (bank2 A B).result x=BitMachineBankCodec.encode ![A.result x,B.result x] := by
  simp [bank2,concat,compose,PhysicalProducer.field,BitMachineBankCodec.encode_eq_list]
theorem bank3_result (A B C : Producer) (x : List Bool) :
    (bank3 A B C).result x=BitMachineBankCodec.encode ![A.result x,B.result x,C.result x] := by
  simp [bank3,concat,compose,PhysicalProducer.field,BitMachineBankCodec.encode_eq_list]
theorem bank5_result (A B C D E : Producer) (x : List Bool) :
    (bank5 A B C D E).result x=BitMachineBankCodec.encode
      ![A.result x,B.result x,C.result x,D.result x,E.result x] := by
  simp [bank5,concat,compose,PhysicalProducer.field,BitMachineBankCodec.encode_eq_list]

def input (graph : List Bool) (floor K : Nat) :=
  BitMachineBankCodec.encode ![graph,List.replicate floor true,List.replicate K true]
def graph := PhysicalProducer.projection (0 : Fin 3)
def floor := PhysicalProducer.projection (1 : Fin 3)
def rounds := PhysicalProducer.projection (2 : Fin 3)
def vertices := compose graph vertexCount
def edges := compose graph edgeCount
def counts := bank5 graph vertices edges floor rounds
def searchRequest := bank3 floor vertices edges
def searchPacket := bank2 counts searchRequest

def countWord (g : EncodedGraph.Graph) (floor K : Nat) :=
  BitMachineBankCodec.encode ![EncodedGraph.encode g,List.replicate g.vertices true,
    List.replicate g.edges.length true,List.replicate floor true,List.replicate K true]
def requestWord (floor n m : Nat) := BitMachineBankCodec.encode
  ![List.replicate floor true,List.replicate n true,List.replicate m true]
def searchWord (g : EncodedGraph.Graph) (floor K : Nat) :=
  BitMachineBankCodec.encode ![countWord g floor K,requestWord floor g.vertices g.edges.length]

private theorem compose_result (A B : Producer) (x : List Bool) :
    (compose A B).result x=B.result (A.result x) := rfl
private theorem projection_result {N : Nat} (j : Fin N) (x : List Bool) :
    (PhysicalProducer.projection j).result x=BankFieldProjection.result j x := rfl

theorem counts_result (g : EncodedGraph.Graph) (hg : g.Valid) (f K : Nat) :
    counts.result (input (EncodedGraph.encode g) f K)=countWord g f K := by
  simp only [counts,bank5_result,vertices,edges,compose_result,graph,floor,rounds,
    projection_result,input,BankFieldProjection.result_encode,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,vertex_result g hg,edge_result g hg]
  rfl

theorem request_result (g : EncodedGraph.Graph) (hg : g.Valid) (f K : Nat) :
    searchRequest.result (input (EncodedGraph.encode g) f K)=
      requestWord f g.vertices g.edges.length := by
  simp only [searchRequest,bank3_result,vertices,edges,compose_result,graph,floor,
    projection_result,input,BankFieldProjection.result_encode,
    Matrix.cons_val_zero,Matrix.cons_val_one,vertex_result g hg,edge_result g hg]
  rfl

theorem search_result (g : EncodedGraph.Graph) (hg : g.Valid) (f K : Nat) :
    searchPacket.result (input (EncodedGraph.encode g) f K)=searchWord g f K := by
  rw [searchPacket,bank2_result,counts_result g hg,request_result g hg]
  rfl

theorem search_outputs (g : EncodedGraph.Graph) (hg : g.Valid) (f K : Nat) :
    searchPacket.machine.OutputsWithin (input (EncodedGraph.encode g) f K)
      (searchWord g f K)
      (searchPacket.coefficient*((input (EncodedGraph.encode g) f K).length+1)^searchPacket.degree) := by
  simpa only [search_result g hg] using searchPacket.outputs (input (EncodedGraph.encode g) f K)

/-- After the opaque-context search, every graph/count/round field is
physically routed to the literal parameter compiler's Bank5 input. -/
def oldCounts := PhysicalProducer.projection (0 : Fin 2)
def selected := PhysicalProducer.projection (1 : Fin 2)
def old (i : Fin 5) := compose oldCounts (PhysicalProducer.projection i)
def postSearch := bank5 (old 0) (old 1) (old 2) selected (old 4)
def foundWord (g : EncodedGraph.Graph) (f K L : Nat) :=
  BitMachineBankCodec.encode ![countWord g f K,List.replicate L true]
def parameterWord (g : EncodedGraph.Graph) (L K : Nat) :=
  BitMachineBankCodec.encode ![EncodedGraph.encode g,List.replicate g.vertices true,
    List.replicate g.edges.length true,List.replicate L true,List.replicate K true]

theorem post_result (g : EncodedGraph.Graph) (f K L : Nat) :
    postSearch.result (foundWord g f K L)=parameterWord g L K := by
  simp only [postSearch,bank5_result,old,compose_result,oldCounts,selected,
    projection_result,foundWord,countWord,BankFieldProjection.result_encode]
  simp [BankFieldProjection.result_encode,parameterWord]

theorem post_outputs (g : EncodedGraph.Graph) (f K L : Nat) :
    postSearch.machine.OutputsWithin (foundWord g f K L) (parameterWord g L K)
      (postSearch.coefficient*((foundWord g f K L).length+1)^postSearch.degree) := by
  simpa only [post_result] using postSearch.outputs (foundWord g f K L)

#print axioms vertex_result
#print axioms edge_result
#print axioms search_outputs
#print axioms post_outputs
end
end CurrentAdditive.V40GraphConstructorFront
