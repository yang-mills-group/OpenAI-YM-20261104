import YM.Integration.WilsonPositionProgramTrialAccrued
import YM.Integration.WilsonIndependentMatchedFiledIncome

/-! The reporting operator on an actual compact probe planted at K in the
N-vacuum. The back-propagated coordinate contains every stable-to-field
feed of its own word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialProbeFit
open Function Finset Matrix Lattice Wilson RG Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard
open WilsonCoeffUV.Mer WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Mark
open WilsonPositionProgramTrialFittedLens (ticket matrix)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonIndependentMatchedFiledIncome (plate)
open scoped BigOperators Classical
variable {G:Gauge}(Q:SealR G)(A:Levels G)(O:ChartRatio G)(N k m i:ℕ)

def compact (c:Q.Rider):TowerS G Q.D:=Shrine (plate Q.ans Q.path) c
def fit (c:Q.Rider):Q.Rider:=tallyV A O Q.ans Q.path N k (m+i) m (compact Q c)
def income (c:Q.Rider):Q.Rider:=matrix (Wray A O Q.ans Q.path N m)
  (opal Q.F (spools A O N k Q.h m i (compact Q c)))

theorem heads (H:Hol G)(honest:Q.ans.Sound H)(purchase:Bid.pop Q.ans)(c:Q.Rider):
    fit Q A O N k m i c=c+boot A O Q.ans Q.path N k (m+i) m i
      (Silt (Peaks A O Q.ans Q.path N (m+i)) (compact Q c)):=by
  have pivot:opal Q.F (compact Q c)=c:=Shrine_read _ c (freshly Q.ans H Q.path honest purchase)
  change opal Q.F (compact Q c)+_ = _
  rw [pivot,show m+i-m=i by omega]

theorem original {H:Hol G}(honest:Q.ans.Sound H)(purchase:Bid.pop Q.ans)
    {e u:ℕ}{cuts:Rails Q.h k u e}{E W B:Credit}(L:Torch H Q.ans Q.path cuts E W B)
    (entered : L.L.V.anchor ≤ m)(live : m+i ≤ N)(c : Q.Rider):
    let A:=L.L.V.draws
    let O:=L.L.V.paid
    income Q A O N k m i c=ticket A O Q N m (m+i) (fit Q A O N k m i c) ∧
    received A O Q m (m+i) N (income Q A O N k m i c)=fit Q A O N k m i c ∧
    ∀v:Q.Rider,income Q A O N k m i c=v ↔
      fit Q A O N k m i c=received A O Q m (m+i) N v:=by
  intro A O
  have accepted:On k (compact Q c):=Shrine_on _ (freshly Q.ans H Q.path honest purchase) c cuts.hk
  have sold:=TallOracle L entered live (compact Q c) accepted
  have same:income Q A O N k m i c=ticket A O Q N m (m+i) (fit Q A O N k m i c):=by
    change matrix _ (opal _ (spools _ _ _ _ _ _ _ _))=matrix _ (street _ _ _ _ _ _ ((m+i)-m) _)
    rw [show m+i-m=i by omega]
    exact congrArg (matrix (Wray A O Q.ans Q.path N m)) sold
  have defined:=WilsonPositionProgramTrialFittedLens.original H Q L.L entered
    (Nat.le_add_right m i) live (fit Q A O N k m i c)
  have back:received A O Q m (m+i) N (income Q A O N k m i c)=fit Q A O N k m i c:=by
    rw [same]
    exact defined.2.1
  refine ⟨same,back,fun v=>⟨fun hs=>?_,fun hs=>?_⟩⟩
  · rw [←hs,back]
  · rw [same,hs]
    exact WilsonPositionProgramTrialReverseLens.field H Q L.L entered (Nat.le_add_right m i) live v

end YM.Integration.WilsonPositionProgramTrialProbeFit
