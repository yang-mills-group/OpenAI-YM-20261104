import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphInverseFees
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphBasisExterior
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphOutside
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphInverseExterior
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Enh YM.FVA2.O.Bind YM.FVA2.O.Project YM.FVA2.O.Canon
open YM.FVA2.Scale YM.FVA2.Scale.Equator PowerSeries Set Filter
open YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical Topology
variable (g:YangMills.GaugeGroup){n:ℕ}

theorem incurred (u:Scan g.core n)(q:Ordinary.Price (B g) n)
    (fund:Ordinary.ExteriorExpansion (B g) (read g) (labels g u) q):
    OPEA (GraphTruncation.album g) u (GraphPrices.posted g q):=by
  refine ⟨GraphInverseFees.original g fund,?_⟩
  intro K compact sep h d m E v ce ext k _
  obtain ⟨C,pos,L,paid⟩:=fund.exterior K compact sep m (labels g v) E ce
    (fun y hy=>(GraphOutside.original y).mp (ext hy)) h k
  refine ⟨C,pos,L,?_⟩
  filter_upwards [paid] with t bound
  intro i
  have edge:=GraphTruncation.submitted g u v (GraphPrices.posted g q) h k t i.1.val i.2.val
  rw [GraphPrices.read g q fund.grade] at edge
  have bill:=bound i.1.val i.1.property i.2.val i.2.property
  have clean:‖coeff k (Submit (GraphTruncation.album g) u v t (GraphPrices.posted g q) h i.1.val i.2.val)‖≤
      C*(1+t)^L*Real.exp (((totalG u:ℝ)-(h:ℝ)-1)*t):=(congrArg (fun z:ℂ=>‖z‖) edge).le.trans bill
  simpa only [post,neg_sub,sub_sub,neg_add_rev,neg_neg,mul_assoc] using clean

theorem original (simple:g.IsSimple)(u:Scan g.core n)(q:Ordinary.Price (B g) n)
    (fund:Ordinary.ExteriorExpansion (B g) (read g) (labels g u) q):q=GraphBasisExterior.price g u:=by
  have loan:=(ExteriorReceipt.original g simple u).2.1 (GraphPrices.posted g q) (incurred g u q fund)
  calc
    q=GraphPrices.entered g (GraphPrices.posted g q):=(GraphPrices.read g q fund.grade).symm
    _=GraphBasisExterior.price g u:=congrArg (GraphPrices.entered g) loan
end IssuedMaxwell.GraphInverseExterior
end
