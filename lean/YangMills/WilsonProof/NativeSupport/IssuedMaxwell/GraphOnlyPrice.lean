import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphResidual
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphHomogeneous
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphOnlyPrice
open YM YM.FVA2 YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Enh YM.FVA2.O.Project
open Set Filter YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation IssuedMaxwell.GraphRevenue
open scoped BigOperators Classical Topology
variable (g:YangMills.GaugeGroup){n:ℕ}

theorem admitted (simple:g.IsSimple)(a:Fin n→Ordinary.Label (B g))(q r:Ordinary.Price (B g) n)
    (cq:Ordinary.ExteriorExpansion (B g) (read g) a q)(cr:Ordinary.ExteriorExpansion (B g) (read g) a r):
    let u:=GraphAnchor.word g n
    let p:=GraphBasisExterior.ticket g u
    OPEA (GraphTruncation.album g) u (GraphResidual.service g p q r):=by
  let u:=GraphAnchor.word g n
  let p:=GraphBasisExterior.ticket g u
  let adj:=GraphResidual.service g p q r
  have loan:=GraphExteriorMarket.original g simple u
  change OPEA (GraphTruncation.album g) u adj
  refine ⟨GraphAffine.cleared _ _ _ (ExteriorReceipt.original g simple u).1.toMarkup
    (GraphInverseFees.original g cq) (GraphInverseFees.original g cr),?_⟩
  intro K ck sep h d m E v ce ext k _
  have paid:=GraphResidual.funded g a (labels g u) p q r loan cq cr K ck sep (labels g v) E ce ext h k
  have equality (i:K×E)(t:ℝ):PowerSeries.coeff k (Submit (GraphTruncation.album g) u v t adj h i.1.val i.2.val)=
      due g (labels g u) (GraphPrices.entered g adj) (labels g v) h k t i.1.val i.2.val:=
    GraphTruncation.submitted g u v adj h k t i.1.val i.2.val
  change Rain (rate g (labels g u) h) (fun (i:K×E)(t:ℝ)=>PowerSeries.coeff k
    (Submit (GraphTruncation.album g) u v t adj h i.1.val i.2.val))
  simp_rw [equality]
  exact paid

theorem original (simple:g.IsSimple)(a:Fin n→Ordinary.Label (B g))(q r:Ordinary.Price (B g) n)
    (cq:Ordinary.ExteriorExpansion (B g) (read g) a q)(cr:Ordinary.ExteriorExpansion (B g) (read g) a r):q=r:=by
  let u:=GraphAnchor.word g n
  let p:=GraphBasisExterior.ticket g u
  have equal:GraphResidual.service g p q r=p:=(ExteriorReceipt.original g simple u).2.1 _ (admitted g simple a q r cq cr)
  have posted:GraphPrices.posted g q=GraphPrices.posted g r:=by
    funext t x b
    have spent:=congrFun (congrFun (congrFun equal t) x) b
    rw [GraphResidual.service,GraphAffine.full] at spent
    exact add_left_cancel (a:=p t x b) (by linear_combination spent)
  calc
    q=GraphPrices.entered g (GraphPrices.posted g q):=(GraphPrices.read g q cq.grade).symm
    _=GraphPrices.entered g (GraphPrices.posted g r):=congrArg (GraphPrices.entered g) posted
    _=r:=GraphPrices.read g r cr.grade
end IssuedMaxwell.GraphOnlyPrice
end
