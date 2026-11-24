import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphPriceFusion
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphFore
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphHomogeneous
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Enh YM.FVA2.O.Bind YM.FVA2.O.Project YM.FVA2.O.Canon
open YM.FVA2.Scale YM.FVA2.Scale.Equator PowerSeries Filter Set
open YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical Topology
variable (g:YangMills.GaugeGroup){n m:ℕ}

def ticket (a:Fin n→Ordinary.Label (B g)):FLog g.core n:=
  GraphTender.combine (GraphFore.income g a) (fun s=>GraphBasisExterior.ticket g (GraphFore.mask g a s))
def price (a:Fin n→Ordinary.Label (B g)):Ordinary.Price (B g) n:=GraphPrices.entered g (ticket g a)

theorem signed (a:Fin n→Ordinary.Label (B g))(pure:∀i,Ordinary.homogeneous (B g) (a i).1 (a i).2.val)
    (b:Fin m→Ordinary.Label (B g))(h k:ℕ)(t:ℝ)(x:Points n)(y:Points m):
    read g (n+m) k (Fin.append a b) (forest (squeeze t x) y)-
      Ordinary.truncation (B g) (read g) (price g a) (sky g a) h k b t x y=
    ∑s:GraphFore.grades g a,GraphFore.income g a s*
      (read g (n+m) k (Fin.append (labels g (GraphFore.mask g a s)) b) (forest (squeeze t x) y)-
       Ordinary.truncation (B g) (read g) (GraphBasisExterior.price g (GraphFore.mask g a s)) (sky g a) h k b t x y):=by
  unfold price ticket
  rw [GraphFore.expanded g a pure,GraphPriceFusion.original,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _=>(mul_sub _ _ _).symm

theorem original (simple:g.IsSimple)(a:Fin n→Ordinary.Label (B g))
    (pure:∀i,Ordinary.homogeneous (B g) (a i).1 (a i).2.val):
    Ordinary.ExteriorExpansion (B g) (read g) a (price g a):=by
  have paid:Markup (ticket g a):=GraphTender.purchased _ _ (fun s=>
    (ExteriorReceipt.original g simple (GraphFore.mask g a s)).1.toMarkup)
  let p:=ticket g a
  refine ⟨GraphPrices.degree g p,GraphPriceCoordinates.collision g p paid,
    GraphPriceCoordinates.polynomial g p paid,GraphPriceCoordinates.continuous g p paid,
    fun K ck sep=>GraphPriceCompact.original g p paid K ck sep,?_⟩
  intro K ck sep m b E ce ext h k
  let rate:ℝ:=(h:ℝ)+1-(sky g a:ℝ)
  let job (s:GraphFore.grades g a)(i:K×E)(t:ℝ):ℂ:=read g (n+m) k
    (Fin.append (labels g (GraphFore.mask g a s)) b) (forest (squeeze t i.1.val) i.2.val)-
    Ordinary.truncation (B g) (read g) (GraphBasisExterior.price g (GraphFore.mask g a s)) (sky g a) h k b t i.1.val i.2.val
  have each (s:GraphFore.grades g a):Rain rate (job s):=by
    have sale:=GraphExteriorMarket.original g simple (GraphFore.mask g a s)
    obtain ⟨C,pos,L,wages⟩:=sale.exterior K ck sep m b E ce ext h k
    refine ⟨C,pos,L,?_⟩
    filter_upwards [wages] with t bound
    intro i
    have pay:=bound i.1.val i.1.property i.2.val i.2.property
    change ‖job s i t‖≤C*(1+t)^L*Real.exp (((sky g a:ℝ)-(h:ℝ)-1)*t) at pay
    simpa only [rate,post,neg_sub,sub_sub,neg_add_rev,neg_neg,mul_assoc] using pay
  obtain ⟨C,pos,L,cash⟩:=Rain.sum Finset.univ (fun s _=>(each s).scalar (GraphFore.income g a s))
  refine ⟨C,pos,L,?_⟩
  filter_upwards [cash] with t bound
  intro x hx y hy
  have equality:=signed g a pure b h k t x y
  have paidSum:‖∑s,GraphFore.income g a s*job s (⟨x,hx⟩,⟨y,hy⟩) t‖≤
      C*(1+t)^L*Real.exp (((sky g a:ℝ)-(h:ℝ)-1)*t):=by
    simpa only [rate,post,neg_sub,sub_sub,neg_add_rev,neg_neg,mul_assoc] using bound (⟨x,hx⟩,⟨y,hy⟩)
  exact (congrArg (fun z:ℂ=>‖z‖) equality).le.trans paidSum
end IssuedMaxwell.GraphHomogeneous
end
