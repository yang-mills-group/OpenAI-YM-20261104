import YM.Integration.WilsonIndependentCollarDatedMaterial
import YM.Integration.WilsonIndependentCollarLocatorPages

/-! Choose and pay an actual binder before planting. Each leg is the
coordinate route of the designated physical lifts, and the existing
passport and its complete height remain on that same binder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarRoutedBinder
open Lattice Finset Marker QuadraticLocal QuadraticLocal.Earn WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Wheel.Address OriginalIssuedMarkedRows
open scoped Classical BigOperators
variable {n:Side}{I:Type}[Fintype I][DecidableEq I]

theorem leg (x y:Cover)(order:Lattice.Order):(route x y order).length=terrain.gap x y:=by
  have unique:(allAxes order).Nodup:=(List.nodup_finRange 4).map order.injective
  have all:(allAxes order).toFinset=univ:=eq_univ_of_forall fun i=>
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨order.symm i,by simp,by simp⟩)
  simp only [route,axisRoute,List.length_flatMap,straight,List.length_replicate]
  rw [←List.sum_toFinset _ unique,all]
  rfl

variable (P:Passport n I)(s:(Stock.census I).Mode)(c:I)(live:c∈s.val)(y:I → Cover)
  (origins:∀i∈s.val,P.origin i=wrap n (y i))(order:Lattice.Order)(extra:ℕ)

def routed:Binder P (Stock.census I) where
  mode:=s
  front:=c
  east:=live
  path i:=route (y c) (y i) order
  span i h:=by rw [origins c live,origins i h,←wrap_stop_cover,route_end]
  extra:=extra

theorem original:
    (routed P s c live y origins order extra).length ≤ extra+(∑i∈s.val,P.height i)+feeH y c s.val:=by
  change extra+(∑i∈s.val,((route (y c) (y i) order).length+P.height i)) ≤ _
  simp_rw [leg]
  rw [sum_add_distrib]
  unfold feeH
  omega

end YM.Integration.WilsonIndependentCollarRoutedBinder
end
