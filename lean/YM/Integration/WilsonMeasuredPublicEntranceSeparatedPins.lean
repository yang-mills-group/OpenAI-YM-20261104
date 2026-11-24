import YM.Integration.WilsonMeasuredPublicEntranceOrderedPins
import YM.Integration.WilsonMovingCalibratedFields
import YM.OPE.Samples.Layout

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceSeparatedPins
open Function Filter Set Lattice Wilson Cells Extraction Spec RG Source PhysicalNext.Repeat.Legato
open WilsonMeasuredPublicEntranceOrderedPins (physical publicValue)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){order:Extraction.Order}{S:Table R.family.book}(F:Final R.family order S)
    {n:ℕ}(d:Caps n)(site:ℕ)(o:Fin n→ Cover)
local notation "C₀" => R.family
local notation "point" => Order.grid (C₀) site o

theorem elevated {N:ℕ}(live:site≤N):tag ((C₀).S.a N) (fun i=>OPE.zoom (C₀).S live (o i))=point:=by
  change points (fun i=>(C₀).S.gridPoint N (OPE.zoom (C₀).S live (o i)))=points (fun i=>(C₀).S.gridPoint site (o i))
  exact congrArg points (funext fun i=>OPE.zoom_grid (C:=R.family) live (o i))

theorem enrolled {N:ℕ}(live:site≤N)(p:ℕ)(y:(C₀).book.Vector d):
    physical d site o N p y=(C₀).ensemble (N:=N) (p:=p) d (wrap _ ∘ fun i=>OPE.zoom (C₀).S live (o i)) y:=by
  have eq:(fun i=>location (C₀).S site N p (o i))=wrap ((C₀).side N p) ∘ (fun i=>OPE.zoom (C₀).S live (o i)):=by
    funext i
    simp only [location,dif_pos live,Function.comp_apply]
    exact OPE.Log.Trunk.Canvas.neighbor (C:=R.family) (o i) live
  change (C₀).omega N p _=(C₀).omega N p _
  congr 1
  funext U
  change (∏i,(C₀).O N p (y i) ((fun i=>location (C₀).S site N p (o i)) i) U)=_
  rw [eq]

include F in
theorem variation (simple:G.Simple){ν:Filter (ℕ×ℕ)}(below:ν≤order.fuse)(Y:(ℕ×ℕ)→(C₀).book.Vector d)
    (c:(C₀).book.Vector d)(cv:∀i,Tendsto (fun w=>Y w i) ν (𝓝 (c i)))(safe:point∈conf n):
    Tendsto (fun w:ℕ×ℕ=>physical d site o w.1 w.2 (Y w)) ν (𝓝 (S.value d point c)):=by
  rw [Metric.tendsto_nhds]
  intro ε he
  have intake:=WilsonMovingCalibratedFields.paid R simple F below d Y c cv {point} isCompact_singleton
    (Set.singleton_subset_iff.mpr safe) ε he
  have later:∀ᶠw:ℕ×ℕ in order.fuse,site≤w.1:=by
    rw [Order.fused,Order.late]
    exact Eventually.of_forall fun _=>order.mesh.cofinal.eventually (eventually_ge_atTop site)
  filter_upwards [later.filter_mono below,intake] with w live read
  let pin:=fun i=>OPE.zoom (C₀).S live (o i)
  have same:tag ((C₀).S.a w.1) pin=point:=elevated R site o live
  have charged:=read pin (by rw [same];exact Set.mem_singleton _)
  rwa [same,← enrolled R d site o live w.2 (Y w)] at charged

end YM.Integration.WilsonMeasuredPublicEntranceSeparatedPins
end
