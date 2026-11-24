import YM.Integration.WilsonNeutralTwoPrintPathBoxSweep
import YM.Integration.WilsonOriginalCensusDeckMean
import YM.Integration.WilsonOriginalCensusOrbitCenters

/-! The single measured common page mean converges to the same relative
cutoff on all deck translates. The number of common translations cancels
before either error is estimated. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathBoxMean
open Filter Function Finset Lattice Wilson RG
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Mer
open WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonNeutralTwoPrintPathBoxPlacement (homes box)
open WilsonNeutralTwoPrintPathBoxInk (ink config)
open WilsonNeutralTwoPrintPathBoxSweep (goal retained hearing)
open WilsonNeutralTwoPrintPathPageLedger (price)
open WilsonNeutralTwoPrintPathRankFare (tariff)
open WilsonOriginalConnectedPeriodPage (Deck)
open WilsonOriginalCensusOrbitCenters (shifted)
open WilsonOriginalCensusDeckMean (mean)
open scoped Classical BigOperators Topology
variable {I α V:Type}[DecidableEq I][Fintype α][NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]{r:ℕ}{n X:Side}

def plotted (h:n.val∣X.val)(S:Finset I)(o:I)(root:Site X)(site:(S.erase o)→Site X)
    (P:(I → Cover)→Ten V (Site X × α) r)(test:V →L[ℝ] ℂ)(weights:(Fin r→Site n × α)→ℂ)(d:Deck h):ℂ:=
  ∑x:Fin r→Site X × α,(∑p:(S.erase o)→Fin (Pages n X),
    test (P (WilsonOriginalCensusOrbitCenters.layout h S o (d.val+root) (shifted h site d) p) x))*
    weights (WilsonNeutralTwoPrintPathPageRead.lower h ∘ x)

theorem original (h:n.val∣X.val)(S:Finset I)(o:I)(live:o∈S)(origin:Cover)(base:(S.erase o) → Cover)
    (root:Site X)(site:(S.erase o)→Site X)(center:splitter h root=wrap n origin)
    (addresses:∀i,splitter h (site i)=wrap n (origin+base i))(D:ℕ)(room:32*D<X.val)
    (P:(I → Cover)→Ten V (Site X × α) r)(F:(I → Cover)→Ten V (Cloth α) r)(σ A:ℝ)(hs:0<σ)
    (paid:∀y:I → Cover,MarkU y S (P y) (F y) σ A)
    (motion:∀(v:Cover)(y:I → Cover),wrap n v=0 → plume (F (fun i=>v+y i)) n=plume (F y) n)
    (test:V →L[ℝ] ℂ)(weights:(Fin r→Site n × α)→ℂ)(height:ℝ)(hh:0≤height)(bounded:∀x,‖weights x‖ ≤ height):
    ‖mean h (plotted h S o root site P test weights)-retained n S o origin base D F test weights‖≤
      (Real.exp (-((σ/2)/2)*(D:ℝ))*price S o α r σ (‖test‖*A))*height+
      ((box n base D).card*(‖test‖*height*tariff α r σ A))*catchW (σ/512) X:=by
  let low:=retained n S o origin base D F test weights
  change ‖mean h _-low‖≤_
  rw [←WilsonOriginalCensusDeckMean.constant h low]
  apply WilsonOriginalCensusDeckMean.paid
  intro d
  let x:=d.val+root
  let received:=lift x
  have actual:wrap n received=wrap n origin:=by
    rw [←Macrame.branch h,show wrap X received=x from wrap_lift _,show x=d.val+root from rfl,
      map_add,show splitter h d.val=0 from d.prop,zero_add,center]
  have compatible (i:S.erase o):splitter h (shifted h site d i)=splitter h (homes X received base i):=by
    change splitter h (d.val+site i)=splitter h (wrap X (received+base i))
    rw [map_add,show splitter h d.val=0 from d.prop,zero_add,addresses,Macrame.branch,map_add,map_add,actual]
  have high:plotted h S o root site P test weights d=hearing h S o (wrap X received) (homes X received base) P test weights:=by
    change (∑z:Fin r→Site X × α,(∑p:(S.erase o)→Fin (Pages n X),
      test (P (config h S o x (shifted h site d) p) z))*weights (WilsonNeutralTwoPrintPathPageRead.lower h ∘ z))=_
    rw [hearing,show wrap X received=x from wrap_lift _]
    simp only [WilsonNeutralTwoPrintPathBoxTail.finite,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [WilsonNeutralTwoPrintPathBoxInk.same h S o x (shifted h site d) (homes X received base) compatible p]
  have shift:wrap n (received-origin)=0:=by rw [map_sub,actual,sub_self]
  have same:retained n S o received base D F test weights=low:=by
    apply Finset.sum_congr rfl
    intro w _
    have moved:ink S o received w.val=(fun i=>(received-origin)+ink S o origin w.val i):=by
      funext i
      convert WilsonNeutralTwoPrintPathBoxInk.translated S o origin (received-origin) w.val i using 2
      rw [sub_add_cancel]
    unfold goal
    rw [moved,motion _ _ shift]
  rw [high,←same]
  exact WilsonNeutralTwoPrintPathBoxSweep.original h S o live received base D room
    (by dsimp only [received];rw [wrap_lift]) P F σ A hs paid test weights height hh bounded

end YM.Integration.WilsonNeutralTwoPrintPathBoxMean
end
