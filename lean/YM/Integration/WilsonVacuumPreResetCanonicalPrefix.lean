import YM.Integration.WilsonVacuumPreResetCanonicalBlock
import YM.Integration.WilsonConditionalTaylorWheelVacuum
import YM.Integration.WilsonConditionalTaylorWheelFolding
import YM.Integration.WilsonConditionalTaylorWheelTensors

/-! The whole upper quiet table, with its original cutoff, enters the same finite Wick logarithm. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCanonicalPrefix
open Function Filter Lattice RG Wilson Precision Tree PhysicalNext.Repeat.Legato PowerSeries
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Orb FormalBulk08.Lava FormalBulk08.Shore FormalBulk08.Lotus
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open scoped Classical BigOperators Topology
variable {G:Gauge}

theorem retained (R:Run G) (simple:G.Simple) (N j:ℕ) (live:j≤N) (W:Mesa.Pot G)
    (E:ℕ) (previous:∀e≤E,∀r<e+2,-actionW R.family.path.levels R.metals.O N j e (r+1)=W e (r+1)) (n:Side):
    FormalBulk08.Series.Through E (WilsonConditionalTaylorWheelVacuum.signed R N j n) (Mesa.stone W n):=by
  let A:=R.family.path.levels
  let P:=actionW A R.metals.O N j
  let T:=Winding.emera P n
  have good:=Winding.emera_far A simple R.alloy.B.ratio live n
  have fact:=old A R.metals.O simple R.alloy.B.ratio N j live
  intro e paid
  change coeff e (-flash T)=_
  rw [map_neg,flash,coeff_mk,Mesa.sow_coeff,Mesa.sow]
  have cap:still (T e) (e+2+1):=fun r hr=>good.1 e r (by omega)
  rw [visible cap,Finset.sum_range_succ']
  have origin:paint 0 (T e 0)=0:=by change paint 0 (0:_)=0;exact map_zero _
  rw [origin,add_zero,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [WilsonConditionalTaylorWheelTensors.painted,←map_neg]
  apply congrArg (Lava.facade (r+1))
  funext x
  have winding:=WilsonConditionalTaylorWheelFolding.periodized x (P e (r+1)) (fact.patch e (r+1)).road
  change -(lagoon (P e (r+1)) n x)=cum 0 n (W e (r+1)) x
  rw [winding,←previous e paid r (Finset.mem_range.mp hr)]
  change -(∑' v:Picks 0 n (boil n (x 0)) x,P e (r+1) v.val)=
    ∑' v:Picks 0 n (boil n (x 0)) x,-P e (r+1) v.val
  exact tsum_neg.symm


open FormalBulk08.Reef FormalBulk08.Series FormalBulk08.Wick

theorem propagated {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)(a:S.Choices)(O:ChartRatio G)
    (H:Hull (Pine G S F) (wire G c)){p q:Pap (wire G f)}{E:ℕ}(given:Through E p q)
    (solved:Solved H (Reef.flush F a O p)):
    Through E (covelog (Orb.vocal H (Reef.flush F a O p))) (covelog (Orb.vocal H (Reef.flush F a O q))):=by
  have carried:Through E (Reef.vacuumU a p) (Reef.vacuumU a q):=by
    intro e he
    simp only [Reef.vacuumU,map_sub,coeff_map,given e he]
  have integrated:Through E (Reef.flush F a O p) (Reef.flush F a O q):=
    (Through.change_congr _ carried).add (Through.exact_eq _ _)
  have entering:Through E (Orb.toInk H (Reef.flush F a O p)) (Orb.toInk H (Reef.flush F a O q)):=
    Through.change_congr _ integrated
  have calm:Through E (Orb.positive H (Reef.flush F a O p)) (Orb.positive H (Reef.flush F a O q)):=by
    intro e he
    simp only [Orb.positive,map_sub,entering e he]
  exact (beam_through _ (calm.expan_congr (Orb.plur H _ solved))).cove_congr (Orb.voice H _ solved)

end YM.Integration.WilsonVacuumPreResetCanonicalPrefix
