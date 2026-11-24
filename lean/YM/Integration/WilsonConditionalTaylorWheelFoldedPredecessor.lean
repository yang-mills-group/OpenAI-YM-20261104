import YM.Integration.WilsonConditionalTaylorWheelCoverBirth

/-! At an induction date, equality of the whole independently issued
occupied cover gives exact equality of both finite previous polynomials:
the two renderers omit the same vacuum scalar. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelFoldedPredecessor
open Function Filter Lattice RG Wilson Precision Tree PhysicalNext.Repeat.Legato PowerSeries
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Orb FormalBulk08.Lava FormalBulk08.Shore FormalBulk08.Lotus
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open scoped Classical BigOperators Topology
variable {G:Gauge}

theorem signed (R:Run G) (simple:G.Simple) (N j:ℕ) (live:j≤N) (W:Mesa.Pot G)
    (previous:∀e r,-actionW R.family.path.levels R.metals.O N j e (r+1)=W e (r+1)) (n:Side):
    WilsonConditionalTaylorWheelVacuum.signed R N j n=Mesa.stone W n:=by
  let A:=R.family.path.levels
  let P:=actionW A R.metals.O N j
  let T:=Winding.emera P n
  have good:=Winding.emera_far A simple R.alloy.B.ratio live n
  have fact:=old A R.metals.O simple R.alloy.B.ratio N j live
  apply PowerSeries.ext
  intro e
  change coeff e (-flash T)=_
  rw [map_neg,flash,coeff_mk,Mesa.sow_coeff,Mesa.sow]
  have cap:still (T e) (e+2+1):=fun r hr=>good.1 e r (by omega)
  rw [visible cap,Finset.sum_range_succ']
  have origin:paint 0 (T e 0)=0:=by change paint 0 (0:_)=0;exact map_zero _
  rw [origin,add_zero,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [WilsonConditionalTaylorWheelTensors.painted,←map_neg]
  apply congrArg (Lava.facade (r+1))
  funext x
  have winding:=WilsonConditionalTaylorWheelFolding.periodized x (P e (r+1)) (fact.patch e (r+1)).road
  change -(lagoon (P e (r+1)) n x)=cum 0 n (W e (r+1)) x
  rw [winding,←previous e r]
  change -(∑' v:Picks 0 n (boil n (x 0)) x,P e (r+1) v.val)=
    ∑' v:Picks 0 n (boil n (x 0)) x,-P e (r+1) v.val
  exact tsum_neg.symm

theorem born (R:Run G) (simple:G.Simple) (u:G.ColorIndex)
    (wood:∀j,Lodge (R.family.path.levels.clock.op j 0).patch)
    (tags:∀j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (N:ℕ) (n:Side):WilsonConditionalTaylorWheelVacuum.signed R N N n=
    Mesa.stone (Dove.model R.family.path.levels wood (fun j=>(R.family.path.levels.blocks j 0).branches)
      R.metals.O u N N) n:=
  signed R simple N N le_rfl _ (WilsonConditionalTaylorWheelCoverBirth.original R simple u wood tags N) n

end YM.Integration.WilsonConditionalTaylorWheelFoldedPredecessor
end

