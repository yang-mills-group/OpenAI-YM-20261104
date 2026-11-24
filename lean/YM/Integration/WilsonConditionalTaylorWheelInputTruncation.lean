import YM.Integration.WilsonConditionalTaylorWheelFoldedPredecessor
import YM.Integration.WilsonConditionalTaylorVacuumPrefix
import YM.Integration.WilsonConditionalTaylorWheelMassTransfer

/-! At an induction date, equality of the whole independently issued
occupied cover gives exact equality of both finite previous polynomials:
the two renderers omit the same vacuum scalar. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelInputTruncation
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

open Matrix Push.Uniform FormalBulk08.Series MSbar MSbar.Cacao MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary Lotus
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato
open MSbar MSbar.Cacao MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open PertExtension.Chart WilsonMovingNormalizedBank WilsonConditionalTaylorWick
open WilsonMovingPolynomialPull

theorem bank {c f:Side} {S:StepData c f} {p:Clip} {X:PathData G} {O:ChartRatio G}
    (R:Bulk.Kernel S p X O) (F:Forest S.ratio) (t:S.Choices) (u:Positions (Primary c G))
    {A B:Pap (FormalBulk08.Reef.wire G f)} {E:ℕ} (given:Through E A B):
    Through E (covelog (WilsonRunVacuumWickCubature.bank R F t u A))
      (covelog (WilsonRunVacuumWickCubature.bank R F t u B)):=by
  let s:=(WilsonMovingGaussianCoordinates.link G f).symm
  let head (Z:Pap (FormalBulk08.Reef.wire G f)):=splitV (place s Z)
  have entering:Through E (place s A) (place s B):=given.map_left _
  have low (Z:Pap (FormalBulk08.Reef.wire G f)):Kind (head Z):=by
    change coeff 0 ((place s Z)-PowerSeries.C (coeff 0 (place s Z)))=0
    rw [map_sub,coeff_zero_C,sub_self]
  have split:Through E (head A) (head B):=by
    intro d hd
    change coeff d ((place s A)-PowerSeries.C (coeff 0 (place s A)))=
      coeff d ((place s B)-PowerSeries.C (coeff 0 (place s B)))
    rw [map_sub,map_sub,entering d hd,entering 0 (Nat.zero_le _)]
  have spice:Through E (barbed F t O (head A)) (barbed F t O (head B)):=
    (Through.exact_eq _ _).add (split.map_left (rail (taps F G)).toRingHom)
  have agree:=spice.expan_congr (well F t O (head A) (low A))
  rw [WilsonMovingExponentialConvention.exp _ (well F t O (head A) (low A)),
    WilsonMovingExponentialConvention.exp _ (well F t O (head B) (low B))] at agree
  apply Through.cove_congr
  · exact beam_through _ (agree.map_left _)
  · exact WilsonConditionalTaylorVacuumPrefix.initial _ _ _ (R.positive F t) _ (well _ _ _ _ (low A))

end YM.Integration.WilsonConditionalTaylorWheelInputTruncation
end

