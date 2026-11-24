import YM.Integration.WilsonConditionalTaylorWheelInputTruncation
import YM.Integration.WilsonConditionalTaylorWheelMassTransfer
import YM.Integration.WilsonConditionalTaylorWheelRawVacuum

/-! The same integrated raw finite vacuum on all external fields, before
either prescription extracts its running kinetic term. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelRecordedEnergy
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary Lotus
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato
open MSbar MSbar.Cacao MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonConditionalTaylorWheelKernel
open scoped Classical BigOperators Matrix
variable {G:Gauge} (D:Stage G)
local notation "op" => D.R.family.path.levels.clock.op D.j D.per
local notation "coarse" => D.R.family.side D.j D.per
local notation "fine" => D.R.family.side (D.j+1) D.per
local notation "form" => freeForms D.R.family.path.levels D.N (D.j+1)
local notation "target" => freeForms D.R.family.path.levels D.N D.j
set_option quotPrecheck false in
local notation "mean" => installed (op).ratio (predictionA D.R.family.path.levels D.N D.j)
local notation "old" => Winding.emera (actionW D.R.family.path.levels D.R.metals.O D.N (D.j+1)) fine
set_option quotPrecheck false in
local notation "K" => (RunFormalChain.fromRun D.R).step D.N D.j D.per D.live
local notation "I" => WilsonConditionalTaylorWheelRawVacuum.inside D

theorem positive (simple:G.Simple) {E:ℕ} (U:Pap (wire G fine)) (A:Pap (wire G coarse))
    (head:MvPolynomial (wire G coarse) ℝ) (agree:Through E (-flash old) U)
    (issued:∀u:Positions (Primary coarse G),
      let y:=FreeResolvent.flatten (tint G (Body 1 coarse) u)
      glimpse y A=PowerSeries.C (traceP y head)+covelog (WilsonRunVacuumWickCubature.bank K D.forest D.tag u U))
    (e:ℕ) (active:0<e) (cap:e≤E):
    coeff e A=coeff e (covelog I):=by
  have shape:=Winding.emera_far D.R.family.path.levels simple D.R.alloy.B.ratio (Nat.succ_le_iff.mpr D.live) fine
  have origin:coeff 0 I=1:=by
    rw [coeff_zero_eq_constantCoeff_apply]
    unfold WilsonConditionalTaylorWheelRawVacuum.inside
    rw [←WilsonConditionalTaylorWheelKernel.vacuum]
    exact inside_mass op D.forest form mean (P:=old) D.R.alloy.B.ratio
  apply MvPolynomial.funext
  intro y
  let u:Positions (Primary coarse G):=(tint G (Body 1 coarse)).symm (fun b=>WithLp.toLp 2 (fun i=>y (FreeResolvent.ix b i)))
  have represented:FreeResolvent.flatten (tint G (Body 1 coarse) u)=y:=by
    unfold u
    rw [ContinuousLinearEquiv.apply_symm_apply];rfl
  have bill:=issued u
  have mass:=WilsonConditionalTaylorWheelMassTransfer.bank D old shape.1 u
  dsimp only at bill mass
  rw [represented] at bill mass
  have signed:=WilsonConditionalTaylorWheelInputTruncation.bank K D.forest D.tag u agree
  have log:
      glimpse y (covelog I)=covelog (WilsonRunVacuumWickCubature.bank K D.forest D.tag u (-flash old)):=by
    change PowerSeries.map (MvPolynomial.aeval y).toRingHom (covelog I)=_
    rw [map_covelog _ origin]
    change covelog (glimpse y I)=_
    exact congrArg covelog mass
  have tested:coeff e (glimpse y A)=coeff e (glimpse y (covelog I)):=by
    rw [bill,log,map_add,coeff_C_of_ne_zero (Nat.ne_of_gt active),zero_add]
    exact (signed e cap).symm
  simpa only [glimpse_coeff,traceP,MvPolynomial.aeval_eq_eval] using tested

theorem occupied (simple:G.Simple) {E:ℕ} (U:Pap (wire G fine)) (A:Pap (wire G coarse))
    (head:MvPolynomial (wire G coarse) ℝ) (agree:Through E (-flash old) U)
    (issued:∀u:Positions (Primary coarse G),
      let y:=FreeResolvent.flatten (tint G (Body 1 coarse) u)
      glimpse y A=PowerSeries.C (traceP y head)+covelog (WilsonRunVacuumWickCubature.bank K D.forest D.tag u U))
    (e r:ℕ) (live:0<e) (cap:e≤E) (used:0<r):
    rancho (-flash (winter op D.forest form target mean D.R.metals.O old)) e r=rancho A e r:=by
  rw [WilsonConditionalTaylorWheelRawVacuum.occupied D simple e r live used]
  exact congrArg (Lava.marble r) (positive D simple U A head agree issued e live cap).symm

end YM.Integration.WilsonConditionalTaylorWheelRecordedEnergy
end

