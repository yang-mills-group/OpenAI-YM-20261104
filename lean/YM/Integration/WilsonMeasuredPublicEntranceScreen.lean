import YM.Integration.WilsonMeasuredPublicEntrancePanel
import YM.Integration.WilsonMeasuredPublicEntranceQuiet
/-! A finite screen uses the actual original parent chain; its empty family is read exactly. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 4300000
set_option maxRecDepth 8192
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceScreen
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open WilsonOriginalReceivedChain WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse
open WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
open WilsonReceivedFirstTrace
open Pert.Asymptotics
open Filter WilsonThermometerMixedCollarSubpower
open WilsonThermometerMixedCollarSubpower
open Multi WilsonOriginalAlternativeTrialFunded
open QuadraticLocal.Tint QuadraticLocal.Advent.Oak QuadraticLocal.Earn Filter MeasureTheory
open WilsonAddressedFiniteGuardTrial (printed)
open WilsonMeasuredPublicEntranceSignedEar (weighted)
open Labels Source RG12 Extra.Histories Motion Bandage Trace.Physical.GermGraph
open WilsonReflectedFundedHearing WilsonReflectedPublicGuardedColumns
open WilsonThermometerReflectedTrajectory WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetTale
open WilsonThermometerMarchSource WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue
open RG05Readout RG05Readout.Native RG05Readout.Address Ac GridApprox.Nil MergeProof MergeProof.Accent
open RG05Readout.Many RG05Readout.Pantry Records WilsonThermometerUnitFilingCoarse
open WilsonAddressedAlignedColumn WilsonReflectedPublicOrientedFaces
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonReflectedMixedThermalArms (rent)
open WilsonReflectedPublicCommonDose (dose)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonReflectedMixedThermalArms (rent)
open WilsonReflectedPublicCommonDose (dose)
variable {G:Gauge} (R:Run G) {V:Type} [Fintype V] [DecidableEq V] (grades:V → ℕ)
local notation "C" => R.family
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "J_" => Stock.census V
local notation "fired_" => WilsonOriginalAlternativeFiniteSource.fired (V:=V)


open WilsonMeasuredPublicEntrancePanel
local notation "X" => Unit×(V×Bool)

def Ground (N per j f apron:ℕ) (o:V → Site ((C).side f per)):Prop:=
  5 ≤ ((C).path.rep N per f).p.B ∧
  (∀v w:V,v≠w→((C).path.rep N per f).p.B^2+1 ≤ separation (o v) (o w)) ∧
  (C).S.a j/(C).S.a f ≤ (H f)^apron ∧
  ∃(path:∀a,X→Site ((C).side a per))(anchor:X),
    path f=(o∘Prod.fst)∘Prod.snd ∧
    (∀v,j+1 ≤ v→v<f→path v=((C).path.levels.clock.op v per).ratio.parent ∘ path (v+1)) ∧
    (∀v,coverNumber (((C).path.rep N per (j+1)).p.B) ({path (j+1) anchor,path (j+1) v}:Support _) ≤ 1) ∧
    ((C).path.levels.clock.op j per).ratio.parent (path (j+1) anchor)=0

theorem vacant {N per f K requested power t u:ℕ}{B:ℝ}{fk:f ≤ K}{cut:K ≤ N}
    (A:Panel R grades N per f K fk cut requested power t B)(held:u ≤ f)(none:V→False):
    Reading R grades A held:=by
  classical
  intro s
  have empty:s.val=∅:=Finset.eq_empty_iff_forall_notMem.mpr (fun v _=>(none v).elim)
  let pin:=fun v=>((C).S.toDepth fk per).embed (A.loc v)
  let v:=fun a=>Motion.patch ((C).labels.level (grades a)) (A.turn a)
    ((A.axis a).symm (fitted R (grades a) (A.slot a) N per (A.names a)))
  let z:=fun a=>(charged R grades A a:ℂ)*(((C).S.a K:ℂ)^(grades a))⁻¹
  let ids:=fun a=>displayed R (grades a) (A.names a) (A.turn a)
  let o:=fun a=>WilsonThermometerReflectedTrajectory.anchorAt R (A.loc a) N
  let c:=fun a=>(charged R grades A a:ℂ)
  have eqn:=WilsonMeasuredPublicEntranceSignedAtK.original R grades cut (held.trans fk) pin v z ids o c s 1
  have zero:=WilsonMeasuredPublicEntranceQuiet.original R grades cut (held.trans fk) pin v z ids o c s empty 1
  exact ⟨eqn,(norm_eq_zero.mpr zero).le.trans (inv_nonneg.mpr (pow_nonneg (WardBin.hot (C).path.levels f).le _))⟩

end YM.Integration.WilsonMeasuredPublicEntranceScreen
end
