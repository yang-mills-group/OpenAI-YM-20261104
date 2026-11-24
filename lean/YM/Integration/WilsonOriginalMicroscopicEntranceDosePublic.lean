import YM.Integration.WilsonOriginalMicroscopicEntranceDoseGrid
import YM.Integration.WilsonOriginalMicroscopicEntrancePublicTrial
import YM.Integration.WilsonOriginalMicroscopicEntranceSettledHeld
import YM.Integration.WilsonOriginalMicroscopicEntrancePublicHeld

/-! An original, publicly enrolled cutoff product and its independently replanted K comparator at one real boundary. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceDosePublic
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ
open WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetTale WilsonThermometerReflectedTrajectory
open WilsonThermometerOwnOffsetNectar WilsonReflectedPublicOrientedFaces
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Push.Local Marker Motion PhysicalNext PhysicalNext.Repeat.Legato
open Planned.GuardedAtom MergeProof MergeProof.Accent Extra.Multi RG05Readout RG05Readout.Address
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory
open WilsonAddressedAlignedColumn
open WilsonThermometerUnitFilingCoarse WilsonReflectedPublicOrientedFaces WilsonSeparatedPrefixCanonicalClearConvolution
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "I" => Fin 3
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta
local notation "J₀" => Marks I
local notation "X" => Unit×(I×Bool)


open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedWallet
open Extra.Histories Extra.Multi Push.AbsoluteSums.Animals
open WilsonOriginalMicroscopicEntranceFiling (units)
open WilsonOriginalMicroscopicEntranceGridBalance (slotFare)
open WilsonOriginalMicroscopicEntranceOpticalUnits (pole rank dye fare)
open WilsonOriginalMicroscopicGuardedFlat (peak count)
open Trace.Physical.Germ Trace.Physical.GermGraph
open MeasureTheory WilsonOriginalMicroscopicEntranceTwoExits
open GapsContact GapsContact.Seams GapsContact.Stamps GapsContact.Ascent
open OPE.Therm WilsonCoeffUV.Embroider
open WilsonOriginalMicroscopicEntranceGridRow (pin)

open WilsonOriginalMicroscopicEntranceGridBalance (slotFare)
open WilsonOriginalMicroscopicEntranceHaloIncome (all)
open WilsonOriginalMicroscopicEntranceOpticalUnits (fare)
open WilsonOriginalMicroscopicGuardedFlat (count)
open WilsonOriginalMicroscopicEntrancePublicTrial (Restart)
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)

theorem field {T:Type*} (c:I→ℂ)(nonzero:∀i,c i≠0)(s:(J₀).Mode)(P:I→T→ℂ)(W:T):
    (mass c s)⁻¹*(∏i∈s.val,c i*P i W)=∏i∈s.val,P i W:=by
  have nz:mass c s≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>nonzero i)
  rw [Finset.prod_mul_distrib]
  exact inv_mul_cancel_left₀ nz _

theorem original (d:I → ℕ)(simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (pace:WilsonWindowReportingPace.Slow R.kit)(cater:Cater (C) R.doors)
    (wage:WilsonReportLampForecast.Ready (A))
    (nested:WilsonPositionProgramNestedLengths.Nested R.rolls)(window target t:ℕ):
    ∀ᶠ j:ℕ in atTop,∀ N p f (height:j≤f) (live:f<N)
      (V:∀i,Sight (C) (d i) p)(r:∀i,Emblems (C) (d i))(home:∀i,Opened (C) (d i) f p)
      (_enrolled:∀i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p (d i)
        (digits R N p 0) (V i) (r i))
      (x:∀i,(C).label (d i))(turn:I → Motion)(o:I → Site ((C).side f p))
      (route:∀u,X → Site ((C).side u p)),
    let P:=(C).path.rep N p f
    let y:=fun i=>offer R (x i) (home i) live.le
    let data:=fun i=>reduce (y i)
    let arm:=fun i=>marked R (N:=N) 0 (turn i) (o i) (V i) (r i) (data i) f
    WilsonThermometerReflectedRoster.filed R d (fun _=>0) turn o data V r J₀ live.le t →
    (C).S.a j/(C).S.a f≤(H f)^window → ((A).params f).supportExponent=100 →
    5≤P.p.B → (∀a b:I,a≠b → P.p.B^2+1≤ separation (o a) (o b)) →
    route f=(o∘Prod.fst) ∘ Prod.snd →
    (∀v,j≤v → v<f → route v=((A).clock.op v p).ratio.parent ∘ route (v+1)) →
    2≤((A).budget j).supportExponent → ∀endpoint:Config G ((C).side j p),
    flags ((C).path.rep N p j).p.threshold endpoint=∅ → ∀s:(J₀).Mode,
    ∀V₀:Fin 3→ℝ,(∀i,charge (y i)≤ max 1 (2*V₀ i)) →
    let Y:=fun i=>displayed R (d i) (x i) (turn i)
    ∀(dose:I→ℂ), (∀a,dose a≠0) →
    let charged:=fun U=>∏i∈s.val,(dose i*(charge (y i):ℂ))*(arm i).2.1 U
    Restart R d simple (N:=N) height Y o s endpoint (fun U=>(mass dose s)⁻¹*charged U) ((∏i∈s.val,max 1 (2*V₀ i))*((H f)^target)⁻¹):=by
  filter_upwards [WilsonOriginalMicroscopicEntrancePublicTrial.original R d simple shop pace cater wage nested window target t] with j bought
  intro N per f height live V r home enrolled x turn o route P y data arm posted length aperture width apart
    current walk older endpoint clear s V₀ earned Y dose nonzero charged
  have eq:(fun U=>(mass dose s)⁻¹*charged U)=fun U=>∏i∈s.val,(charge (y i):ℂ)*(arm i).2.1 U:=by
    funext U
    simpa only [charged,mul_assoc] using field dose nonzero s (fun i U=>(charge (y i):ℂ)*(arm i).2.1 U) U
  rw [eq]
  exact @bought N per f height live V r home enrolled x turn o route posted length aperture width apart
    current walk older endpoint clear s V₀ earned

end YM.Integration.WilsonOriginalMicroscopicEntranceDosePublic
end
