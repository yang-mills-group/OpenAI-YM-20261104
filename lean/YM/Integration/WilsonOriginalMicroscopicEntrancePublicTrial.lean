import YM.Integration.WilsonOriginalMicroscopicEntranceSettledHeld
import YM.Integration.WilsonOriginalMicroscopicEntrancePublicHeld

/-! An original, publicly enrolled cutoff product and its independently replanted K comparator at one real boundary. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntrancePublicTrial
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
def Restart (d:I→ℕ)(simple:G.Simple){N per f u:ℕ}(uf:u≤f)(Y:∀a:I,(C).label (d a))
    (o:I→Site ((C).side f per))(s:(J₀).Mode)(W:Config G ((C).side u per))
    (b:Config G ((C).side f per)→ℂ)(oldFee:ℝ):Prop:=
  ∀{m k n:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀j,RG.Rep G ((C).side j per))
    (_course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:f+n≤N)
    (_top:Topline (Ψ N) (R.alloy.B.a.clock.forcedAllowance N))
    (_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(_ticket:TicketP R.alloy R.kit D Q)(_floor:m≤u)
    (_fixed:WilsonSingleHardRadius.first R simple≤u)(_capture:WilsonCenteredCaptureClock.first R simple≤f+n)
    {h:I→ℕ}(_κ:(a:I)→Knob (h a))(_pt:I→Chamber)(v:∀a:I,(C).label (d a))
    {t:ℕ}(_before:u+1≤f+n)(_housing:(C).S.a f/(C).S.a (f+n)≤(H (f+n))^t)
    (V:I→ℝ)(_vp:∀a,0≤V a)(_earned:∀a,slotFare R d f (f+n) v a≤((C).S.a f)^(d a)*V a)
    (q:ℕ){ε:ℝ}(positive:0<ε)(_late:(eventually_atTop.mp
      (WilsonOriginalFlatHaloRate.calendar R simple (q+all R d t) positive)).choose≤f+n)
    (c:Config G ((C).side f per)→ℂ)(_right:Integrable (fun U=>((C).path.rep N per f).eval U • c U) (prior G _))
    {trialFee:ℝ}, ‖actualTransport (C) (N:=N) (trialFace R d (N:=N) (n:=n) o v s-c) uf W‖≤trialFee →
    ‖originalRead R d live Y o v s uf W-
      (actualTransport (C) (N:=N) b uf W-actualTransport (C) (N:=N) c uf W)‖≤
    oldFee+trialFee+WilsonOriginalMicroscopicEntranceHeldHalo.spring R u N per W*
      (fare R d V s*((count R d s.val:ℝ)*(4*Real.exp ((R.alloy.B.a.budget (f+n)).supportExponent+2))*(ε/(H (f+n))^q)))

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
    let head:=fun U=>∏i∈s.val,(charge (y i):ℂ)*(arm i).2.1 U
    Restart R d simple (N:=N) height Y o s endpoint head ((∏i∈s.val,max 1 (2*V₀ i))*((H f)^target)⁻¹):=by
  filter_upwards [WilsonOriginalMicroscopicEntrancePublicHeld.original R d simple shop pace cater wage nested
    window target t] with j issued
  intro N per f height live V r home enrolled x turn o route P y data arm posted length aperture width apart
    current walk older endpoint clear s V₀ earned Y head
  obtain ⟨left,debt⟩:=issued N per f height live V r home enrolled x turn o route posted length aperture width
    apart current walk older endpoint clear s V₀ earned
  intro m k n π Γ Ψ course active top way D Q ticket floor fixed capture h κ pt v order before housing V₁ vp
    salary q ε positive late c right trialFee trial
  exact WilsonOriginalMicroscopicEntranceSettledHeld.original R d π Γ Ψ course active top simple way D Q
    ticket floor height fixed capture κ pt Y v o before housing V₁ vp salary q positive late s endpoint head c
    left right debt trial

end YM.Integration.WilsonOriginalMicroscopicEntrancePublicTrial
end
