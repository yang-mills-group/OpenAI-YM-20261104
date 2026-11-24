import YM.Integration.WilsonSeparatedPrefixCanonicalClearRate
import YM.Integration.WilsonSeparatedPrefixCanonicalPublicSale

/-! Two genuine earlier flat readings of the actual displaced, oriented and
normalized public cutoff fields. The elected roster includes all proper faces. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalClearPublic
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
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta
local notation "J₀" => Marks I
local notation "X" => Unit×(I×Bool)

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
    let b:=fun i=>WilsonThermometerReflectedTrajectory.anchorAt R (o i) N
    let arm:=fun i=>marked R (N:=N) 0 (turn i) (o i) (V i) (r i) (data i) f
    WilsonThermometerReflectedRoster.filed R d (fun _=>0) turn o data V r J₀ live.le t →
    (C).S.a j/(C).S.a f≤(H f)^window → ((A).params f).supportExponent=100 →
    5≤P.p.B → (∀a b:I,a≠b → P.p.B^2+1≤ separation (o a) (o b)) →
    route f=(o∘Prod.fst) ∘ Prod.snd →
    (∀v,j≤v → v<f → route v=((A).clock.op v p).ratio.parent ∘ route (v+1)) →
    2≤((A).budget j).supportExponent → ∀endpoint:Config G ((C).side j p),
    flags ((C).path.rep N p j).p.threshold endpoint=∅ → ∀s:(J₀).Mode,
      ‖readingAt R (N:=N) (fun U=>P.eval U • actualTransport (C) (N:=N)
          (fun W=> ∏i∈s.val,((charge (y i):ℝ):ℂ)⁻¹*(C).O N p (displayed R (d i) (x i) (turn i)) (b i) W) live.le U)
          height endpoint-
       readingAt R (N:=N) (fun U=>(P.eval U:ℂ)*∏i∈s.val,(arm i).2.1 U) height endpoint‖≤((H f)^target)⁻¹:=by
  obtain ⟨f₀,original⟩:=eventually_atTop.mp (WilsonSeparatedPrefixCanonicalPublicSale.original R d simple shop)
  have goals:=Filter.eventually_all.mpr (fun i:I=>Filter.eventually_all.mpr (fun e:Fin (d i+1)=>eventually_ge_atTop ((C).ref e.val)))
  obtain ⟨f₁,age⟩:=eventually_atTop.mp goals
  filter_upwards [WilsonSeparatedPrefixCanonicalClearRate.original R d simple pace cater wage nested window (t+4) target,
    eventually_ge_atTop (max f₀ f₁),eventually_ge_atTop 1,(RG01.Physical.hats simple (A)).eventually_ge_atTop 1] with j ear late born warm
  intro N p i
  cases i with
  | zero => intro h;omega
  | succ k =>
    intro height live V r home enrolled x turn o route P y data b arm filed span fixed size apart course parent alpha endpoint clearW s
    let f:=k+1
    have hp:1≤H f:=warm.trans (WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le (by dsimp [f];omega))
    have ref(i)(e:ℕ)(he:e≤d i):(C).ref e≤f:=age f (by dsimp [f];omega) i ⟨e,by omega⟩
    obtain ⟨q,fit,head,paid,Bcap,bright,_,_,stock⟩:=original f (by dsimp [f];omega) N p live V r home enrolled x turn o t filed
    let F:=WilsonThermometerReflectedRoster.density R d (fun _=>0) turn o data r J₀ live.le live.le
    let B:=WilsonReflectedPublicMountedInvoice.wage R f
    have Bprice:(H f)^4≤(H f)^(t+4):=pow_le_pow_right₀ hp (by omega)
    have inverse:((H f^t)⁻¹)⁻¹≤(H f)^(t+4):=by rw [inv_inv];exact pow_le_pow_right₀ hp (by omega)
    have hp':0<H f:=zero_lt_one.trans_le hp
    have cash:=ear N p k height (by omega) o (fun _=>(H f^t)⁻¹) (fun _=>B)
      route q F span (fun _=>inverse) (fun i=>(head i).trans Bprice) (fun _=>Bcap.trans Bprice)
      fixed (fun _=>inv_pos.mpr (pow_pos hp' _)) (fun i=>ref i (d i) le_rfl) fit paid stock size apart course parent alpha endpoint clearW s
    have goods:=WilsonReflectedPublicOrientedFaces.original R d x V r home live.le enrolled
      (fun i e he=>(ref i e he).trans live.le) turn o J₀ t filed f live.le s
    have regular:(fun U=>(P.eval U:ℂ)*∏i∈s.val,(q i).exponentialEntry (o i) ((C).localSection (d i)) P U)=
        (fun U=>(P.eval U:ℂ)*∏i∈s.val,(arm i).2.1 U):=by
      funext U
      refine congrArg (fun z:ℂ=>(P.eval U:ℂ)*z) (Finset.prod_congr rfl ?_)
      intro i _;exact congrFun (bright i).symm U
    exact (congrArg₂ (fun a b=>‖readingAt R (N:=N) a height endpoint-
        readingAt R (N:=N) b height endpoint‖≤((H f)^target)⁻¹)
        (funext goods) regular).mp cash

end YM.Integration.WilsonSeparatedPrefixCanonicalClearPublic
