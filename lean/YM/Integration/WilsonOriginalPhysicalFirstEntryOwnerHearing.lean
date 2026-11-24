import YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerSale
import YM.Integration.WilsonSeparatedPrefixCanonicalPublicHearing

/-! The original N-born word, its actual hard and mixed owner ledger and its
single signed withdrawal at either eligible flat, for every physical subface. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerHearing
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
open WilsonThermometerUnitFilingCoarse WilsonReflectedPublicOrientedFaces
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta
local notation "J₀" => Marks I
local notation "X" => Unit×(I×Bool)

theorem original (d:I → ℕ)(simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (pace:WilsonWindowReportingPace.Slow R.kit)(cater:Cater (C) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(wage:WilsonReportLampForecast.Ready (A))
    (nested:WilsonPositionProgramNestedLengths.Nested R.rolls)(window room target t:ℕ):
    ∀ᶠ j:ℕ in atTop,∀ N p f (_height:j+2≤f) (live:f<N)(l:ℕ)
      (V:∀i,Sight (C) (d i) p)(r:∀i,Emblems (C) (d i))(home:∀i,Opened (C) (d i) f p)
      (_enrolled:∀i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p (d i)
        (digits R N p 0) (V i) (r i))
      (x:∀i,(C).label (d i))(turn:I → Motion)(o:I → Site ((C).side f p))
      (route:∀u,X → Site ((C).side u p))(anchor:X),
    let P:=(C).path.rep N p f
    let y:=fun i=>offer R (x i) (home i) live.le
    let data:=fun i=>reduce (y i)
    let b:=fun i=>WilsonThermometerReflectedTrajectory.anchorAt R (o i) N
    let F:=WilsonThermometerReflectedRoster.density R d (fun _=>0) turn o data r J₀ live.le live.le
    WilsonThermometerReflectedRoster.filed R d (fun _=>0) turn o data V r J₀ live.le t →
    l≤room → (C).S.a j/(C).S.a f≤(H f)^window → ((A).params f).supportExponent=100 →
    5≤P.p.B → (∀a b:I,a≠b → P.p.B^2+1≤ separation (o a) (o b)) →
    route f=(o∘Prod.fst) ∘ Prod.snd →
    (∀v,j+1≤v → v<f → route v=((A).clock.op v p).ratio.parent ∘ route (v+1)) →
    (∀i,coverNumber ((C).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    ∃q:∀i,Coefficient ((C).labels.level (d i)) ((C).side f p),
      let φ:=fun v=>(q v).exponentialEntry (o v) ((C).localSection (d v)) P
      WilsonOriginalPhysicalFirstEntryOwnerLedger.Priced (P:=P) (o:=o) q φ F
        (fun _=>(H f^t)⁻¹) (LocalComparison.forcedDivisor (C) f)
        (fun _=>WilsonReflectedPublicMountedInvoice.wage R f) ∧
      (∀s:(J₀).Mode,∀U,(F U).part s=P.eval U • actualTransport (C) (N:=N)
        (fun W=>∏i∈s.val,((charge (y i):ℝ):ℂ)⁻¹*(C).O N p (displayed R (d i) (x i) (turn i)) (b i) W) live.le U) ∧
      ∀u:ℕ,(C).ref 0≤u → ∀uj:u≤j,Opened (C) 0 u p → Opened (C) 0 j p → ∀s:(J₀).Mode,
        ‖reading R (N:=N) (fun U=>(F U).part s) u (uj.trans (by omega))-
          reading R (N:=N) (fun U=>(P.eval U:ℂ)*∏v∈s.val,φ v U) u (uj.trans (by omega))‖≤((H f)^target)⁻¹:=by
  obtain ⟨f₀,original⟩:=eventually_atTop.mp (WilsonOriginalPhysicalFirstEntryOwnerSale.original R d simple shop)
  have goals:=Filter.eventually_all.mpr (fun i:I=>Filter.eventually_all.mpr (fun e:Fin (d i+1)=>eventually_ge_atTop ((C).ref e.val)))
  obtain ⟨f₁,age⟩:=eventually_atTop.mp goals
  filter_upwards [WilsonSeparatedPrefixCanonicalTwoFlat.original R d simple pace cater bank wage nested window (t+4) room target,
    eventually_ge_atTop (max f₀ f₁),(RG01.Physical.hats simple (A)).eventually_ge_atTop 1] with j ear late warm
  intro N p i
  cases i with
  | zero => intro h;omega
  | succ k =>
    intro height live l V r home enrolled x turn o route anchor P y data b F filed housed span fixed size apart course parent housing zero
    let f:=k+1
    have hp:1≤H f:=warm.trans (WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le (by dsimp [f];omega))
    have ref(i)(e:ℕ)(he:e≤d i):(C).ref e≤f:=age f (by dsimp [f];omega) i ⟨e,by omega⟩
    obtain ⟨q,fit,head,paid,Bcap,bright,keys,whole,purchase⟩:=original f (by dsimp [f];omega) N p live V r home enrolled x turn o t fixed filed
    let B:=WilsonReflectedPublicMountedInvoice.wage R f
    have Bprice:(H f)^4≤(H f)^(t+4):=pow_le_pow_right₀ hp (by omega)
    have inverse:((H f^t)⁻¹)⁻¹≤(H f)^(t+4):=by rw [inv_inv];exact pow_le_pow_right₀ hp (by omega)
    have hp':0<H f:=zero_lt_one.trans_le hp
    refine ⟨q,purchase,?_,?_⟩
    · intro s
      exact WilsonReflectedPublicOrientedFaces.original R d x V r home live.le enrolled
        (fun i e he=>(ref i e he).trans live.le) turn o J₀ t filed f live.le s
    · exact ear N p k height (by omega) l o (fun _=>(H f^t)⁻¹) (fun _=>B)
        route anchor q F housed span (fun _=>inverse) (fun i=>(head i).trans Bprice) (fun _=>Bcap.trans Bprice)
        fixed (fun _=>inv_pos.mpr (pow_pos hp' _)) (fun i=>ref i (d i) le_rfl) fit paid
        (WilsonOriginalPhysicalFirstEntryOwnerLedger.served q _ F _ _ _ purchase) size apart course parent housing zero

end YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerHearing
