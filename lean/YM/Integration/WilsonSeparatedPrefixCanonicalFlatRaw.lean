import YM.Integration.WilsonSeparatedPrefixCanonicalPublicHearing
import YM.Integration.WilsonSeparatedPrefixCohortIncome
/-! Two genuine earlier flat readings of the actual displaced, oriented and
normalized public cutoff fields. The elected roster includes all proper faces. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalFlatRaw
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
    let arm:=fun i=>marked R (N:=N) 0 (turn i) (o i) (V i) (r i) (data i) f
    WilsonThermometerReflectedRoster.filed R d (fun _=>0) turn o data V r J₀ live.le t →
    l≤room → (C).S.a j/(C).S.a f≤(H f)^window → ((A).params f).supportExponent=100 →
    5≤P.p.B → (∀a b:I,a≠b → P.p.B^2+1≤ separation (o a) (o b)) →
    route f=(o∘Prod.fst) ∘ Prod.snd →
    (∀v,j+1≤v → v<f → route v=((A).clock.op v p).ratio.parent ∘ route (v+1)) →
    (∀i,coverNumber ((C).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    ∀u:ℕ,(C).ref 0≤u → ∀uj:u≤j,Opened (C) 0 u p → Opened (C) 0 j p → ∀s:(J₀).Mode,
      let source:=fun W=>∏i∈s.val,(C).O N p (displayed R (d i) (x i) (turn i)) (b i) W
      let seen:=actualTransport (C) (N:=N) source live.le
      let masked:=fun U=>∏i∈s.val,((charge (y i):ℝ):ℂ)*(arm i).2.1 U
      Integrable (fun U=>(P.eval U:ℂ)*masked U) (prior G _) ∧
      ‖actualTransport (C) (N:=N) (fun U=>seen U-masked U) (uj.trans (by omega:f≥j)) 1‖≤
        (∏i∈s.val,charge (y i))*((H f)^target)⁻¹:=by
  have refs:=Filter.eventually_all.mpr (fun i:I=>eventually_ge_atTop ((C).ref (d i)))
  obtain ⟨j₀,market⟩:=eventually_atTop.mp (WilsonSeparatedPrefixCanonicalPublicSale.original R d simple shop)
  filter_upwards [WilsonSeparatedPrefixCanonicalPublicHearing.original R d simple shop pace cater bank wage nested window room target t,
    refs,eventually_ge_atTop j₀] with j quoted here ready N p f height live l V r home enrolled x turn o route anchor P y data b arm filed housed span fixed width apart course ancestor housing zero u hu uj ou oj s source seen masked
  have jf:j≤f:=by omega
  let pixels:=fun i U=>(C).O N p (displayed R (d i) (x i) (turn i)) (b i) U
  let φ:=fun i=>(arm i).2.1
  let χ:=fun i=>charge (y i)
  have pos(i):0<χ i:=WilsonThermometerMarchSource.charged (y i)
  have price:=quoted N p f height live l V r home enrolled x turn o route anchor filed housed span fixed width apart course ancestor housing zero u hu uj ou oj s
  obtain ⟨q,fmt,_,bounded,_,bright,_,_,_⟩:=market f (ready.trans jf) N p live V r home enrolled x turn o t filed
  have ref(i): (C).ref (d i)≤f:=(here i).trans jf
  have board:P.p=(A).budget f:=(R.makes.wilson.represents N p f live.le).vac
  have exactWidth:P.p.supportExponent=100:=by
    rw [board]
    exact fixed
  have small:1≤P.p.supportExponent:=by rw [exactWidth];norm_num
  have a₀:φ=fun i=>(q i).exponentialEntry (o i) ((C).localSection (d i)) P:=funext bright
  have finite:Integrable (fun U=>(P.eval U:ℂ)*WilsonSeparatedPrefixCohortUnscale.product s.val φ U) (prior G _):=by
    rw [a₀]
    exact WilsonSeparatedPrefixCohortIncome.original R live.le ref o q fmt bounded small s.val
  let c:ℂ:=∏i∈s.val,(χ i:ℂ)
  constructor
  · convert finite.smul c using 1
    funext U
    simp only [masked,c,χ,φ,WilsonSeparatedPrefixCohortUnscale.product,
      Finset.prod_mul_distrib,Pi.smul_apply,smul_eq_mul]
    ring
  · have boundedPixels(i:I):WilsonOriginalMicroscopicEntranceDeposits.funded (pixels i):=by
      have smooth:=(C).continuousO N p (d i) (displayed R (d i) (x i) (turn i)) (b i)
      obtain ⟨M,cash⟩:=(isCompact_range smooth.norm).bddAbove
      exact ⟨smooth.measurable,M,fun U=>cash ⟨U,rfl⟩⟩
    have rested:=WilsonSeparatedPrefixCohortUnscale.held R live.le (uj.trans jf) s.val pixels boundedPixels φ finite χ pos 1
    change actualTransport (C) (N:=N) (fun U=>seen U-masked U) (uj.trans (by omega:f≥j)) 1=c*(_-_) at rested
    rw [rested,norm_mul]
    have cash:‖c‖=∏i∈s.val,χ i:=by
      simp only [c,norm_prod,Complex.norm_real]
      exact Finset.prod_congr rfl (fun i _=>Real.norm_of_nonneg (pos i).le)
    rw [cash]
    exact mul_le_mul_of_nonneg_left price (Finset.prod_nonneg (fun i _=>(pos i).le))

end YM.Integration.WilsonSeparatedPrefixCanonicalFlatRaw
