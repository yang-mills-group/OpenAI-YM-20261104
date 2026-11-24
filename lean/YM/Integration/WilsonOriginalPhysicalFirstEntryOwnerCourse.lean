import YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerHearing
import YM.Integration.WilsonReflectedPublicChargedRoster

/-! Issue the reflected finite physical sources at their real cutoff and period,
then sell their first signed owner withdrawal at the two original flats. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerCourse
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
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta

theorem original (D:ℕ)(simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (pace:WilsonWindowReportingPace.Slow R.kit)(cater:Cater (C) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(wage:WilsonReportLampForecast.Ready (A))
    (nested:WilsonPositionProgramNestedLengths.Nested R.rolls):
    ∃t≥D+3,∀(I:Type)[Fintype I][DecidableEq I](d:I→Fin (D+1))(window room target:ℕ),
    ∀ᶠ j:ℕ in atTop,∀ N p f (_height:j+2≤f) (live:f<N),
    ∃(V:(a:Fin (D+1))→Sight (C) a.val p)(r:(a:Fin (D+1))→Emblems (C) a.val)
      (home:∀a:Fin (D+1),Opened (C) a.val f p),
    (∀a,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p a.val
      (digits R N p 0) (V a) (r a)) ∧
    ∀(x:∀i,(C).label (d i).val)(turn:I→Motion)(o:I→Site ((C).side f p))
      (l:ℕ)(route:∀v,Unit×(I×Bool)→Site ((C).side v p))(anchor:Unit×(I×Bool)),
    let P:=(C).path.rep N p f
    let y:=fun i=>offer R (x i) (home (d i)) live.le
    let data:=fun i=>reduce (y i)
    let b:=fun i=>WilsonThermometerReflectedTrajectory.anchorAt R (o i) N
    let F:=WilsonThermometerReflectedRoster.density R (fun i=>(d i).val) (fun _=>0) turn o data
      (fun i=>r (d i)) (Marks I) live.le live.le
    l≤room → (C).S.a j/(C).S.a f≤(H f)^window → ((A).params f).supportExponent=100 →
    5≤P.p.B → (∀a b:I,a≠b → P.p.B^2+1≤ separation (o a) (o b)) →
    route f=(o∘Prod.fst) ∘ Prod.snd →
    (∀v,j+1≤v → v<f → route v=((A).clock.op v p).ratio.parent ∘ route (v+1)) →
    (∀i,coverNumber ((C).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    (∀i,charge (y i) ≤ max 1 (2*((C).S.a f^(d i).val)⁻¹*Next.UVStress.quota (C) (d i).val f N p (x i))) ∧
    WilsonThermometerReflectedRoster.filed R (fun i=>(d i).val) (fun _=>0) turn o data
        (fun i=>V (d i)) (fun i=>r (d i)) (Marks I) live.le t ∧
    ∃q:∀i,Coefficient ((C).labels.level (d i).val) ((C).side f p),
      let φ:=fun v=>(q v).exponentialEntry (o v) ((C).localSection (d v).val) P
      WilsonOriginalPhysicalFirstEntryOwnerLedger.Priced (P:=P) (o:=o) q φ F
        (fun _=>(H f^t)⁻¹) (LocalComparison.forcedDivisor (C) f)
        (fun _=>WilsonReflectedPublicMountedInvoice.wage R f) ∧
      (∀s:(Marks I).Mode,∀U,(F U).part s=P.eval U • actualTransport (C) (N:=N)
        (fun W=>∏i∈s.val,((charge (y i):ℝ):ℂ)⁻¹*(C).O N p (displayed R (d i).val (x i) (turn i)) (b i) W) live.le U) ∧
      ∀u:ℕ,(C).ref 0≤u → ∀uj:u≤j,Opened (C) 0 u p → Opened (C) 0 j p → ∀s:(Marks I).Mode,
        ‖reading R (N:=N) (fun U=>(F U).part s) u (uj.trans (by omega))-
          reading R (N:=N) (fun U=>(P.eval U:ℂ)*∏v∈s.val,φ v U) u (uj.trans (by omega))‖≤((H f)^target)⁻¹:=by
  obtain ⟨t,deep,issued⟩:=WilsonReflectedPublicChargedRoster.original R simple shop D
  obtain ⟨f₀,bought⟩:=eventually_atTop.mp issued
  refine ⟨t,deep,?_⟩
  intro I fi di d window room target
  filter_upwards [eventually_ge_atTop f₀,WilsonOriginalPhysicalFirstEntryOwnerHearing.original R
    (fun i=>(d i).val) simple shop pace cater bank wage nested window room target t] with j late hear N p f height live
  obtain ⟨V,r,home,enrolled,sale⟩:=bought f (by omega) p N live
  refine ⟨V,r,home,enrolled,?_⟩
  intro x turn o l route anchor P y data b F rooms span fixed width apart first chain located zero
  have budget:P.p=(A).budget f:=(R.makes.wilson.represents N p f live.le).vac
  have physical a b (ab:a≠b):((A).budget f).B^2 <
      separation (point R (N:=N) 0 (turn a) (o a) f) (point R (N:=N) 0 (turn b) (o b) f):=by
    rw [WilsonReflectedPublicOpticalJoint.location R live.le,WilsonReflectedPublicOpticalJoint.location R live.le,←budget]
    exact apart a b ab
  have given:=sale I d x turn o (Marks I) physical
  refine ⟨given.1,given.2.1,?_⟩
  exact hear N p f height live l (fun i=>V (d i)) (fun i=>r (d i))
    (fun i=>home (d i)) (fun i=>enrolled (d i)) x turn o route anchor given.2.1 rooms span fixed width apart first chain located zero

end YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerCourse
