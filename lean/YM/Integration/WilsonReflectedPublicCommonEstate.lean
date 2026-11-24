import YM.Integration.WilsonReflectedPublicDoseRoster
import YM.Integration.WilsonReflectedPublicCommonCoupon
import YM.Integration.WilsonReflectedPublicNamedEstate

/-! The common-dose measured school for the actual public reflected fields, their entire old deposit and the guarded original K trial. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicCommonEstate
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open Next.Rank Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open WilsonReflectedOpticalArm WilsonReflectedFullPanel WilsonReflectedFundedHearing
open WilsonOriginalMicroscopicGuardedPage WilsonReflectedRestoredStation
open scoped Topology Classical
variable {G:Gauge} {R:Run G} {order:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family order S) {l:Ultrafilter (ℕ×ℕ)} {z:Trace.Terrace.Arch R.family}
    {H:(Bel R.family.book).Hierarchy}
local notation "C₀" => R.family
local notation "lev" => R.family.path.levels
local notation "mesh" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta

open Extra.Histories.Motion RG05Readout.Address MergeProof Push.Local
open WilsonReflectedFundedHearing WilsonReflectedFullPanel WilsonReflectedAffordableArm
open FVA2.Register MS PhysMS Frame WilsonReflectedPublicGuardedEstate
variable (J:ℝ→tower S)(Z:WilsonPrescription G)
def Ready {N p f K d:ℕ} (q:ℕ)(B:ℝ)(power:ℕ)(C:ℝ)
    (Y:(C₀).label d)(j:ℕ)(pay:ℝ)(M:(C₀).label d ≃ₗ[ℂ] (C₀).label d)
    (V:Sight C₀ d p)(u:Emblems C₀ d)(est:Opened C₀ d f p)
    (h:f<K)(top:K≤N)(turn:Motion)(point₀:Site ((C₀).side f p)):Prop:=
  let y:=offer R Y est (h.le.trans top)
  let χ:=WilsonThermometerMarchSource.charge y
  let c:=WilsonReflectedPublicCommonDose.dose χ C pay
  let θ:ℂ:=(c*χ:ℝ)
  let wage:=WilsonReflectedPublicMountedInvoice.wage R f
  let Ω:=orbitCost ((C₀).labels.level d)
  ∃A:Arm R d N p f K,A.Y=Y ∧ A.w=M.symm (WilsonOriginalMicroscopicGuardedPage.full R d N p j Y) ∧
    A.b=turn.2 ∧ A.s=turn.1 ∧ A.o=point₀ ∧
    (∃L:Arm R d N p K K,WilsonReflectedRestoredStation.Situated R h.le A L) ∧
    ∃Q E,WilsonReflectedPublicGuardedColumns.Joined R A h.le top (c:ℂ)
      (marked R (N:=N) 0 turn point₀ V u (θ • reduce y) f) wage (Ω*(1+wage))
      ((2+Ω)*((β f)^q)⁻¹) Q E ∧
    ((C₀).labels.level d).coeffSize
      (((c:ℂ)*(((mesh K:ℂ)^d)⁻¹)) • WilsonReflectedPublicGuardedMotion.coords R A) ≤ B*(β K)^power

theorem original (simple:G.Simple) (bliss:Bliss F l z H) (lead:Leading F J)
    (obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) (slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (width:∀i,1≤((lev).budget i).supportExponent)(capWidth:∀i,((lev).budget i).supportExponent≤100)
    (law:OPE.Therm.Poetry lev) (D d T q jets:ℕ) (cap:d≤D)
    (y:(Spin.comparator R.family.book).Field d)(x:RG17.Free (C₀) d):
    ∃t≥D+3, ∃C:ℝ,0<C ∧ ∃B:ℝ,0<B ∧ ∃power:ℕ,∀ᶠ r in trail, ∀{k:ℕ}
      {stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T)}
      {W:Vane R.family k}{fits:D≤k}{U:Spin.change S d}
      (P:Pair F stock cap W fits U r),W.checked order H k→W.wheel.r=r→
    let m:=max stock.j W.k
    let f:=WilsonInvariantActionPosition.berth R 5 m
    let K:=WilsonInvariantActionPosition.berth R (WilsonReflectedOpticalRate.depth (q+1+2) (2*T+9) D) f
    ∃h:f<K, ∃_start:∀b,station F P b≤f, ∀N p (top:K≤N),
    ∃(V:Sight C₀ d p)(u:Emblems C₀ d)(est:Opened C₀ d f p),
    Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p d (digits R N p 0) V u ∧
    ∃M:Bool→(C₀).label d ≃ₗ[ℂ] (C₀).label d,
      ∀(I:Type)[Fintype I][DecidableEq I](weak:I → Bool)(turn:I → Motion)(o:I → Site ((C₀).side f p)),
        (∀i j:I,i≠j → ((lev).budget f).B^2 < separation (o i) (o j)) →
        let names:=Stock.census I
        let probe:=fun i=>WilsonOriginalTwoFlatPublicNamedFare.chosen F J Z r U (weak i) y x
        let source:=fun i=>(P.arm (weak i) (probe i)).source (N,p)
        let val:=fun i=>offer R (source i) est (h.le.trans top)
        let χ:=fun i=>WilsonThermometerMarchSource.charge (val i)
        let pay:=fun i=>fee F P (weak i) (probe i)
        let c:=fun i=>WilsonReflectedPublicCommonDose.dose (χ i) C (pay i)
        let data:=fun i=>((c i*χ i:ℝ):ℂ) • reduce (val i)
        (∀i,(c i)⁻¹ ≤ max (max 1 (2*(β f)^((2*T+9)*(d+1))*pay i)) (C*pay i)) ∧
        WilsonThermometerReflectedRoster.filed R (fun _:I=>d) (fun _=>0) turn o data (fun _=>V)
          (fun _=>u) names (h.le.trans top) t ∧
        (∀j (hj:j ≤ N)(s:names.Mode) L,
          (WilsonThermometerReflectedRoster.density R (fun _:I=>d) (fun _=>0) turn o data
            (fun _=>u) names (h.le.trans top) hj L).part s =
            ((C₀).path.rep N p j).eval L • actualTransport C₀ (N:=N)
            (fun U=>∏i∈s.val,(c i:ℂ)*(C₀).O N p (displayed R d (source i) (turn i))
              (anchorAt R (o i) N) U) hj L) ∧
        ∀i,Ready (R:=R) q B power C (source i) (station F P (weak i)) (pay i)
          (M (weak i)) V u est h top (turn i) (o i):=by
  obtain ⟨t₀,_,C,cp,goods⟩:=WilsonReflectedPublicPairedStocks.original F simple bliss slow shop width capWidth law D d T q jets cap
  obtain ⟨t,dt,events⟩:=WilsonReflectedPublicDoseRoster.original R simple shop D
  obtain ⟨k₀,late⟩:=eventually_atTop.mp events
  obtain ⟨B,bp,power,cash⟩:=WilsonReflectedPublicNamedTrialCapital.original F J Z simple bliss lead obedient slow capWidth D d T q cap y x
  let bound:=(Finset.range (d+1)).sup (C₀).ref
  refine ⟨t,dt,C,cp,B,bp,power,?_⟩
  filter_upwards [goods,cash,WilsonReflectedPublicStationLate.original F simple bliss T (max bound k₀)]
    with r bought paid stationReady k stock W fits U P checked atR m f K
  obtain ⟨h,start,issued⟩:=bought P checked atR
  have enough:max bound k₀ ≤ f:=(stationReady P checked atR false).trans (start false)
  have byStage:k₀ ≤ f:=(le_max_right ..).trans enough
  refine ⟨h,start,?_⟩
  intro N p high
  obtain ⟨V,u,est,enrolled,M,old,sale⟩:=issued N p high
  refine ⟨V,u,est,enrolled,M,?_⟩
  intro I fi di weak turn o apart names probe source val χ pay c data
  let cut:=h.le.trans high
  have refs (e:ℕ)(he:e ≤ d):(C₀).ref e ≤ N:=
    (Finset.le_sup (f:=(C₀).ref) (Finset.mem_range.mpr (Nat.lt_succ_of_le he))).trans
      ((le_max_left bound k₀).trans (enough.trans cut))
  obtain ⟨charges,oldPost,_⟩:=old.2 I weak probe turn o names apart
  obtain ⟨posted,faces⟩:=late f byStage p N cut I (fun _=>d) (fun _=>cap) source (fun _=>V) (fun _=>u)
    (fun _=>est) (fun _=>enrolled) (fun _=>refs) turn o apart names (fun _=>C) pay
  refine ⟨?_,posted,faces,?_⟩
  · intro i
    change (WilsonReflectedPublicCommonDose.dose (χ i) C (pay i))⁻¹ ≤ _
    rw [WilsonReflectedPublicCommonDose.refund]
    unfold WilsonReflectedPublicCommonDose.denominator
    apply max_le_max _ le_rfl
    exact max_le (le_max_left ..) (charges i)
  · intro i
    have heard:=WilsonReflectedPublicFiledSingle.original R (fun _:I=>d) source (fun _=>V) (fun _=>u)
      (fun _=>est) cut (fun _=>enrolled) (fun _=>refs) turn o names t₀ oldPost i
    obtain ⟨ticket,A,src,w,side,motion,loc,situation,X,E,joined⟩:=
      WilsonReflectedPublicCommonCoupon.original (R:=R) t₀ T q jets C (fun b v=>(P.arm b v).source (N,p))
        (fee F P) (station F P) V u est M h start high old sale (weak i) (probe i) (turn i) (o i) heard
    have good:=WilsonReflectedPublicCommonDose.smaller (χ i) C (pay i) (le_max_left ..)
    have small:‖(c i:ℂ)‖ ≤ 1:=by rw [Complex.norm_real,Real.norm_of_nonneg (WilsonReflectedPublicCommonDose.positive ..).le];exact good.1
    obtain ⟨_,salary⟩:=paid P checked atR (weak i)
    exact ⟨A,src,w,side,motion,loc,situation,X,E,joined,salary N p high (M (weak i)) jets ticket A w (c i:ℂ) small⟩

end YM.Integration.WilsonReflectedPublicCommonEstate
end
