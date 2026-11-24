import YM.Integration.WilsonReflectedPublicGuardedEstate
import YM.Integration.WilsonReflectedPublicNamedTrialCapital
/-! A preappointed reflected physical panel with its actual occupied history and
both signed native replacements at the one common optical cutoff. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicNamedEstate
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
private theorem charge_le_one {c:ℝ}(hc:1≤c):‖(c:ℂ)⁻¹‖≤1:=by
  have pos:0<c:=lt_of_lt_of_le (by norm_num:(0:ℝ)<1) hc
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos]
  exact inv_le_one_of_one_le₀ hc

def Ready {N p f K d:ℕ} (q:ℕ)(B:ℝ)(power:ℕ)(C:ℝ)
    (Y:(C₀).label d)(j:ℕ)(pay:ℝ)(M:(C₀).label d ≃ₗ[ℂ] (C₀).label d)
    (V:Sight C₀ d p)(u:Emblems C₀ d)(est:Opened C₀ d f p)
    (h:f<K)(top:K≤N)(turn:Motion)(c:Site ((C₀).side f p)):Prop:=
  let y:=offer R Y est (h.le.trans top)
  let dose:=((charge y:ℝ):ℂ)⁻¹
  let wage:=WilsonReflectedPublicMountedInvoice.wage R f
  let Ω:=orbitCost ((C₀).labels.level d)
  ∃A:Arm R d N p f K,A.Y=Y ∧ A.w=M.symm (WilsonOriginalMicroscopicGuardedPage.full R d N p j Y) ∧
    A.b=turn.2 ∧ A.s=turn.1 ∧ A.o=c ∧
    (∃L:Arm R d N p K K,WilsonReflectedRestoredStation.Situated R h.le A L) ∧
    ∃Q E,WilsonReflectedPublicGuardedColumns.Joined R A h.le top dose
      (marked R (N:=N) 0 turn c V u (reduce y) f) wage (Ω*(1+wage))
      ((2+Ω)*C*((β f)^q)⁻¹*pay) Q E ∧
    ((C₀).labels.level d).coeffSize
      ((dose*(((mesh K:ℂ)^d)⁻¹)) • WilsonReflectedPublicGuardedMotion.coords R A) ≤ B*(β K)^power

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
    ∃h:f<K, ∃start:∀b,station F P b≤f, ∀N p (top:K≤N),
    ∃(V:Sight C₀ d p)(u:Emblems C₀ d)(est:Opened C₀ d f p),
    Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p d (digits R N p 0) V u ∧
    ∃M:Bool→(C₀).label d ≃ₗ[ℂ] (C₀).label d,
      Dossier (R:=R) t T q jets C (fun b v=>(P.arm b v).source (N,p)) (fee F P)
        (station F P) V u est M h start top
      ∧ ∀(I:Type)[Fintype I][DecidableEq I](weak:I→Bool)(turn:I→Motion)
          (o:I→Site ((C₀).side f p)),
        (∀i j:I,i≠j → ((lev).budget f).B^2 < separation (o i) (o j)) →
        let names:=Stock.census I
        let probe:=fun i=>WilsonOriginalTwoFlatPublicNamedFare.chosen F J Z r U (weak i) y x
        let source:=fun i=>(P.arm (weak i) (probe i)).source (N,p)
        let data:=fun i=>reduce (offer R (source i) est (h.le.trans top))
        WilsonThermometerReflectedRoster.filed R (fun _:I=>d) (fun _=>0) turn o data (fun _=>V)
          (fun _=>u) names (h.le.trans top) t ∧
        ∀i,Ready (R:=R) q B power C (source i) (station F P (weak i)) (fee F P (weak i) (probe i))
          (M (weak i)) V u est h top (turn i) (o i):=by
  obtain ⟨t,dt,C,cp,estate⟩:=WilsonReflectedPublicGuardedEstate.original F simple bliss slow shop width capWidth law D d T q jets cap
  obtain ⟨B,bp,power,salary⟩:=WilsonReflectedPublicNamedTrialCapital.original F J Z simple bliss lead obedient slow capWidth D d T q cap y x
  refine ⟨t,dt,C,cp,B,bp,power,?_⟩
  filter_upwards [estate,salary] with r available priced k stock W fits U P check exactly m f K
  obtain ⟨h,start,stored⟩:=available P check exactly
  refine ⟨h,start,?_⟩
  intro N p high
  obtain ⟨V,u,est,paid,M,both⟩:=stored N p high
  refine ⟨V,u,est,paid,M,both,?_⟩
  intro I fi di weak turn o apart names probe source data
  obtain ⟨_,filed,slots,_⟩:=both I weak probe turn o names apart
  refine ⟨filed,?_⟩
  intro i
  obtain ⟨ticket,A,old,weight,flip,rotate,site,placed,Q,E,joined⟩:=slots i
  obtain ⟨before,bill⟩:=priced P check exactly (weak i)
  let dose:=((charge (offer R (source i) est (h.le.trans high)):ℝ):ℂ)⁻¹
  have small:‖dose‖≤1:=charge_le_one (le_max_left ..)
  have wallet:=bill N p high (M (weak i)) jets ticket A weight dose small
  exact ⟨A,old,weight,flip,rotate,site,placed,Q,E,joined,wallet⟩

end YM.Integration.WilsonReflectedPublicNamedEstate
end
