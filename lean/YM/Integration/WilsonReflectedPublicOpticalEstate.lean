import YM.Integration.WilsonReflectedPublicMountedInvoice
/-! The two separately registered native source coefficients and all original
conditional faces on one and the same previously chosen optical pair. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicOpticalEstate
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
theorem original (simple:G.Simple) (bliss:Bliss F l z H) (slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (D d T:ℕ) (cap:d ≤ D):
    ∃ t ≥ D+3,∀ᶠ r in trail,∀{k:ℕ}
      {stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T)}
      {W:Vane R.family k} {fits:D ≤ k} {U:Spin.change S d}
      (P:Pair F stock cap W fits U r), W.checked order H k → W.wheel.r=r →
    let m:=max stock.j W.k
    let f:=WilsonInvariantActionPosition.berth R 5 m
    ∀p N (deep:f<N),∃ (V:Sight C₀ d p) (u:Emblems C₀ d) (est:Opened C₀ d f p),
      Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p d (digits R N p 0) V u ∧
      (∀ (weak:Bool) (v:S.Field d) (s:Motion) (c:Site (R.family.side f p)),
        let rep:=(C₀).path.rep N p f
        let data:=reduce (offer R ((P.arm weak v).source (N,p)) est deep.le)
        let field:=marked R (N:=N) 0 s c V u data f
        let fee₀:=WilsonReflectedPublicMountedInvoice.wage R f
        ∃q:Coefficient ((C₀).labels.level d) ((C₀).side f p),
          q.Format c (C₀).params rep ∧
          ((C₀).labels.level d).coeffSize q.x≤orbitCost ((C₀).labels.level d)*(1+fee₀) ∧
          q.remBound c rep (kappa (C₀).path f) fee₀ ∧
          field.2.1=q.exponentialEntry c ((C₀).localSection d) rep ∧
          profile rep.activities field.2.2=profile rep.activities q.forced ∧
          q.density c ((C₀).localSection d) rep=field.1) ∧
      ∀(I:Type) [Fintype I] [DecidableEq I] (weak:I→Bool) (v:I→S.Field d) (turn:I→Motion)
        (c:I→Site (R.family.side f p)) (names:Census I),
      (∀i j:I,i≠j → ((lev).budget f).B^2 < separation (c i) (c j)) →
      let x:=fun i=>(P.arm (weak i) (v i)).source (N,p)
      let y:=fun i=>offer R (x i) est deep.le
      let data:=fun i=>reduce (y i)
      (∀i,charge (y i) ≤ max 1 (2*(β f)^((2*T+9)*(d+1))*fee F P (weak i) (v i))) ∧
      WilsonThermometerReflectedRoster.filed R (fun _:I=>d) (fun _=>0) turn c data (fun _=>V) (fun _=>u)
        names deep.le t ∧
      ∀j (hj:j ≤ N) (s:names.Mode) A,
        (WilsonThermometerReflectedRoster.density R (fun _:I=>d) (fun _=>0) turn c data
          (fun _=>u) names deep.le hj A).part s =
        ((C₀).path.rep N p j).eval A • actualTransport C₀ (N:=N)
          (fun U=>∏ i∈s.val, ((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p
            (WilsonReflectedPublicOrientedFaces.displayed R d (x i) (turn i))
            (((C₀).S.toDepth deep.le p).embed (c i)) U) hj A := by
  obtain ⟨t,grade,market⟩:=WilsonReflectedPublicOpticalJoint.original F simple bliss slow shop D d T cap
  obtain ⟨base,invoice⟩:=eventually_atTop.mp (WilsonReflectedPublicMountedInvoice.original R simple shop d)
  refine ⟨t,grade,?_⟩
  filter_upwards [market,WilsonReflectedPublicStationLate.original F simple bliss T base] with r bought reach
  intro k stock W fits U P cleared exactR m f p N deep
  have one:=reach P cleared exactR false
  have datePaid:base ≤ m:=one.trans (show station F P false ≤ m by simp [station,m])
  have ready:base≤f:=datePaid.trans (WilsonInvariantActionPosition.arrival R 5 m).1.le
  obtain ⟨V,u,est,enrolled,all⟩:=bought P cleared exactR p N deep
  exact ⟨V,u,est,enrolled,fun b v s c=>invoice f ready deep.le est enrolled ((P.arm b v).source (N,p)) s c,all⟩

end YM.Integration.WilsonReflectedPublicOpticalEstate
end
