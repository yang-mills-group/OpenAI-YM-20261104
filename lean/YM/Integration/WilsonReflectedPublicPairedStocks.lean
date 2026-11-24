import YM.Integration.WilsonReflectedPublicGuardedColumns
/-! On the two original public stocks, jointly choosing the entire paid physical
occupation history and the signed fixed-K all-fields source before either regulator. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicPairedStocks
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
def Inventory {N p f d:ℕ} {X:Type} (t T:ℕ)
    (book:Bool→X→(C₀).label d)(fee₁:Bool→X→ℝ)
    (V:Sight C₀ d p)(u:Emblems C₀ d)(est:Opened C₀ d f p)(top:f≤N):Prop :=
      (∀ (weak:Bool) (v:X) (s:Motion) (c:Site (R.family.side f p)),
        let rep:=(C₀).path.rep N p f
        let data:=reduce (offer R (book weak v) est top)
        let field:=marked R (N:=N) 0 s c V u data f
        let fee₀:=WilsonReflectedPublicMountedInvoice.wage R f
        ∃q:Coefficient ((C₀).labels.level d) ((C₀).side f p),
          q.Format c (C₀).params rep ∧
          ((C₀).labels.level d).coeffSize q.x≤orbitCost ((C₀).labels.level d)*(1+fee₀) ∧
          q.remBound c rep (kappa (C₀).path f) fee₀ ∧
          field.2.1=q.exponentialEntry c ((C₀).localSection d) rep ∧
          profile rep.activities field.2.2=profile rep.activities q.forced ∧
          q.density c ((C₀).localSection d) rep=field.1) ∧
      ∀(I:Type) [Fintype I] [DecidableEq I] (weak:I→Bool) (v:I→X) (turn:I→Motion)
        (c:I→Site (R.family.side f p)) (names:Census I),
      (∀i j:I,i≠j → ((lev).budget f).B^2 < separation (c i) (c j)) →
      let x:=fun i=>book (weak i) (v i)
      let y:=fun i=>offer R (x i) est top
      let data:=fun i=>reduce (y i)
      (∀i,charge (y i) ≤ max 1 (2*(β f)^((2*T+9)*(d+1))*fee₁ (weak i) (v i))) ∧
      WilsonThermometerReflectedRoster.filed R (fun _:I=>d) (fun _=>0) turn c data (fun _=>V) (fun _=>u)
        names top t ∧
      ∀j (hj:j ≤ N) (s:names.Mode) A,
        (WilsonThermometerReflectedRoster.density R (fun _:I=>d) (fun _=>0) turn c data
          (fun _=>u) names top hj A).part s =
        ((C₀).path.rep N p j).eval A • actualTransport C₀ (N:=N)
          (fun U=>∏ i∈s.val, ((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p
            (WilsonReflectedPublicOrientedFaces.displayed R d (x i) (turn i))
            (((C₀).S.toDepth top p).embed (c i)) U) hj A

def Stock {N p f K d:ℕ} {X:Type} (q jets:ℕ)(C:ℝ)
    (book:Bool→X→(C₀).label d)(fee₁:Bool→X→ℝ)(date:Bool→ℕ)
    (M:Bool→(C₀).label d ≃ₗ[ℂ] (C₀).label d)
    (h:f<K)(start:∀b,date b≤f)(top:K≤N):Prop :=
  ∀ b (v : X),
      let Y := book b v
      let j := date b
      let w := (M b).symm (WilsonOriginalMicroscopicGuardedPage.full R d N p j Y)
      receipt R d j K N p jets ((start b).trans h.le) top (1/32) (M b) Y (mesh j^d*fee₁ b v) ∧
      ∀ side s o, ∃ A : Arm R d N p f K, A.Y = Y ∧ A.w = w ∧ A.b = side ∧ A.s = s ∧ A.o = o ∧
        Priced R A (C*((β f)^(q+1))⁻¹*(mesh f)^d*fee₁ b v) ∧
        (∃ B : Arm R d N p K K, WilsonReflectedRestoredStation.Situated R h.le A B) ∧
        ∀ factor:ℂ, ‖factor‖≤1 → ∃E, WilsonReflectedPublicSignedFare.Restored R A h.le top factor
          ((2+Extra.Histories.Motion.orbitCost ((C₀).labels.level d))*C*((β f)^q)⁻¹*fee₁ b v) E

theorem original (simple:G.Simple) (bliss:Bliss F l z H) (slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (width:∀i,1≤((lev).budget i).supportExponent)(capWidth:∀i,((lev).budget i).supportExponent≤100)
    (law:OPE.Therm.Poetry lev) (D d T q jets:ℕ) (cap:d≤D):
    ∃t≥D+3, ∃C:ℝ,0<C ∧ ∀ᶠ r in trail, ∀{k:ℕ}
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
      (Inventory (R:=R) t T (fun b v=>(P.arm b v).source (N,p)) (fee F P) V u est (h.le.trans top) ∧
        Stock (R:=R) (p:=p) q jets C (fun b v=>(P.arm b v).source (N,p)) (fee F P)
          (station F P) M h start top) :=by
  obtain ⟨t,degree,estate⟩:=WilsonReflectedPublicOpticalEstate.original F simple bliss slow shop D d T cap
  obtain ⟨C,cp,joins⟩:=WilsonReflectedPublicOpticalSwaps.original F simple bliss slow shop width capWidth law D d T q jets cap
  refine ⟨t,degree,C,cp,?_⟩
  filter_upwards [estate,joins] with r stored trade k stock W fits U P check exactR m f K
  obtain ⟨h,start,buy⟩:=trade P check exactR
  refine ⟨h,start,?_⟩
  intro N p top
  have deep:f<N:=h.trans_le top
  obtain ⟨V,u,est,enrolled,unary,joint⟩:=stored P check exactR p N deep
  obtain ⟨M,both⟩:=buy N p top
  exact ⟨V,u,est,enrolled,M,⟨unary,joint⟩,both⟩

end YM.Integration.WilsonReflectedPublicPairedStocks
end
