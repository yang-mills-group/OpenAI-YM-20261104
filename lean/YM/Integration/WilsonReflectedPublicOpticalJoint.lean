import YM.Integration.WilsonReflectedPublicCensusFare
import YM.Integration.WilsonReflectedPublicOrientedCarton
import YM.Integration.WilsonAddressedPublicGridRooms
/-! A true finite public portfolio on the single common optical grid fixed
by the appointed weak and pooled stations. The original normalization is
paid before the UV and the period, including its action on every proper face. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicOpticalJoint
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

theorem location (R:Run G) {N f p:ℕ} (hf:f ≤ N) (s:Motion) (c:Site (R.family.side f p)):
    WilsonThermometerReflectedTrajectory.point R (N:=N) 0 s c f=c := by
  let Q:Ratio (R.family.side f p) (R.family.side N p):=R.family.S.toDepth hf p
  have zero:Q.parent 0=0 := by rw [←Q.root.map_zero];exact Q.embed_parent _
  have base:anchorAt R c f=c:=Extra.Histories.Tour.begin_anchor R.family p f c
  simp only [WilsonThermometerReflectedTrajectory.point,WilsonThermometerOwnOffsetNectar.location,WilsonThermometerOwnOffsetTale.site,dif_pos hf,base]
  change affine s.1 c (Q.parent 0) = c
  rw [zero]
  simp [affine]

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
  classical
  obtain ⟨t,tmin,market⟩:=WilsonReflectedPublicChargedRoster.original R simple shop D
  obtain ⟨f₀,early⟩:=eventually_atTop.mp market
  obtain ⟨f₁,range⟩:=eventually_atTop.mp ((WilsonAddressedCollarWindow.original R simple slow 5 zero_lt_one).and
    ((hat_rate (lev) simple).eventually_ge_atTop 1))
  have late:=WilsonReflectedPublicStationLate.original F simple bliss T (max f₀ f₁)
  refine ⟨t,tmin,?_⟩
  filter_upwards [late,WilsonReflectedPublicStationSpan.original F simple bliss T] with r enrolled spend
  intro k stock W fits U P cleared exactR m f
  have reached := enrolled P cleared exactR
  have attained (b:Bool) : station F P b ≤ m := by cases b <;> simp [station,m]
  have large : max f₀ f₁ ≤ m := (reached false).trans (attained false)
  have rangeM := range m ((le_max_right ..).trans large)
  have mf:m<f:=rangeM.1.1
  have start (b):= (attained b).trans mf.le
  have ratio (b : Bool) : mesh (station F P b)/mesh f ≤ (β f)^(2*T+9) := by
    have own := spend P cleared exactR b
    have edge : mesh m / mesh f ≤ (β m)^6 := by
      simpa [Real.rpow_one,show (6:ℕ)=5+1 by decide,pow_succ] using rangeM.1.2.2
    have positive := (R.family.S.a_pos m).ne'
    calc
      _ = (mesh (station F P b)/mesh m)*(mesh m/mesh f) := by field_simp
      _ ≤ (β m)^(2*T+3)*(β m)^6 := mul_le_mul own edge (div_nonneg (R.family.S.a_pos _).le
        (R.family.S.a_pos _).le) (pow_nonneg (zero_le_one.trans rangeM.2) _)
      _ = (β m)^(2*T+9) := by rw [←pow_add]
      _ ≤ _ := pow_le_pow_left₀ (zero_le_one.trans rangeM.2)
        (WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos simple).le mf.le) _
  intro p N deep
  obtain ⟨V,u,est,issued,board⟩:=early f (((le_max_left ..).trans large).trans mf.le) p N deep
  let a:Fin (D+1):=⟨d,Nat.lt_succ_of_le cap⟩
  refine ⟨V a,u a,est a,issued a,?_⟩
  intro I fi di weak v turn c names apart x y data
  have sites (i j:I)(dist:i≠j): ((lev).budget f).B^2 <
      separation (WilsonThermometerReflectedTrajectory.point R (N:=N) 0 (turn i) (c i) f) (WilsonThermometerReflectedTrajectory.point R (N:=N) 0 (turn j) (c j) f) := by
    simpa only [location R deep.le] using apart i j dist
  obtain ⟨cash,filed,faces⟩:=board I (fun _=>a) x turn c names sites
  refine ⟨?_,filed,?_⟩
  · intro i
    have paid:=WilsonReflectedPublicCensusFare.original F P cleared (weak i) (v i) (start _) (p:=p) deep
    have fee₀:= (WilsonReflectedPublicStationFare.original F P cleared (weak i) (v i)).2 N p
      ((start _).trans_lt deep)
    have nn: 0 ≤ Next.UVStress.quota C₀ d (station F P (weak i)) N p (x i):=by
      unfold Next.UVStress.quota Labels.Frame.coeffSize;positivity
    have pos:=nonneg_of_mul_nonneg_right (nn.trans fee₀) (pow_pos (R.family.S.a_pos _) d)
    apply (cash i).trans (paid.trans (max_le_max_left _ ?_))
    apply mul_le_mul_of_nonneg_right _ pos
    rw [pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (div_nonneg (R.family.S.a_pos _).le (R.family.S.a_pos _).le) (ratio (weak i)) (d+1)) zero_le_two
  · intro j hj s A
    simpa only [WilsonAddressedPublicGridRooms.top R deep.le] using faces j hj s A

end YM.Integration.WilsonReflectedPublicOpticalJoint
end
