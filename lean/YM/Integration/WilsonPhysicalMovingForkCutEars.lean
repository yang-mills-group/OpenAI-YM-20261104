import YM.Integration.WilsonPhysicalMovingForkUpper
import YM.Integration.WilsonSeparatedPrefixGridGround
import YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerFinance
/-! Original optical purchase of the finite K entrance for arbitrary separated physical vertex rows. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalMovingForkCutEars
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)

open WilsonMeasuredPublicEntrancePanel (accuracy)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonReflectedPublicStationFare (station)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntranceScreen (Ground)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkFiniteCell (Upper)
open WilsonMeasuredPublicEntranceCutoffFile (complete)
open WilsonMeasuredPublicEntranceFullCampus (School)
open WilsonThermometerUnitFilingFourSquare (Arm)


universe u
open WilsonLimitConstruction PhysMS
open WilsonMovingForkOpticalBook (reporter)
open WilsonMeasuredPublicEntranceMasterUpper (threshold)
omit [DecidableEq I] in
theorem original {simple:G.Simple}{axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}
    {campaign:Campaign R}{W:Campaign.Pillars R campaign}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R campaign W)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (P))
    (lamp:WilsonReportLampForecast.Ready (P))
    (bliss:Bliss F l z H)(D T b t:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(r:{r:ℝ //0<r ∧ r<δ})→Book F (l:=l) H z D T r.val)
    (field:(i:I)→{r:ℝ //0<r ∧ r<δ}→Bool→Bool→S.Field (d i).val)
    {n:ℕ}(np:0<n)(select:Fin n→I)(mode branch:Fin n→Bool)
    (M:I→ℝ)(E e:I→ℕ)(one:∀i,1≤M i)(tuition:ℝ)(reserve power target desired requested:ℕ)
    (allowed:∀i,accuracy (fun a=>(d (select a)).val) requested i≤e (select i))
    (expo:desired+∑i,E (select i)≤requested)
    {width sep:ℝ}(home:0<width)(away:0<sep):
    ∀ᶠ m:ℕ in atTop,∀u:ℕ,m≤u→∀ᶠr in trail,
      ∀ρ:I→{r:ℝ //0<r ∧ r<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z b r) → (∃i,(ρ i).val=r) →
      let f:=reporter F books ρ
      let K:=berth R reserve f
      ∃j:ℕ,u≤j ∧ j+2≤f ∧
      ∀(_school:School F D T t d e books field M E tuition power target ρ f K),
      ∀(file:Filed R (fun i=>(d (select i)).val) K),
      file.station=(fun i=>station F ((books (ρ (select i))).rows (d (select i))) (branch i)) →
      ∀N per (top:K<N)(site:Fin n→ Lattice.Cover),
      (∀i,‖(C).S.gridPoint f (site i)‖≤width*outer z b r) →
      (Pairwise fun i k=>sep*r≤‖(C).S.gridPoint f (site i)-(C).S.gridPoint f (site k)‖) →
      let arms:=fun i=>((books (ρ (select i))).rows (d (select i))).arm (branch i)
        (field (select i) (ρ (select i)) (mode i) (branch i))
      ∀v c:ℕ,∀(fk:f≤K)(uv:u≤v)(vc:v≤c)(ck:c≤K),
      WilsonMovingForkFiniteCell.Upper file arms fk uv vc ck site (N,per) top
        ((∏i,WilsonAddressedHomeDose.ceiling (R:=R) (d (select i)).val (M (select i)))*((β f)^desired)⁻¹):=by
  classical
  letI:Nonempty (Fin n):=⟨⟨0,np⟩⟩
  have costs:=WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid
  obtain ⟨room,faculty⟩:=WilsonMeasuredPublicEntranceMasterUpper.original R simple costs.2.1 costs.2.2.2
    costs.2.2.1 bank lamp costs.1 paid
  obtain ⟨apron,housing⟩:=WilsonSeparatedPrefixGridGround.original F simple bliss costs.2.1 D T b d books home away
  let g:=fun i:Fin n=>(d (select i)).val
  have size:Fintype.card (Fin n)≤n:=by simp
  let first:=threshold R simple costs.2.1 costs.2.2.2 costs.2.2.1 bank lamp costs.1
    g n apron requested t reserve power (capital R D tuition) np size
  have pos:0≤capital R D tuition:=by
    unfold capital
    positivity
  obtain ⟨ear,openEar⟩:=eventually_atTop.mp (open_late R.family simple 0)
  filter_upwards [faculty n D requested,eventually_ge_atTop ear] with m sale start
  intro u mu
  let floor:=max u first
  have stations:=WilsonAddressedMixedStationRange.original F simple bliss costs.2.1 D T b floor d books
  filter_upwards [housing floor,stations] with r funded windows
  intro ρ span near f K
  obtain ⟨j,after,extent,covered⟩:=funded ρ span near
  have uj:u≤j:=(le_max_left ..).trans after
  have fj:first≤j:=(le_max_right ..).trans after
  refine ⟨j,uj,extent,?_⟩
  intro school file locked N per top site bounded apart arms v c fk uv vc ck
  have fine:f≤N:=fk.trans top.le
  obtain ⟨stamp,_,_,read⟩:=sale N (mu.trans (uj.trans (by omega)))
  have bill:=read (Fin n) g np size (fun i=>Nat.le_of_lt_succ (d (select i)).isLt) apron requested t reserve power
    (capital R D tuition) pos per
  have ground:Ground R N per j f apron (snap C f per site):=(covered (Fin n) N per fine site bounded apart).1
  have quiet:=ground.2.1
  have rep:((C).path.rep N per f).p=(P).budget f:=(R.makes.wilson.represents N per f fine).vac
  rw [rep] at quiet
  have firstAt(i:Fin n):first≤file.station i:=by
    rw [locked]
    exact (le_max_right ..).trans ((windows ρ span near).2 (select i) (branch i)).1
  exact WilsonPhysicalMovingForkUpper.original F school one select mode branch file locked top bill fj
    (mu.trans uj) extent rfl firstAt mu uj (openEar u (start.trans mu) per)
    (openEar j (start.trans (mu.trans uj)) per) site (Or.inr ground) quiet allowed desired expo uv vc ck fk

end YM.Integration.WilsonPhysicalMovingForkCutEars
end
