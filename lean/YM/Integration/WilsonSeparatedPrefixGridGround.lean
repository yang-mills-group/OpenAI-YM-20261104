import YM.Integration.WilsonSeparatedPrefixScreenedPhysical
import YM.Integration.WilsonSeparatedPrefixPanelReturn
import YM.Integration.WilsonSeparatedPrefixHeldPanelReturn

/-! The actual screened physical positions on a single reporting mesh satisfy both original entrance hearings. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixGridGround
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
open PhysMS
open MS MS.Land FVA2 FVA2.Register


open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory WilsonMeasuredPublicEntranceHeadBoard
open WilsonAddressedAlignedColumn WilsonReflectedPublicStationFare
open WilsonThermometerOffsetCylinder WilsonThermometerOffsetTrajectory

open WilsonThermometerUnitFilingCoarse WilsonSeparatedPrefixCanonicalClearConvolution
open Lodestar
variable {E:Type}[Fintype E][DecidableEq E][Nonempty E]
open WilsonSeparatedPrefixMovingHomeEars (returned)
local notation "J₀" => Marks E
local notation "X" => Unit×(E×Bool)


open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonMeasuredPublicEntranceScreen (Ground)
open WilsonOriginalNullOriginGridRoster (ancestry)
open WilsonMovingForkOpticalBook (reporter)

omit [Fintype E] [DecidableEq E] [Nonempty E] in
theorem branch {f per:ℕ}(o:E→Site ((C).side f per)):
    let path:=fun k (x:X)=>ancestry R per f (o x.2.1) k
    path f=(o∘Prod.fst)∘Prod.snd ∧
    ∀v,v<f → path v=((P).clock.op v per).ratio.parent ∘ path (v+1):=by
  intro path
  exact ⟨funext (fun x=>WilsonOriginalNullOriginGridRoster.starts R per f (o x.2.1)),
    fun v vf=>funext (fun x=>(WilsonOriginalNullOriginGridRoster.route R per f (o x.2.1) vf).symm)⟩

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    {L η:ℝ}(lp:0<L)(ep:0<η):
    ∃apron:ℕ,∀floor:ℕ,∀ᶠr in trail,∀ρ:I→{s:ℝ //0<s ∧ s<δ},
    (∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) → (∃i,(ρ i).val=r) →
    let f:=reporter F books ρ
    ∃j:ℕ,floor≤j ∧ j+2≤f ∧
    ∀(V:Type)[Fintype V][DecidableEq V][Nonempty V](N per:ℕ),f≤N →
    ∀site:V→Lattice.Cover,(∀i,‖(C).S.gridPoint f (site i)‖≤L*outer z h r) →
    (Pairwise fun i k=>η*r≤‖(C).S.gridPoint f (site i)-(C).S.gridPoint f (site k)‖) →
    let o:=snap (C) f per site
    let path:=fun k (x:Unit×(V×Bool))=>ancestry R per f (o x.2.1) k
    Ground R N per j f apron o ∧
    (path f=(o∘Prod.fst)∘Prod.snd ∧ ∀v,v<f → path v=((P).clock.op v per).ratio.parent ∘ path (v+1)):=by
  classical
  obtain ⟨apron,housing⟩:=WilsonSeparatedPrefixCellHousing.original F simple bliss slow D T h 0 d books L lp
  have clearance:=WilsonMovingForkClearance.original (I:=I) F simple bliss slow D T h books lp ep
  obtain ⟨walls,wide⟩:=eventually_atTop.mp ((hat_rate (P) simple).eventually_ge_atTop (Real.exp 3))
  refine ⟨apron,?_⟩
  intro floor
  filter_upwards [housing (max floor walls),clearance] with r captured separated ρ band hit f
  obtain ⟨j,before,extent,span,home⟩:=captured ρ band hit
  change j+2≤f at extent
  have wall:Real.exp 3≤β f:=wide f (by omega)
  have heat:0<β f:=(Real.exp_pos 3).trans_le wall
  have ink:5≤((P).budget f).B:=by
    have sq:(Real.log (β f))^2≤(((P).budget f).B:ℝ):=Nat.le_ceil _
    have log3:3≤Real.log (β f):=(Real.le_log_iff_exp_le heat).mpr wall
    exact_mod_cast (show (5:ℝ)≤(((P).budget f).B:ℝ) by nlinarith)
  refine ⟨j,(le_max_left ..).trans before,extent,?_⟩
  intro V _ _ _ N per live site reach apart o path
  have rep:((C).path.rep N per f).p=(P).budget f:=(R.makes.wilson.represents N per f live).vac
  have routes:=branch (R:=R) o
  refine ⟨⟨rep ▸ ink,?_,span,?_⟩,routes⟩
  · intro i k ne
    rw [rep]
    have fee:=separated ρ band hit (N:=N) (p:=per) live site reach apart i k ne
    change ((P).budget f).B^2 < separation
      (WilsonThermometerReflectedTrajectory.point R (N:=N) 0 (1,false) (o i) f)
      (WilsonThermometerReflectedTrajectory.point R (N:=N) 0 (1,false) (o k) f) at fee
    rwa [WilsonAddressedPublicGridRooms.position R live,WilsonAddressedPublicGridRooms.position R live] at fee
  · let anchor:Unit×(V×Bool):=((),Classical.arbitrary V,false)
    have room:8*(L*outer z h r)≤(C).S.a (j+1):=by simpa using home
    have deposit:=WilsonSeparatedPrefixScreenedParents.original R (p:=per) extent site _ reach room
    have pinned (v:Unit×(V×Bool)):path (j+1) v=0:=deposit v.2.1
    refine ⟨path,anchor,routes.1,fun v _ vf=>routes.2 v vf,?_,?_⟩
    · intro v
      simpa [pinned] using WilsonThermometerUnchangedGrouping.alone
        ((C).path.rep N per (j+1)).p.B (0:Site ((C).side (j+1) per))
    · rw [pinned]
      let g:=((P).clock.op j per).ratio
      change g.parent 0=0
      rw [←g.root.map_zero]
      exact g.embed_parent _

end YM.Integration.WilsonSeparatedPrefixGridGround
end
