import YM.Integration.WilsonMeasuredSignedActionReleased
/-! The original named Wilson stock through a further paid stress position. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionPosed
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
  {z:Trace.Terrace.Arch R.family}{lo wid teach}(L:Package R.family wid lo teach)
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family

open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourWeakWall (Purchased)
open WilsonPositionProgramPublicStations (Pair)
open WilsonThermometerUnitFilingFourSquare (Arm)


open WilsonMeasuredSignedActionOwnedRows (Rows)
open WilsonMeasuredPublicEntranceNativeFrame (atRadius)
open PhysMS


open WilsonMeasuredPublicEntranceNativeStaff (Receipt)
open WilsonMeasuredSignedActionOwnedBook (sub)
open Trace.Terrace Trace.Pilot PhysMS

open WilsonMeasuredSignedActionOwnedIncome (Issued)
open PhysMS.Frame

theorem current (J:ℝ→tower S){P':ℝ→Spin.change S 4}{d:ℝ→ℝ}
    (same:∀ᶠr in trail,J r 4=P' r)(trained:TendC F P' d):
    TendC F (fun r=>J r 4) d:=by
  refine ⟨trained.measures,?_,?_⟩
  · obtain ⟨c,paid⟩:=trained.centered
    refine ⟨c,?_⟩
    filter_upwards [same,paid] with r h hr
    simpa only [h] using hr
  · filter_upwards [same,trained.tensor] with r h hr
    simpa only [h] using hr

theorem original {δ:ℝ}(cap:Set.Ioc (0:ℝ) δ→ℕ)(W:∀s,Vane C (cap s))
    (prior J Q:ℝ→tower S)(stock:Issued F (H:=H) (l:=l) (z:=z) cap W prior J)
    {P P':ℝ→Spin.change S 4}{a d e:ℝ→ℝ}
    (same:∀ᶠr in trail,Q r 4=P' r)(paid:Target.FieldComparison F H z P P' a d e):
    Issued F (H:=H) (l:=l) (z:=z) cap W prior Q:=
  ⟨⟨d,current F Q same paid.leading⟩,paid.wilson,stock.2.2⟩

theorem capacity {δ:ℝ}(cap:Set.Ioc (0:ℝ) δ→ℕ)(W:∀s,Vane C (cap s))
    (prior J Q:ℝ→tower S)(old:localCost trail (atRadius l cap W prior) J)
    (posed:localCost trail J Q):
    localCost trail (atRadius l cap W prior) Q ∧ ∀d,∀v:(Bel (C).book).Field d,
      ∀ᶠ r in trail,‖(atRadius l cap W prior r d).symm (Q r d v)‖≤‖v‖+1:=by
  have near:=localCost_trans old posed
  refine ⟨near,fun d v=>?_⟩
  exact ((near d v).norm.eventually_lt_const (lt_add_one _)).mono fun _ h=>h.le

def move (J Q:tower S)(d:ℕ):(Bel (C).book).Field d≃ₗ[ℂ](Bel (C).book).Field d:=(Q d).trans (J d).symm

theorem restored (J Q:tower S)(d:ℕ)(v:(Bel (C).book).Field d):
    J d (move J Q d v)=Q d v:=by simp [move]

theorem measured (J Q:tower S)(p:Viewers F){n:ℕ}{d:Caps n}(v:MaxwellSlots C d)(r:ℝ)(x:Points n):
    PhysMS.measured F p Q v r x=PhysMS.measured F p J (fun i=>move J Q (d i) (v i)) r x:=by
  simp only [PhysMS.measured,restored]

theorem source {D T:ℕ}{r:ℝ}(B:Book F (l:=l) H z D T r)(i:Fin (D+1))(branch:Bool)
    (J Q:tower S)(v:(Bel (C).book).Field i)(cutoff:ℕ×ℕ):
    ((B.rows i).arm branch (Q i v)).source cutoff=
      ((B.rows i).arm branch (J i (move J Q i v))).source cutoff:=by
  rw [restored]

end YM.Integration.WilsonMeasuredSignedActionPosed
end
