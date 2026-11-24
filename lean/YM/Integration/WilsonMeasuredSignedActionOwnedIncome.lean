import YM.Integration.WilsonMeasuredSignedActionOwnedBook
import YM.Integration.WilsonMeasuredPublicEntranceNativeStaff
import YM.Integration.WilsonMeasuredSignedActionPosition
/-! The physically staffed current and original source on the selected table. -/
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionOwnedIncome
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

def Issued {δ:ℝ}(cap:Set.Ioc (0:ℝ) δ→ℕ)(W:∀s,Vane C (cap s))(prior J:ℝ→tower S):Prop:=
  (∃bias:ℝ→ℝ,TendC F (fun r=>J r 4) bias) ∧ Coupling G (wilson z) ∧ ∀D:ℕ,
    ∃T:ℕ,∃e:ℝ,0<e ∧ ∃incl:e≤δ,∃B:(s:{s:ℝ // 0<s ∧ s<e})→Book F (l:=l) H z D T s.val,
      (∀s,(B s).k=cap (sub incl s) ∧ (B s).W.k=(W (sub incl s)).k ∧ HEq (B s).W (W (sub incl s)) ∧
              ∀i:Fin (D+1),(B s).V i=atRadius l cap W prior s.val i) ∧
      ∀j:ℕ,∀ᶠr in trail,∀p:0<r,∀small:r<e,j≤(B ⟨r,p,small⟩).k ∧ j≤(B ⟨r,p,small⟩).W.k

theorem original (simple:G.Simple)(bliss:Bliss F l z H){δ:ℝ}(positive:0<δ)
    (cap:Set.Ioc (0:ℝ) δ→ℕ)(W:∀s,Vane C (cap s))(prior J:ℝ→tower S)
    (real:∀s,(W s).wheel.r=s.val)(honest:∀s,(W s).checked order H (cap s))
    (calendar:∀s:ℕ→Set.Ioc (0:ℝ) δ,Tendsto (fun n=>(s n).val) atTop (𝓝 0)→
      Tendsto (fun n=>cap (s n)) atTop atTop ∧ Tendsto (fun n=>(W (s n)).k) atTop atTop)
    (staff:∀m:ℕ,∀ᶠr in trail,Receipt (Y:=l) simple F H r (atRadius l cap W prior r) (J r) m):
    Issued F (H:=H) (l:=l) (z:=z) cap W prior J:=by
  have angle:PlotX F H l simple (fun r=>J r 4):=(staff 0).mono fun _ h=>h.1.angle
  exact ⟨margaret F simple bliss _ angle,wilson_link F simple bliss.budgets bliss.keen bliss.lies,
    WilsonMeasuredSignedActionOwnedBook.original F simple bliss positive cap W prior real honest calendar⟩

end YM.Integration.WilsonMeasuredSignedActionOwnedIncome
end
