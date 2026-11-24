import YM.Integration.WilsonMeasuredPublicEntranceFullCampus
import YM.Integration.WilsonMovingForkDatedInvoice
import YM.Integration.WilsonSeparatedPrefixPanelWord

/-! The appointed original upper hearing on the named dated moving-fork file, with its N-law at K. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalMovingForkUpper
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

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem original {D T t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    {books:(r:{r:ℝ //0<r ∧ r<δ})→Book F (l:=l) H z D T r.val}
    {field:(i:I)→{r:ℝ //0<r ∧ r<δ}→Bool→Bool→S.Field (d i).val}
    {M:I→ℝ}{E e:I→ℕ}{tuition:ℝ}{power target f K:ℕ}{ρ:I→{r:ℝ //0<r ∧ r<δ}}
    (school:School F D T t d e books field M E tuition power target ρ f K)
    (one:∀i,1≤M i){n:ℕ}(select:Fin n→I)(mode branch:Fin n→Bool)
    (file:Filed R (fun i=>(d (select i)).val) K)
    (slots:file.station=fun i=>station F ((books (ρ (select i))).rows (d (select i))) (branch i))
    {N per apron m first requested reserve j u v c:ℕ}(top:K<N)
    (read:ReadAt R (fun i=>(d (select i)).val) m N per apron requested t reserve power (capital R D tuition) first)
    (ready:first≤j)(base:m≤j)(height:j+2≤f)(depth:K=berth R reserve f)
    (old:∀i,first≤file.station i)(mu:m≤u)(uj:u≤j)(ou:Opened C 0 u per)(oj:Opened C 0 j per)
    (offered:Fin n→ Lattice.Cover)
    (clear:((Fin n)→False) ∨ Ground R N per j f apron (snap C f per offered))
    (apart:∀i k:Fin n,i≠k→((P).budget f).B^2<separation (snap C f per offered i) (snap C f per offered k))
    (allowed:∀i,accuracy (fun a=>(d (select a)).val) requested i≤e (select i))
    (desired:ℕ)(expo:desired+∑i,E (select i)≤requested)
    (uv:u≤v)(vc:v≤c)(ck:c≤K):
    let arms:=fun i=>((books (ρ (select i))).rows (d (select i))).arm (branch i)
      (field (select i) (ρ (select i)) (mode i) (branch i))
    ∀fk:f≤K,Upper file arms fk uv vc ck offered (N,per) top
      ((∏i,WilsonAddressedHomeDose.ceiling (R:=R) (d (select i)).val (M (select i)))*((β f)^desired)⁻¹):=by
  classical
  intro arms fk
  obtain ⟨up,electrode,_,camp⟩:=school
  obtain ⟨V,w,home,enrolled,admit⟩:=camp N per top.le
  let g:=fun i=>(d (select i)).val
  let el:=fun p i=>electrode p (select i) (branch i)
  obtain ⟨A,dates,axes,rows,tariffs,_,_,still,pins,_,_,_,refs,fares⟩:=
    admit n select mode branch file slots requested allowed (fun _=>(1,false)) (snap C f per offered) apart
  have matchAxes:A.axis=file.A N per:=axes.trans (WilsonMeasuredPublicEntranceCutoffFile.live R g file el top per).1
  have pay:=WilsonSeparatedPrefixPanelWord.original R g A offered file (fun i=>(arms i).source (N,per))
    rows pins still read ready base height depth old clear mu uj ou oj dates matchAxes
    (fun i=>tariffs ▸ one (select i)) (fun i=>E (select i)) refs fares desired expo
  simpa only [WilsonMovingForkFiniteCell.Upper,tariffs,Function.comp_apply] using pay

end YM.Integration.WilsonPhysicalMovingForkUpper
end
