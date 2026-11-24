import YM.Integration.WilsonThermometerWeakPositionMoments
import YM.Integration.WilsonAddressedPositionStencils
import YM.Integration.WilsonThermometerWeakWardSourceBall

/-! The corrected position source, its priced upper stencils, and every
occupied Ward-erased moment against the cleared exterior of the same Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMeasuredExterior
open PhysicalNext.RankCovariance MergeProof.East Trace.Over
open scoped Topology Classical

open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Ship Next.Rank.Station Next.Rank.Spindle
open Function Filter Set Metric Source RG12 Extra.Histories RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Tapes.West Configuration Normal Rise
open Paint Thirst Relation Perch Glimmer LiftMark Beamer Station Atlas Tariffs Ribbon
open Edition Peak Value Marker Corona Alarm Next.Rank.Glyph
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonAddressedWeakCalibration WilsonAddressedWeakReflectedHearing WilsonThermometerReflectedTrajectory
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone PhysMS
open Trace Trace.Pilot WilsonAddressedWeakCorrectedCylinder WilsonAddressedWeakPointCells WilsonAddressedWeakMaxwellPositions
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG RG12 Labels Extra.Histories RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext.Repeat.Legato MergeProof Accent Trace.Physical Trace.Physical.GermGraph Work.G08 Next.Rank
open RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerReading
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource WilsonPositionCorrectedCap
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open scoped BigOperators Classical Topology
open Next.Extract Push PhysicalNext.RankCovariance Pert Pert.Position MS.Land MS.Menus
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local WilsonAddressedReportedColumns
open WilsonPositionThermometerStationNorm
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {T:Table R.family.book}
variable {D:Local.Physical.Deck G} {O:Booked D} (M:MS_Data G O)
variable (V₀:∀d,Source.SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    {P₀:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ]R.family.label d)} (b:Presentation R.family)
    (house:Hearthside R.family V₀ W P₀ b (PhysicalNext.Repeat.Legato.Bandage.fly R.alloy.B.a))
variable (F:Final R.family f T) (P:ℝ→tower T) (V:Store G) {H:(Bel R.family.book).Hierarchy}
    {l:Ultrafilter (ℕ×ℕ)} {cap:ℕ} (A:ℝ→WilsonPositionThermometerCapStation.Group R.family cap)
local notation "C" => R.family
local notation "Lev" => R.family.path.levels
local notation "cash" => WilsonThermometerOffsetLedger.cash R



variable (portfolio:∀d,Mark.Portfolio R.family.params (V₀ d) (W d))

open WilsonOffsetReportingProducts
open WilsonThermometerReflectedWatch (exterior)
open WilsonCapturedPrimaryWardRetimed (reading)
open WilsonThermometerMarchTerminalWatch (upper)
open MeasureTheory Labels XSpace XSpace.Rose WilsonOffsetEquationLaw OPE.Orbits


def word {J:Type} [Fintype J] (e:J→ℕ) (N p:ℕ) (o:J→Site ((C).side N p))
    (a:∀i,(C).label (e i)) (g:Config G ((C).side N p)):ℂ:=∏i,(C).O N p (a i) (o i) g

def rate (e k:ℕ) (A:ℝ):ℝ:=A*(C).S.a k^(-(e:ℝ)-1)+1

def posted (e k N p:ℕ)(active:k≤N)(A:ℝ):Prop:=
  ∀(j:ℕ)(early:j≤k)(q:Site ((C).side j p))(o:Site ((C).side N p))(v:(C).label e),
    let T:=center (C).S p (early.trans active) 0
    o ∈ T.margin q (3*span (C).S active p) →
    ∃Y, Interior (T.chamber 0) Y ∧ T.rootTest ((C).beta N p) Y ≤ rate (R:=R) e k A*(1+‖v‖) ∧
      T.copy q Y=(C).O N p v o

theorem purchase (room:CellHyp (C) f) {J:Type} [Fintype J] (e:J→ℕ):
    ∃(floor:J→ℕ)(A:J→ℝ),(∀i,0≤A i) ∧ ∀k:J→ℕ,(∀i,floor i≤k i) →
    ∀ᶠ n:ℕ×ℕ in f.fuse,∃h:∀i,k i≤n.1,∀i,posted (R:=R) (e i) (k i) n.1 n.2 (h i) (A i):=by
  classical
  choose floor A pos sale using fun i:J=>WilsonThermometerExtractedColumns.original R.makes room (e i)
  refine ⟨floor,A,pos,fun k atFloor=>?_⟩
  filter_upwards [eventually_all.mpr (fun i=>sale i (k i) (atFloor i))] with n present
  choose h paid using present
  exact ⟨h,paid⟩

theorem continuous_word {J:Type} [Fintype J] (e:J→ℕ)(N p:ℕ)
    (o:J→Site ((C).side N p))(a:∀i,(C).label (e i)):
    Continuous (word (R:=R) e N p o a):=
  continuous_finsetProd _ (fun i _=>(C).continuousO N p (e i) (a i) (o i))

theorem local_word {J:Type} [Fintype J] (e:J→ℕ)(N p:ℕ)
    (o:J→Site ((C).side N p))(a:∀i,(C).label (e i)) (K:Set (Site ((C).side N p)))
    (kept:∀i,(↑(((C).localSection (e i)).footprint (o i)):Set (Site ((C).side N p)))⊆K):
    LocalOn K (word (R:=R) e N p o a):=by
  intro U V eq
  exact Finset.prod_congr rfl fun i _=>(C).localO N p (e i) (a i) (o i) U V (agrees_mono eq (kept i))

theorem stationary {I J:Type} [Fintype I] [Fintype J] (d:I→Fin (cap+1))
    (w:∀i,(Bel (C).book).Field (d i))(Z:WilsonPositionThermometerCapStation.Group (C) cap)
    {N m p:ℕ}(active:m≤N)(z:I→Site ((C).side N p))(r:∀i,Emblems (C) (d i))(y:∀i,Palette (C) (d i))
    (rad:ℕ→ℕ)(δ:ℝ)(nn:0≤δ)(source:WilsonThermometerWeakPositionMoments.expense V₀ d w Z (p:=p) active z r y rad δ)
    (e:J→ℕ)(k:J→ℕ)(fund:∀i,k i≤N)(A:J→ℝ)
    (owns:∀i,posted (R:=R) (e i) (k i) N p (fund i) (A i))
    (s:Finset I)(apart:Avoids («C» := R.family) V₀ rad (fun i:s=>(d i).val) (fun i=>z i))
    (j:ℕ)(early:j ≤ m)(visit:∀i,j≤k i)(v:s→Site ((C).side j p))(q:J→Site ((C).side j p))
    (o:J→Site ((C).side N p))(a:∀i,(C).label (e i)) :
    let T:=center (C).S p (early.trans active) 0
    (∀i:s,z i∈T.margin (v i) (3*span (C).S active p)) →
    (∀i:J,o i∈T.margin (q i) (3*span (C).S (fund i) p)) →
    Injective (Sum.elim v q) →
    (∀(i:s)(t:J),(↑(((C).localSection (e t)).footprint (o t)):Set (Site ((C).side N p)))
      ⊆Mark.Outer (rad (d i)) (z i)) →
    let ext:=word (R:=R) e N p o a
    ‖moment ((C).beta N p) (fun g=>(∏i:s,(C).O N p (reading (p:=p) (r i) active (y i)) (z i) g)*ext g)-
      moment ((C).beta N p) (fun g=>(∏i:s,(C).O N p
        (Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))) (z i) g)*ext g)‖ ≤
      δ*((∏i,rate (R:=R) (e i) (k i) (A i))*(∏i,(1+‖a i‖))):=by
  classical
  intro T inside outside distinct clear ext
  choose W entered bill placed using fun i:J=>owns i j (visit i) (q i) (o i) (a i) (outside i)
  have equal:exterior T q W=ext:=by
    funext g
    exact Finset.prod_congr rfl fun i _=>congrFun (placed i) g
  have raw:=source s apart j early v inside J q W distinct entered
  rw [equal] at raw
  have paid:=raw (fun i=>local_word e N p o a _ (clear i)) (Mark.cont_envelope (continuous_word e N p o a))
  apply paid.trans (mul_le_mul_of_nonneg_left ?_ nn)
  rw [←Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun i _=>T.root_nonneg _ _) (fun i _=>bill i)

end YM.Integration.WilsonThermometerWeakMeasuredExterior
end
