import YM.Integration.WilsonThermometerWeakMeasuredExterior
import YM.Integration.WilsonAddressedPhysicalCells
import YM.Integration.WilsonPositionPhysicalCellTest
import YM.Integration.WilsonThermometerWeakPositionMoments
import YM.Integration.WilsonAddressedPositionStencils
import YM.Integration.WilsonThermometerWeakWardSourceBall

/-! The corrected position source, its priced upper stencils, and every
occupied Ward-erased moment against the cleared exterior of the same Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakExteriorTest
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



open WilsonThermometerWeakMeasuredExterior (word posted rate)
open WilsonPositionPhysicalCellTest (Sites site mass total_variation)

theorem submitted {n:ℕ} (φ:Test n) (ρ:ℝ)(np:UVIndex)(h:Sites R np n→ℂ):
    (∫x,φ x*h (site ρ np x))=∑c:Sites R np n,mass φ ρ np c*h c:=by
  change (∫x,φ x*h (WilsonAddressedPhysicalCells.atSite ((C).S.a np.1) ρ ((C).side np.1 np.2) x))=_
  rw [WilsonAddressedPhysicalCells.integrate ((C).S.a np.1) ρ ((C).side np.1 np.2) ((C).S.a_pos _) (fun c x=>φ x*h c)
    (fun c=>(φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).mul_const (h c))]
  exact Finset.sum_congr rfl fun c _=>integral_mul_const _ _

theorem variation {n:ℕ} (φ:Test n)(ρ:ℝ)(np:UVIndex)(lo hi:Sites R np n→ℂ)(Q:ℝ)(nn:0≤Q)
    (seen:∀c:Sites R np n,mass φ ρ np c≠0 → ‖lo c-hi c‖≤Q) :
    ‖(∫x,φ x*lo (site ρ np x))-(∫x,φ x*hi (site ρ np x))‖≤(∫x,‖φ x‖)*Q:=by
  classical
  rw [submitted φ ρ np lo,submitted φ ρ np hi,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑c:Sites R np n,‖mass φ ρ np c*lo c-mass φ ρ np c*hi c‖:=norm_sum_le ..
    _ ≤ ∑c:Sites R np n,‖mass φ ρ np c‖*Q:=Finset.sum_le_sum fun c _=>by
      rw [←mul_sub,norm_mul]
      by_cases hc:mass φ ρ np c=0
      · rw [hc,norm_zero,zero_mul,zero_mul]
      · exact mul_le_mul_of_nonneg_left (seen c hc) (norm_nonneg _)
    _ ≤ (∫x,‖φ x‖)*Q:=by rw [←Finset.sum_mul];exact mul_le_mul_of_nonneg_right (total_variation φ ρ np) nn

def readingAt {n:ℕ}{J:Type}[Fintype J](d:Fin n→ℕ)(s:Finset (Fin n))(e:J→ℕ)(np:UVIndex)
    (z:Sites R np n)(x:∀i,(C).label (d i))(o:J→Site ((C).side np.1 np.2))(a:∀i,(C).label (e i)):ℂ:=
  moment ((C).beta np.1 np.2) (fun g=>(∏i:s,(C).O np.1 np.2 (x i) (z i) g)*word (R:=R) e np.1 np.2 o a g)

/-- The receipts for a genuine supporting cell involve the true marked footprints and one
coarse cube able to hold every priced source there. Each exterior keeps its own scale. -/
def Housing {n:ℕ}{J:Type}[Fintype J] (d:Fin n→ℕ)(s:Finset (Fin n))(e:J→ℕ)(rad:ℕ→ℕ)
    {N m p:ℕ}(active:m≤N)(k:J→ℕ)(fund:∀i,k i≤N)(o:J→Site ((C).side N p))(z:Sites R (N,p) n):Prop:=
  Avoids («C» := R.family) V₀ rad (fun i:s=>d i) (fun i=>z i) ∧
  (∀(i:s)(t:J),(↑(((C).localSection (e t)).footprint (o t)):Set (Site ((C).side N p)))⊆Mark.Outer (rad (d i)) (z i)) ∧
  ∃j:ℕ,∃early:j ≤ m,(∀i,j≤k i) ∧ ∃(v:s→Site ((C).side j p))(q:J→Site ((C).side j p)),
    let T:=center (C).S p (early.trans active) 0
    (∀i:s,z i∈T.margin (v i) (3*span (C).S active p)) ∧
    (∀i:J,o i∈T.margin (q i) (3*span (C).S (fund i) p)) ∧ Injective (Sum.elim v q)

theorem tested {n:ℕ}{J:Type}[Fintype J] (d:Fin n→Fin (cap+1))
    (w:∀i,(Bel (C).book).Field (d i))(Z:WilsonPositionThermometerCapStation.Group (C) cap)
    {N m p:ℕ}(active:m≤N)(r:Sites R (N,p) n→∀i,Emblems (C) (d i))(y:Sites R (N,p) n→∀i,Palette (C) (d i))
    (rad:ℕ→ℕ)(δ:ℝ)(nn:0≤δ)(source:∀z,WilsonThermometerWeakPositionMoments.expense V₀ d w Z (p:=p) active z (r z) (y z) rad δ)
    (e:J→ℕ)(k:J→ℕ)(fund:∀i,k i≤N)(A:J→ℝ)(pp:∀i,0≤A i)
    (owns:∀i,posted (R:=R) (e i) (k i) N p (fund i) (A i))
    (φ:Test n) (ρ:ℝ)(s:Finset (Fin n))(o:J→Site ((C).side N p))(a:∀i,(C).label (e i))
    (cell:∀z:Sites R (N,p) n,mass φ ρ (N,p) z≠0 → Housing V₀ (fun i=>(d i).val) s e rad active k fund o z):
    let actual:=fun i=>Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))
    let fitted:=fun z i=>reading (p:=p) (r z i) active (y z i)
    ‖(∫x,φ x*let z:=site ρ (N,p) x;readingAt (fun i=>(d i).val) s e (N,p) z (fitted z) o a)-
      (∫x,φ x*let z:=site ρ (N,p) x;readingAt (fun i=>(d i).val) s e (N,p) z actual o a)‖ ≤
      (∫x,‖φ x‖)*(δ*((∏i,rate (R:=R) (e i) (k i) (A i))*(∏i,(1+‖a i‖)))):=by
  intro actual fitted
  apply variation φ ρ (N,p) (fun z=>readingAt (fun i=>(d i).val) s e _ z (fitted z) o a)
    (fun z=>readingAt (fun i=>(d i).val) s e _ z actual o a)
  · apply mul_nonneg nn (mul_nonneg (Finset.prod_nonneg fun i _=> ?_) (Finset.prod_nonneg fun i _=>by positivity))
    dsimp only [WilsonThermometerWeakMeasuredExterior.rate]
    positivity [(C).S.a_pos (k i),pp i]
  intro z hz
  obtain ⟨apart,clear,j,early,visit,v,q,inside,outside,distinct⟩:=cell z hz
  exact WilsonThermometerWeakMeasuredExterior.stationary V₀ d w Z active z (r z) (y z) rad δ nn (source z)
    e k fund A owns s apart j early visit v q o a inside outside distinct clear

end YM.Integration.WilsonThermometerWeakExteriorTest
end
