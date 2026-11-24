import YM.Integration.WilsonThermometerWeakShiftedWord
import YM.Integration.WilsonThermometerWeakRosterCubes
import YM.Integration.WilsonThermometerWeakExteriorTest
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
namespace YM.Integration.WilsonThermometerWeakSeatedExterior
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


open WilsonThermometerWeakWardSourceBall (covered)


open WilsonThermometerWeakExteriorTest (readingAt Housing)

def padding (J:Type)[Fintype J]{n:ℕ}(s:Finset (Fin n)):ℕ:=
  (WilsonThermometerWeakRosterCubes.original (C).S (s ⊕ J)).choose

/-- The true lifted displacements, before making a common translation. -/
def Seats {n:ℕ}{J:Type}[Fintype J](s:Finset (Fin n)){N m p:ℕ}(k:J→ℕ)
    (z:Sites R (N,p) n)(o:J→Site ((C).side N p)):Prop:=
  ∃j:ℕ,j+padding (R:=R) J s+1 ≤ m ∧ (∀v,j+padding (R:=R) J s+1≤k v) ∧
    ∃x:(s ⊕ J) → Lattice.Cover,(∀i:s,Lattice.wrap ((C).side N p) (x (.inl i))=z i) ∧
      (∀i:J,Lattice.wrap ((C).side N p) (x (.inr i))=o i) ∧
      (∀i i',i≠i'→∃a:Axis,(C).S.a j≤|(C).S.gridPoint N (x i) a-(C).S.gridPoint N (x i') a|) ∧
      ∀i i' (a:Axis),2*(|(C).S.gridPoint N (x i) a-(C).S.gridPoint N (x i') a|+(C).S.a j)<((C).side j p).val*(C).S.a j

theorem seated {n:ℕ}{J:Type}[Fintype J](d:Fin n→ℕ)(s:Finset (Fin n))(e:J→ℕ)(rad:ℕ→ℕ)
    {N m p:ℕ}(active:m≤N)(k:J→ℕ)(fund:∀i,k i≤N)(o:J→Site ((C).side N p))(z:Sites R (N,p) n)
    (apart:Avoids («C» :=R.family) V₀ rad (fun i:s=>d i) (fun i=>z i))
    (clear:∀(i:s)(t:J),(↑(((C).localSection (e t)).footprint (o t)):Set (Site ((C).side N p)))⊆Mark.Outer (rad (d i)) (z i))
    (space:Seats (R:=R) (m:=m) s k z o):
    ∃t:Site ((C).side m p),let g:=((C).S.toDepth active p).embed t
      Housing V₀ d s e rad active k fund (fun i=>o i+g) (fun i=>z i+g):=by
  obtain ⟨j,start,deep,x,hz,ho,gap,per⟩:=space
  let r:s ⊕ J→ℕ:=Sum.elim (fun _=>m) k
  have a:∀i,j+padding (R:=R) J s+1 ≤ r i:=fun i=>by cases i with
    | inl i=>exact start
    | inr i=>exact deep i
  have paid:∀i,r i≤N:=fun i=>by cases i with
    | inl i=>exact active
    | inr i=>exact fund i
  have h: j ≤ m:=by omega
  obtain ⟨t,v,inj,hit⟩:=(WilsonThermometerWeakRosterCubes.original (C).S (s ⊕ J)).choose_spec j m N p active start r a paid x gap per
  let g:=((C).S.toDepth active p).embed t
  refine ⟨t,WilsonThermometerWeakShiftedWord.absent V₀ (fun i:s=>d i) rad (fun i=>z i) g apart,?_,j,h,fun i=>by have:=deep i;omega,
    (fun i=>v (.inl i)),(fun i=>v (.inr i)),?_,?_,?_⟩
  · exact fun i l=>WilsonThermometerWeakShiftedWord.footprint _ (o l) (z i) g _ (clear i l)
  · intro i;simpa only [hz,r,Sum.elim_inl] using! hit (.inl i)
  · intro i;simpa only [ho,r,Sum.elim_inr] using! hit (.inr i)
  · intro i i' eq
    apply inj
    cases i <;> cases i' <;> exact eq

theorem atSite {n:ℕ}{J:Type}[Fintype J] (d:Fin n→Fin (cap+1))
    (w:∀i,(Bel (C).book).Field (d i))(Z:WilsonPositionThermometerCapStation.Group (C) cap)
    {N m p:ℕ}(active:m≤N)(z:Sites R (N,p) n)(r:∀i,Emblems (C) (d i))(y:∀i,Palette (C) (d i))
    (rad:ℕ→ℕ)(δ:ℝ)(nn:0≤δ)
    (source:∀(t:Site ((C).side m p)),WilsonThermometerWeakPositionMoments.expense V₀ d w Z (p:=p) active
        (fun i=>z i+((C).S.toDepth active p).embed t) r y rad δ)
    (e:J→ℕ)(k:J→ℕ)(fund:∀i,k i≤N)(A:J→ℝ)
    (owns:∀i,posted (R:=R) (e i) (k i) N p (fund i) (A i))
    (s:Finset (Fin n))(o:J→Site ((C).side N p))(a:∀i,(C).label (e i))
    (apart:Avoids («C» :=R.family) V₀ rad (fun i:s=>(d i).val) (fun i=>z i))
    (clear:∀(i:s)(t:J),(↑(((C).localSection (e t)).footprint (o t)):Set (Site ((C).side N p)))⊆Mark.Outer (rad (d i)) (z i))
    (space:Seats (R:=R) (m:=m) s k z o):
    let actual:=fun i=>Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))
    let fitted:=fun i=>reading (p:=p) (r i) active (y i)
    ‖readingAt (R:=R) (fun i=>(d i).val) s e (N,p) z fitted o a - readingAt (R:=R) (fun i=>(d i).val) s e (N,p) z actual o a‖ ≤
      δ*((∏i,rate (R:=R) (e i) (k i) (A i))*(∏i,(1+‖a i‖))):=by
  intro actual fitted
  obtain ⟨t,apart,clear,j,early,visit,v,q,inside,outside,distinct⟩:=
    seated V₀ (fun i=>(d i).val) s e rad active k fund o z apart clear space
  let g:=((C).S.toDepth active p).embed t
  have paid:‖readingAt (R:=R) (fun i=>(d i).val) s e (N,p) (fun i=>z i+g) fitted (fun i=>o i+g) a -
      readingAt (R:=R) (fun i=>(d i).val) s e (N,p) (fun i=>z i+g) actual (fun i=>o i+g) a‖≤_:=
    WilsonThermometerWeakMeasuredExterior.stationary V₀ d w Z active (fun i=>z i+g)
      r y rad δ nn (source t) e k fund A owns s apart j early visit v q (fun i=>o i+g) a
      inside outside distinct clear
  rw [WilsonThermometerWeakShiftedWord.shifted (R:=R) (fun i=>(d i).val) s e _ z fitted o a g,
      WilsonThermometerWeakShiftedWord.shifted (R:=R) (fun i=>(d i).val) s e _ z actual o a g] at paid
  exact paid

theorem tested {n:ℕ}{J:Type}[Fintype J] (d:Fin n→Fin (cap+1))
    (w:∀i,(Bel (C).book).Field (d i))(Z:WilsonPositionThermometerCapStation.Group (C) cap)
    {N m p:ℕ}(active:m≤N)(r:Sites R (N,p) n→∀i,Emblems (C) (d i))(y:Sites R (N,p) n→∀i,Palette (C) (d i))
    (rad:ℕ→ℕ)(δ:ℝ)(nn:0≤δ)
    (source:∀z (t:Site ((C).side m p)),WilsonThermometerWeakPositionMoments.expense V₀ d w Z (p:=p) active
        (fun i=>z i+((C).S.toDepth active p).embed t) (r z) (y z) rad δ)
    (e:J→ℕ)(k:J→ℕ)(fund:∀i,k i≤N)(A:J→ℝ)(pp:∀i,0≤A i)
    (owns:∀i,posted (R:=R) (e i) (k i) N p (fund i) (A i))
    (φ:Test n) (ρ:ℝ)(s:Finset (Fin n))(o:J→Site ((C).side N p))(a:∀i,(C).label (e i))
    (cell:∀z:Sites R (N,p) n,mass φ ρ (N,p) z≠0 →
      Avoids («C» :=R.family) V₀ rad (fun i:s=>(d i).val) (fun i=>z i) ∧
      (∀(i:s)(t:J),(↑(((C).localSection (e t)).footprint (o t)):Set (Site ((C).side N p)))⊆Mark.Outer (rad (d i)) (z i)) ∧
      Seats (R:=R) (m:=m) s k z o):
    let actual:=fun i=>Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))
    let fitted:=fun z i=>reading (p:=p) (r z i) active (y z i)
    ‖(∫x,φ x*let z:=site ρ (N,p) x;readingAt (fun i=>(d i).val) s e (N,p) z (fitted z) o a)-
      (∫x,φ x*let z:=site ρ (N,p) x;readingAt (fun i=>(d i).val) s e (N,p) z actual o a)‖ ≤
      (∫x,‖φ x‖)*(δ*((∏i,rate (R:=R) (e i) (k i) (A i))*(∏i,(1+‖a i‖)))):=by
  intro actual fitted
  apply WilsonThermometerWeakExteriorTest.variation φ ρ (N,p) (fun z=>readingAt (fun i=>(d i).val) s e _ z (fitted z) o a)
    (fun z=>readingAt (fun i=>(d i).val) s e _ z actual o a)
  · apply mul_nonneg nn (mul_nonneg (Finset.prod_nonneg fun i _=> ?_) (Finset.prod_nonneg fun i _=>by positivity))
    dsimp only [WilsonThermometerWeakMeasuredExterior.rate]
    positivity [(C).S.a_pos (k i),pp i]
  intro z seen
  obtain ⟨apart,clear,space⟩:=cell z seen
  exact atSite V₀ d w Z active z (r z) (y z) rad δ nn (source z) e k fund A owns s o a apart clear space

end YM.Integration.WilsonThermometerWeakSeatedExterior
end
