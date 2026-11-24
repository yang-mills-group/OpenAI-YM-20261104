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
namespace YM.Integration.WilsonThermometerWeakShiftedWord
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

theorem enrolled {m N p d:ℕ}(active:m≤N)(z:Site ((C).side N p))(a:Site ((C).side m p))
    {X:Sight (C) d p}{r:Emblems (C) d}
    (old:Enrolled R.makes R.doors cash m N p d (digits R N p z) X r):
    Enrolled R.makes R.doors cash m N p d (digits R N p (z+((C).S.toDepth active p).embed a)) X r:=by
  let S:=(C).S.toDepth active p
  have n:=WilsonAddressedWeakFixedChild.enrolled R active z (S.parent z+a) old
  simpa only [WilsonAddressedWeakFixedChild.slide,S,add_sub_cancel_left] using n

theorem footprint {d:ℕ}{B:Labels.Frame G d} (E:SectionData B){n:Side}(z o a:Site n)(k:ℕ):
    (↑(E.footprint z):Set (Site n))⊆ Mark.Outer k o →
    (↑(E.footprint (z+a)):Set (Site n))⊆Mark.Outer k (o+a):=by
  intro h x hx
  obtain ⟨u,member,rfl⟩:=Finset.mem_image.mp hx
  have old:=h (a:=wrap n u+z) (Finset.mem_image.mpr ⟨u,member,rfl⟩)
  change k<separation (wrap n u+(z+a)) (o+a)
  rw [←add_assoc,separation_translate]
  exact old

theorem absent {I:Type}(d:I→ℕ)(rad:ℕ→ℕ){N p:ℕ}(z:I→Site ((C).side N p))(a:Site ((C).side N p))
    (start:Avoids («C» := R.family) V₀ rad d z):
    Avoids («C» := R.family) V₀ rad d (fun i=>z i+a):=by
  intro i j diff
  exact ⟨footprint ((C).localSection (d j)) (z j) (z i) a _ (start i j diff).1,
         footprint (V₀ (d j)) (z j) (z i) a _ (start i j diff).2⟩

theorem shifted {n:ℕ}{J:Type}[Fintype J](d:Fin n→ℕ)(s:Finset (Fin n))(e:J→ℕ)(np:UVIndex)
    (c:Sites R np n)(x:∀i,(C).label (d i))(o:J→Site ((C).side np.1 np.2))(v:∀i,(C).label (e i))
    (t:Site ((C).side np.1 np.2)):
    WilsonThermometerWeakExteriorTest.readingAt d s e np (fun i=>c i+t) x (fun i=>o i+t) v =
    WilsonThermometerWeakExteriorTest.readingAt d s e np c x o v:=by
  let F:Config G ((C).side np.1 np.2)→ℂ:=fun U=>(∏i:s,(C).O np.1 np.2 (x i) (c i) U)*word (R:=R) e np.1 np.2 o v U
  have cont:Continuous F:=(continuous_finsetProd _ (fun i _=>(C).continuousO ..)).mul
    (WilsonThermometerWeakMeasuredExterior.continuous_word e np.1 np.2 o v)
  have shift:(fun U=>(∏i:s,(C).O np.1 np.2 (x i) (c i+t) U)*word (R:=R) e np.1 np.2 (fun i=>o i+t) v U)=F ∘ pull 1 t:=by
    funext U;simp only [F,Function.comp_apply,pull_one,(C).translation,WilsonThermometerWeakMeasuredExterior.word]
  unfold WilsonThermometerWeakExteriorTest.readingAt
  rw [shift,moment_pull _ _ _ _ (cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]

/-- Move each measured arm on its own original reporting grid. Its later fine addresses,
full regulated palette and the same upper Wilson coefficient are retained. -/
theorem heard {n N m p:ℕ} (d:Fin n→Fin (cap+1)) (w:∀i,(Bel (C).book).Field (d i))
    (Z:WilsonPositionThermometerCapStation.Group (C) cap)(live:m≤N)(rad:ℕ→ℕ)(Xcap Ycap:Fin n→ℝ)(δ:ℝ)
    (bank:∀s:Finset (Fin n),covered R V₀ b (fun i:s=>(d i).val) rad (fun i=>Xcap i) (fun i=>Ycap i) δ p live)
    (c:Sites R (N,p) n)(Q:∀i,Sight (C) (d i) p)(r:∀i,Emblems (C) (d i))(y:∀i,Palette (C) (d i))
    (course:∀i,Enrolled R.makes R.doors cash m N p (d i) (digits R N p (c i)) (Q i) (r i))
    (same:∀i,b.step (d i) (N,p) (reading (p:=p) (r i) live (y i))=
      b.step (d i) (N,p) (Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))))
    (costs:∀i,‖Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))‖≤Xcap i)
    (sizes:∀i,size (y i)≤Ycap i)(t:Fin n→Site ((C).side m p)):
    WilsonThermometerWeakPositionMoments.expense V₀ d w Z (p:=p) live (fun i=>c i+((C).S.toDepth live p).embed (t i))
      r y rad δ:=by
  intro s
  exact bank s (fun i=>c i+((C).S.toDepth live p).embed (t i)) (fun i=>Q i) (fun i=>r i)
    (fun i=>Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))) (fun i=>y i)
    (fun i=>enrolled live (c i) (t i) (course i)) (fun i=>(same i).symm) (fun i=>costs i) (fun i=>sizes i)

end YM.Integration.WilsonThermometerWeakShiftedWord
end
