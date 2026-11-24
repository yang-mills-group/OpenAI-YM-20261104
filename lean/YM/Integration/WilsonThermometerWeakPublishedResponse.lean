import YM.Integration.WilsonThermometerWeakPublishedCompact
import YM.Integration.WilsonThermometerWeakSignedJets

/-! At a fixed radius the signed invoice is evaluated on the very filed
cutoff course. Its limit uses the elected physical denominator and preserves
the observer. The independently prescribed numerical response is an input. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPublishedResponse
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

open WilsonThermometerWeakPublishedWatch WilsonPositionPhysicalCellTest WilsonCapturedPrimaryWardRetimed
open MeasureTheory Labels XSpace XSpace.Rose WilsonOffsetEquationLaw OPE.Orbits
open WilsonThermometerReflectedWatch WilsonThermometerMarchTerminalWatch
open WilsonThermometerWeakPublishedWatch
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{cap n m:ℕ}(d:Fin n→Fin (cap+1))
    (w:∀i,(Bel R.family.book).Field (d i))
    (Z:WilsonPositionThermometerCapStation.Group R.family cap)(a:Course R d m Z)
    (φ:Test n)(W:Watch R.family)(ρ:ℝ)(s:Finset (Fin n))

def nominated (z:ℕ×ℕ):ℂ:=
  screened d φ W ρ z.1 z.2 (fun _ i=>Z.station.wheel.atCut z (index Z (d i)) (Z.change (d i) (w i))) s

def published (z:ℕ×ℕ)(hn:a.start≤z.1):ℂ:=
  let B:=a.file z.1 hn z.2
  let hm:=a.report.trans (a.late z.1 hn).le
  screened d φ W ρ z.1 z.2 (fun c i=>reading (p:=z.2) (B.r c i) hm (B.y c i)) s

theorem original {l:Filter (ℕ×ℕ)}[l.NeBot](lies:l≤f.fuse)
    (screen:∀δ:ℝ,0<δ→∀ᶠz:ℕ×ℕ in f.fuse,‖difference d w Z a φ W ρ s z‖≤δ*(∫x,‖φ x‖))
    (trueValue independent:ℂ)(wage:ℝ)
    (ordered:Tendsto (nominated d w Z φ W ρ s) l (𝓝 trueValue))
    (issued:∀ᶠz in l,∃hn:a.start≤z.1,‖published d Z a φ W ρ s z hn-independent‖≤wage):
    ‖trueValue-independent‖≤wage:=by
  let δN:=difference d w Z a φ W ρ s
  have zero:Tendsto δN l (𝓝 0):=by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    let M:=∫x,‖φ x‖
    have mn:0≤M:=integral_nonneg fun _=>norm_nonneg _
    have below:0<1+M:=by positivity
    have price:=lies (screen (ε/(1+M)) (div_pos ep below))
    filter_upwards [price] with z fee
    rw [dist_zero_right]
    apply fee.trans_lt
    calc ε/(1+M)*M < ε/(1+M)*(1+M):=mul_lt_mul_of_pos_left (by linarith) (div_pos ep below)
         _ = ε:=div_mul_cancel₀ _ below.ne'
  have landing:Tendsto (fun z=>‖nominated d w Z φ W ρ s z+δN z-independent‖) l
      (𝓝 ‖trueValue-independent‖):=by simpa using ((ordered.add zero).sub tendsto_const_nhds).norm
  apply le_of_tendsto landing
  filter_upwards [issued] with z hzIssued
  obtain ⟨hn,hzSubmitted⟩:=hzIssued
  have same:nominated d w Z φ W ρ s z+δN z=published d Z a φ W ρ s z hn:=by
    dsimp only [δN,difference,nominated,published]
    rw [dif_pos hn]
    abel
  rw [same]
  exact hzSubmitted
end YM.Integration.WilsonThermometerWeakPublishedResponse
end
