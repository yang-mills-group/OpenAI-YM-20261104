import YM.Integration.WilsonThermometerWeakPublishedWatch
import YM.Integration.WilsonThermometerWeakCompactRoom

/-! A single physical enrollment serves every shrinking joint probe supported in the nominated compact. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPublishedCompact
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

open WilsonThermometerWeakPositionMoments (expense)


open WilsonPositionPhysicalCellTest (Sites)
open WilsonThermometerWeakExteriorOriginal (stencils)


open WilsonThermometerWeakPublishedRoster (Sheet paid)
open WilsonPositionPhysicalCellTest (site mass)
open WilsonThermometerWeakMeasuredExterior (rate)
open WilsonThermometerWeakExteriorTest (readingAt)
open WilsonThermometerWeakOriginalShapeGeometry (fixed)
open WilsonThermometerMarchSupported (period)

open WilsonThermometerWeakPublishedWatch (Course salary shifts difference)
open private tested from YM.Integration.WilsonThermometerWeakPublishedWatch
include M V₀ W b house portfolio
theorem original {n:ℕ}(d:Fin n→Fin (cap+1)) (w:∀i,(Bel (C).book).Field (d i))
    (simple:G.Simple) (panels:R2I.RG05Joint.AcrossPanels R.kit) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (rules:Rules G) (warehouse:Warehouse G) (book:Book (f:=f) (l:=l) (H:=H) A P) (lead:Leading F P)
    (slow:WilsonWindowReportingPace.Slow R.kit) (K v:ℕ) (vp:0<v) (μ ε:ℝ) (ep:0<ε):
    let Z:=adjusted F P V A;let m:=WilsonMeasuredWindow.stop (Lev) simple v
    ∃E:Fin (cap+1)→ℝ,(∀j,0≤E j) ∧ ∃use:Set ℝ, use∈trail ∧
      ∃released:∀ρ,ρ∈use → Course R d (m ρ) (Z ρ),
      (∀ρ (hρ:ρ∈use),projects (f:=f) (Y:=l) H d w (Z ρ) (WilsonPositionPrescribedFrame.positioned F P V ρ) 0 ρ ∧
        salary b d w (Z ρ) K E ε (released ρ hρ)) ∧
      ∀(L:Set (Points n)),IsCompact L→L⊆conf n→∀(W₁:Watch (C)),∀ᶠρ:ℝ in trail,∃hρ:ρ∈use,∀(φ:Test n),tsupport (φ:Points n→ℂ)⊆L→∀δ:ℝ,0<δ→∀ᶠ z:ℕ×ℕ in f.fuse,∀s:Finset (Fin n),
        ‖difference d w (Z ρ) (released ρ hρ) φ W₁ ρ s z‖≤(∫x,‖φ x‖)*δ:=by
  classical
  dsimp only
  obtain ⟨rad,E,nn,input⟩:=WilsonThermometerWeakPublishedRoster.original M V₀ W b house F P V A portfolio d w
    simple panels shop rules warehouse book lead slow K v vp μ ε ep
  let Z:=adjusted F P V A
  let m:=WilsonMeasuredWindow.stop (Lev) simple v
  let use:Set ℝ:={ρ|∃a:Course R d (m ρ) (Z ρ),projects (f:=f) (Y:=l) H d w (Z ρ) (WilsonPositionPrescribedFrame.positioned F P V ρ) 0 ρ ∧
    salary b d w (Z ρ) K E ε a ∧ shifts (f:=f) V₀ d w (Z ρ) a rad}
  have accepted:use∈trail:=input.mono fun ρ ⟨pr,r,N,late,files,hbill,htest⟩=>
    ⟨⟨r,N,late,files⟩,pr,hbill,htest⟩
  choose actual terms using fun ρ (hρ:ρ∈use)=>hρ
  refine ⟨E,nn,use,accepted,actual,fun ρ hρ=>⟨(terms ρ hρ).1,(terms ρ hρ).2.1⟩,?_⟩
  intro L compact cleared W₁
  obtain ⟨p₀,shapes⟩:=WilsonThermometerWeakCompactRoom.original (R:=R) simple slow v vp V₀ (fun i=>(d i).val)
    (fun i=>(W₁.q i).1) rad L compact cleared W₁.held W₁.origin (generic_conf _ W₁.wild)
  filter_upwards [accepted,shapes] with ρ hρ seats
  obtain ⟨N₀,geometry⟩:=seats
  exact ⟨hρ,fun φ sub=>tested V₀ d w (Z ρ) (actual ρ hρ) rad (terms ρ hρ).2.2 F.room.copies φ W₁ ρ N₀ p₀ (fun p hp N hN s k hk=>geometry p hp N hN s k hk φ sub)⟩

end YM.Integration.WilsonThermometerWeakPublishedCompact
end
