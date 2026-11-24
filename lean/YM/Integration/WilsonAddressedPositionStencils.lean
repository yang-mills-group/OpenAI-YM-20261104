import YM.Integration.WilsonAddressedPositionReport
import YM.Integration.WilsonAddressedFiniteStencils

/-! The actual corrected physical MS roster on all dates of the funded upper collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPositionStencils
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

include M V₀ W b house portfolio
theorem original {I:Type} [Fintype I] (d:I→Fin (cap+1)) (w:∀i,(Bel (C).book).Field (d i))
    (simple:G.Simple) (panels:R2I.RG05Joint.AcrossPanels R.kit) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (rules:Rules G) (warehouse:Warehouse G) (book:Book (f:=f) (l:=l) (H:=H) A P) (lead:Leading F P)
    (slow:WilsonWindowReportingPace.Slow R.kit) (K v:ℕ) (pos:0<v) (μ ε:ℝ) (ep:0<ε):
    ∃E:Fin (cap+1)→ℝ,(∀j,0≤E j) ∧ ∀ᶠ s:ℝ in trail,
      let Z:=adjusted F P V A s
      let m:=WilsonMeasuredWindow.stop (Lev) simple v s
      projects (f:=f) (Y:=l) H d w Z (WilsonPositionPrescribedFrame.positioned F P V s) 0 s ∧
      ∃reported:m≤Z.station.k,∀ᶠ N:ℕ in atTop,∃late:Z.station.k<N,
        ∀(p:ℕ)(z:I→Site ((C).side N p)),∃(Q:∀i,Sight C (d i) p)(r:∀i,Emblems C (d i)),
        (∀i,Enrolled R.makes R.doors cash m N p (d i) (digits R N p (z i)) (Q i) (r i)) ∧
        ∃y:∀i,Palette (C) (d i),
          (∀i,b.step (d i) (N,p) (WilsonCapturedPrimaryWardRetimed.reading (p:=p) (r i) (reported.trans late.le) (y i))=
            b.step (d i) (N,p) (Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))) ∧
            size (y i) ≤ (E (d i)*(2*(Lev).clock.hatBeta m)^ε)*(cost (C) (d i)*(‖w i‖+costHint 0))) ∧
          ∀(u:ℕ)(mu:m≤u)(un:u≤N),u≤WilsonInvariantActionPosition.berth R K m →
          let S:=(C).path.rep N p u
          let h:=fun i=>WilsonCapturedPrimaryWardRetimed.lift (r i) mu (y i)
          ∃q:∀i,Palette (C) (d i),
            (∀i,b.step (d i) (N,p) (WilsonCapturedPrimaryWardRetimed.reading (p:=p) (r i) un (h i))=
              b.step (d i) (N,p) (Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))) ∧
              Printed (C) (d i) S 0 (kappa (C).path u)
                (Q i u (h i)) (q i) (h i) (cash (d i) u*size (h i))) ∧
            ∀J:Finset I,(∑a:WilsonAddressedFiniteStencils.Choices R (fun i=>(d i).val) J,
                ‖∏i:J,WilsonAddressedThermometerBasis.coefficient S.p.threshold (q i.val) (a i)‖) ≤
              ∏ i:J,WilsonAddressedThermometerBasis.fee R K m (d i.val)*
                (((C).S.a m/(C).S.a u)^(d i.val).val*size (y i.val)):=by
  obtain ⟨E,epos,forms⟩:=WilsonAddressedPositionReport.original M V₀ W b house F P V A portfolio d w
    simple panels shop rules warehouse book lead v pos μ ε ep
  refine ⟨E,epos,?_⟩
  filter_upwards [forms,(WilsonMeasuredWindow.stop_tendsto (Lev) simple v pos).eventually
    (WilsonAddressedFiniteStencils.original R (fun i=>(d i).val) simple slow shop K)] with s income quoted
  obtain ⟨measured,reported,active⟩:=income
  refine ⟨measured,reported,?_⟩
  filter_upwards [active] with N rights
  obtain ⟨late,invoice⟩:=rights
  refine ⟨late,?_⟩
  intro p z
  obtain ⟨Q,r,enrolled,sale⟩:=quoted N p (reported.trans late.le) z
  obtain ⟨y,paid⟩:=invoice p z Q r enrolled
  refine ⟨Q,r,enrolled,y,paid,?_⟩
  intro u mu un near
  obtain ⟨q,read,fees⟩:=sale y u mu un near
  refine ⟨q,fun i=>⟨?_,(read i).2⟩,fees⟩
  rw [(read i).1]
  exact (paid i).1

end YM.Integration.WilsonAddressedPositionStencils
end
