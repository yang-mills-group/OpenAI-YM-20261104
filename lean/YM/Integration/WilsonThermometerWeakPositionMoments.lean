import YM.Integration.WilsonAddressedPositionStencils
import YM.Integration.WilsonThermometerWeakWardSourceBall

/-! The corrected position source, its priced upper stencils, and every
occupied Ward-erased moment against the cleared exterior of the same Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPositionMoments
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

def expense {I:Type} [Fintype I] (d:I→Fin (cap+1)) (w:∀i,(Bel (C).book).Field (d i))
    (Z:WilsonPositionThermometerCapStation.Group (C) cap) {N m p:ℕ}(active:m≤N)
    (z:I→Site ((C).side N p))(r:∀i,Emblems C (d i))(y:∀i,Palette (C) (d i))
    (rad:ℕ→ℕ)(δ:ℝ):Prop:=
  ∀s:Finset I,Avoids («C» := R.family) V₀ rad (fun i:s=>(d i).val) (fun i=>z i) →
  ∀(j:ℕ)(early:j ≤ m)(v:s→Site ((C).side j p)),let U:=Cells.center (C).S p (early.trans active) 0
  (∀i:s,z i∈U.margin (v i) (3*Cells.span (C).S active p)) →
  ∀(J:Type)[Fintype J](loc:J→U.Cell)(watch:J → Config G ((C).side N p)→ℂ),
  Injective (Sum.elim v loc) → (∀i,Interior (U.chamber 0) (watch i)) →
  let outside:=exterior U loc watch
  (∀i:s,LocalOn (Mark.Outer (rad (d i)) (z i)) outside) → Envelope outside →
  ‖moment ((C).beta N p) (fun g=>(∏i:s,(C).O N p (reading (p:=p) (r i) active (y i)) (z i) g)*outside g)-
   moment ((C).beta N p) (fun g=>(∏i:s,(C).O N p
     (Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))) (z i) g)*outside g)‖ ≤
  δ*∏i,U.rootTest ((C).beta N p) (watch i)

include M V₀ W b house portfolio
theorem original {I:Type} [Fintype I] (d:I→Fin (cap+1)) (w:∀i,(Bel (C).book).Field (d i))
    (simple:G.Simple) (panels:R2I.RG05Joint.AcrossPanels R.kit) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (rules:Rules G) (warehouse:Warehouse G) (book:Book (f:=f) (l:=l) (H:=H) A P) (lead:Leading F P)
    (slow:WilsonWindowReportingPace.Slow R.kit) (K v:ℕ) (pos:0<v) (μ ε:ℝ) (ep:0<ε):
    ∃rad:ℕ→ℕ,∃E:Fin (cap+1)→ℝ,(∀j,0≤E j) ∧ ∀ᶠ s:ℝ in trail,
      let Z:=adjusted F P V A s
      let m:=WilsonMeasuredWindow.stop (Lev) simple v s
      projects (f:=f) (Y:=l) H d w Z (WilsonPositionPrescribedFrame.positioned F P V s) 0 s ∧
      ∃reported:m≤Z.station.k,∀δ:ℝ,0<δ → ∀ᶠ n:ℕ×ℕ in f.fuse,let N:=n.1;let p:=n.2
        ∃late:Z.station.k<N,∀(z:I→Site ((C).side N p)),∃(Q:∀i,Sight C (d i) p)(r:∀i,Emblems C (d i)),
        (∀i,Enrolled R.makes R.doors cash m N p (d i) (digits R N p (z i)) (Q i) (r i)) ∧
        ∃y:∀i,Palette (C) (d i),
          (∀i,b.step (d i) (N,p) (WilsonCapturedPrimaryWardRetimed.reading (p:=p) (r i) (reported.trans late.le) (y i))=
            b.step (d i) (N,p) (Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))) ∧
            size (y i) ≤ (E (d i)*(2*(Lev).clock.hatBeta m)^ε)*(cost (C) (d i)*(‖w i‖+costHint 0))) ∧
          (∀(u:ℕ)(mu:m≤u)(un:u≤N),u≤WilsonInvariantActionPosition.berth R K m →
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
                (((C).S.a m/(C).S.a u)^(d i.val).val*size (y i.val))) ∧ expense V₀ d w Z (p:=p) (reported.trans late.le) z r y rad δ:=by
  classical
  obtain ⟨E,en,fields⟩:=WilsonAddressedPositionStencils.original M V₀ W b house F P V A portfolio d w
    simple panels shop rules warehouse book lead slow K v pos μ ε ep
  obtain ⟨rad,_,_,threshold⟩:=WilsonThermometerWeakWardSourceBall.original R M V₀ W b portfolio house cap
    simple panels shop rules warehouse μ ε ep f H F.room.copies
  refine ⟨rad,E,en,?_⟩
  have go:Tendsto (fun s=>(adjusted F P V A s).station.k) trail atTop:=tendsto_atTop.mpr
    fun j=>(WilsonPositionCorrectedCap.mixed F P V A book lead d w j).mono fun _ e=>e.1
  have stops:=WilsonMeasuredWindow.stop_tendsto (Lev) simple v pos
  filter_upwards [fields,stops.eventually (threshold I d),go.eventually (eventually_all.mpr (fun i:I=>
      WilsonThermometerReferenceStation.cutoff («C» := R.family) (f:=f) (H:=H) simple R.makes (d i).val ε ep))]
    with s inputs available upperPay
  let Z:=adjusted F P V A s
  let m:=WilsonMeasuredWindow.stop (Lev) simple v s
  obtain ⟨proj,reported,income⟩:=inputs
  refine ⟨proj,reported,?_⟩
  intro δ small
  let Xcap (i:I):=Real.exp (Work.D01.columnLogs (Lev) Z.station.k)*
    (((Lev).clock.hatBeta Z.station.k)^ε*(cost (C) (d i)*‖Z.change (d i) (w i)‖))
  let Ycap (i:I):=(E (d i)*(2*(Lev).clock.hatBeta m)^ε)*
      (cost (C) (d i)*(‖w i‖+costHint 0))
  filter_upwards [(upper f).eventually income,available Xcap Ycap δ small] with n old exteriorBudget
  obtain ⟨late,actual⟩:=old
  obtain ⟨_,_,offers⟩:=exteriorBudget
  refine ⟨late,fun z=>?_⟩
  obtain ⟨Q,r,lodged,y,matchPaid,upperStencils⟩:=actual n.2 z
  refine ⟨Q,r,lodged,y,matchPaid,upperStencils,?_⟩
  let x (i:I):=Z.station.wheel.atCut n (index Z (d i)) (Z.change (d i) (w i))
  have upperBound (i:I):‖x i‖≤Xcap i:=by
    have coin:‖x i‖≤((C).labels.level (d i)).coeffSize (x i):=(pi_norm_le_iff_of_nonneg
      (Work.G08.size_nonneg _ _)).mpr fun j=>Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ j)
    exact coin.trans (upperPay i Z.station (index Z (d i)) rfl rfl proj.2.1 (Z.change (d i) (w i)) n.1 n.2 late)
  intro t
  exact offers t (fun i=>z i) (fun i=>Q i) (fun i=>r i) (fun i=>x i)
    (fun i=>y i) (fun i=>lodged i) (fun i=>(matchPaid i).1.symm) (fun i=>upperBound i) (fun i=>(matchPaid i).2)

end YM.Integration.WilsonThermometerWeakPositionMoments
end
