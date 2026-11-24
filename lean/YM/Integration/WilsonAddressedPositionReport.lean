import YM.Integration.WilsonThermometerWeakSharedReport
import YM.Integration.WilsonCapturedPrimaryWardPaidThermometer

/-! The finite true weak quotient of every jointly positioned homogeneous input on one original reporting course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPositionReport
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
    (v:ℕ) (pos:0<v) (μ ε:ℝ) (ep:0<ε):
    ∃E:Fin (cap+1)→ℝ,(∀j,0≤E j) ∧ ∀ᶠ s:ℝ in trail,
      let Z:=adjusted F P V A s
      let m:=WilsonMeasuredWindow.stop (Lev) simple v s
      projects (f:=f) (Y:=l) H d w Z (WilsonPositionPrescribedFrame.positioned F P V s) 0 s ∧
      ∃reported:m≤Z.station.k,∀ᶠ N:ℕ in atTop,∃late:Z.station.k<N,∀(p:ℕ)(z:I→Site ((C).side N p))
        (Q:∀i,Sight C (d i) p) (r:∀i,Emblems C (d i)),
        (∀i,Enrolled R.makes R.doors cash m N p (d i) (digits R N p (z i)) (Q i) (r i)) →
        ∃y:∀i,Palette (C) (d i),∀i,
          b.step (d i) (N,p) (WilsonCapturedPrimaryWardRetimed.reading (p:=p) (r i) (reported.trans late.le) (y i))=
            b.step (d i) (N,p) (Z.station.wheel.atCut (N,p) (index Z (d i)) (Z.change (d i) (w i))) ∧
          size (y i) ≤ (E (d i)*(2*(Lev).clock.hatBeta m)^ε)*
            (cost (C) (d i)*(‖w i‖+costHint 0)):=by
  let τ:=ε/((cap+2:ℕ):ℝ)
  have dp:0<((cap+2:ℕ):ℝ):=by positivity
  have tp:0<τ:=div_pos ep dp
  obtain ⟨E,positive,issued⟩:=WilsonThermometerWeakSharedReport.original R M V₀ W b portfolio house cap
    simple panels shop rules warehouse μ τ tp f H
  refine ⟨E,positive,?_⟩
  have events j:=WilsonPositionCorrectedCap.mixed F P V A book lead d w j
  have go:Tendsto (fun s=>(adjusted F P V A s).station.k) trail atTop:=
    tendsto_atTop.mpr fun j=>(events j).mono fun _ e=>e.1
  have track:=eventually_all.mpr (fun i:I=>(WilsonThermometerOffsetLedger.original R simple shop (d i)).mono
    (fun _ p=>p.1))
  have cashFlow:=WilsonCapturedPrimaryWardRetimed.cash (C)
  have stops:=WilsonMeasuredWindow.stop_tendsto (Lev) simple v pos
  filter_upwards [events 0,go.eventually issued,go.eventually track,go.eventually cashFlow,
    stops.eventually cashFlow,go.eventually (WilsonPositionOriginalDiagnosticCorridor.original (Lev) simple v tp)]
    with s landed offers starts fromStar fromMesh costs
  let Z:=adjusted F P V A s
  let k:=Z.station.k
  let m:=WilsonMeasuredWindow.stop (Lev) simple v s
  have radial:Next.Rank.Station.gap (Lev) Z.station.b k=s:=landed.2.2.1
  obtain ⟨reported,spread,clocks⟩:=costs Z.station.b landed.2.1.high.1 landed.2.1.high.2
  rw [radial] at reported spread clocks
  let β:=(Lev).clock.hatBeta k
  let L:=β^τ
  have bh:1≤β:=((Lev).fits.delayed k).le
  have large:1≤L:=Real.one_le_rpow bh tp.le
  have costNum (i:I):0≤cost (C) (d i):=by unfold cost;positivity
  have within:(C).S.a k/(C).S.a m≤L:=((div_le_one ((C).S.a_pos _)).2 ((C).S.strictAnti.antitone reported)).trans large
  have absorb:L^(cap+2)=β^ε:=by
    dsimp only [L]
    rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans bh)]
    congr 1
    exact div_mul_cancel₀ _ dp.ne'
  refine ⟨landed,reported,?_⟩
  filter_upwards [offers] with N arrived
  obtain ⟨late,read⟩:=arrived
  refine ⟨late,?_⟩
  intro p z Q r enrolled
  classical
  choose V' r' hired send trip using fun i=>WilsonCapturedPrimaryWardRelay.original (enrolled i) late.le
    (reported.trans late.le) (starts i) large within spread fromStar fromMesh
  choose y fitted price using fun i=>read (d i) p (z i) (V' i) (r' i) (hired i)
    Z.station ((Nat.le_of_lt_succ (d i).isLt).trans Z.fits) (Z.change (d i) (w i)) rfl landed.2.1
  refine ⟨fun i=>send i (y i),?_⟩
  intro i
  refine ⟨(congrArg (b.step (d i) (N,p)) (trip i (y i)).1).trans (fitted i),?_⟩
  have close:‖Z.change (d i) (w i)-w i‖≤costHint 0:=landed.2.2.2.2.2 i
  have normBound:‖Z.change (d i) (w i)‖≤‖w i‖+costHint 0:=calc
    _ = ‖(Z.change (d i) (w i)-w i)+w i‖:=by rw [sub_add_cancel]
    _ ≤ ‖Z.change (d i) (w i)-w i‖+‖w i‖:=norm_add_le _ _
    _ ≤ _:=by linarith only [close]
  let fee:=cost (C) (d i)*(‖w i‖+costHint 0)
  have feePos:0≤fee:=mul_nonneg (costNum i) ((norm_nonneg _).trans normBound)
  have payItem:size (y i)≤(E (d i)*L)*fee:=(price i).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left normBound (costNum i)) (mul_nonneg (positive _) (zero_le_one.trans large)))
  have level:(d i).val+1≤cap+1:=by have :=(d i).isLt;omega
  calc
    size (send i (y i)) ≤ L^((d i).val+1)*size (y i):=(trip i (y i)).2
    _ ≤ L^(cap+1)*((E (d i)*L)*fee):=mul_le_mul (pow_le_pow_right₀ large level) payItem (size_ge _) (pow_nonneg (zero_le_one.trans large) _)
    _ = L^(cap+2)*(E (d i)*fee):=by rw [show cap+2=cap+1+1 by omega,pow_succ L (cap+1)];ring
    _ ≤ (2*(Lev).clock.hatBeta m)^ε*(E (d i)*fee):=by
      rw [absorb];exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (zero_le_one.trans bh) clocks ep.le) (mul_nonneg (positive _) feePos)
    _ = _:=by dsimp only [fee];ring

end YM.Integration.WilsonAddressedPositionReport
end
