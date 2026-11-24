import YM.Integration.WilsonCapturedPrimaryWardRelay
import YM.Integration.WilsonThermometerWeakNominatedTriple
import YM.Integration.WilsonPositionOriginalDiagnosticCorridor

/-! Deposit the three genuinely measured fields on their separated physical reporting routes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardPaidThermometer
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
    {l:Ultrafilter (ℕ×ℕ)} (A:ℝ→WilsonPositionThermometerCapStation.Group R.family 6)
local notation "C" => R.family
local notation "Lev" => R.family.path.levels
local notation "cash" => WilsonThermometerOffsetLedger.cash R
private abbrev armGrade := WilsonPositionThermometerGradedSource.grade


include M V₀ W b house
theorem original (simple:G.Simple) (panels:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (rules:Rules G) (warehouse:Warehouse G)
    (book:Book (f:=f) (l:=l) (H:=H) A P) (lead:Leading F P) (v:ℕ) (pos:0<v) (μ ε:ℝ) (ep:0<ε):
    ∃E:ℝ,0≤E ∧ ∀ᶠ t:ℝ in trail,let Z:=adjusted F P V A t
      let m:=WilsonMeasuredWindow.stop (Lev) simple v t
      ∃reported:m≤Z.station.k,∀ᶠ N:ℕ in atTop,∃late:Z.station.k<N,∀p,
      ∀(z:Fin 3→Site ((C).side N p)) (Q:∀i:Fin 3,Sight C (armGrade i) p)
        (r:∀i:Fin 3,Emblems C (armGrade i)), z 0=0 →
        (∀i,Enrolled R.makes R.doors cash m N p (armGrade i) (digits R N p (z i)) (Q i) (r i)) →
        ∀s:Badge,WilsonThermometerWeakNominatedTriple.paid Z m N p (reported.trans late.le) s r
          (E*(2*(Lev).clock.hatBeta m)^ε):=by
  let τ:=ε/8
  have tp:0<τ:=by unfold τ;positivity
  obtain ⟨E,epos,weak⟩:=WilsonThermometerWeakNominatedTriple.original M V₀ W b house F P V A simple panels shop rules warehouse book lead μ τ tp
  refine ⟨E,epos,?_⟩
  let d:Badge×Fin 3 → Fin 7:=fun i=>armGrade i.2
  let w:∀i:Badge×Fin 3,(Bel (C).book).Field (d i):=fun i=>source (C) i.1 i.2
  have events j:=WilsonPositionCorrectedCap.mixed F P V A book lead d w j
  have go:Tendsto (fun t=>(adjusted F P V A t).station.k) trail atTop:=
    tendsto_atTop.mpr fun j=>(events j).mono fun _ e=>e.1
  have track (i:Fin 3):=
    (WilsonThermometerOffsetLedger.original R simple shop (armGrade i)).mono fun _ paid=>paid.1
  have timely:=WilsonCapturedPrimaryWardRetimed.cash (C)
  obtain ⟨floor,free⟩:=eventually_atTop.1 ((eventually_all.mpr track).and timely)
  have destination:=WilsonMeasuredWindow.stop_tendsto (Lev) simple v pos
  filter_upwards [weak floor,events 0,go.eventually (WilsonPositionOriginalDiagnosticCorridor.original (Lev) simple v tp),
    destination.eventually (eventually_ge_atTop floor)] with t bank elected price active
  let Z:=adjusted F P V A t
  let m:=WilsonMeasuredWindow.stop (Lev) simple v t
  have radial:Next.Rank.Station.gap (Lev) Z.station.b Z.station.k=t:=elected.2.2.1
  obtain ⟨ms,span_m,clock⟩:=price Z.station.b elected.2.1.high.1 elected.2.1.high.2
  rw [radial] at ms span_m clock
  obtain ⟨k,base,ks,span_k,issued⟩:=bank
  refine ⟨ms,?_⟩
  filter_upwards [issued] with N panel
  obtain ⟨late,sale⟩:=panel
  let kn:=ks.trans late.le
  let mn:=ms.trans late.le
  refine ⟨late,?_⟩
  intro per z Q r zero courses
  let β:ℝ:=(Lev).clock.hatBeta Z.station.k
  let L:ℝ:=β^τ
  have high:1≤β:=((Lev).fits.delayed _).le
  have large:1≤L:=Real.one_le_rpow high tp.le
  have forwards:(C).S.a k/(C).S.a m≤ L:=le_trans (div_le_div_of_nonneg_left ((C).S.a_pos k).le ((C).S.a_pos _) ((C).S.strictAnti.antitone ms)) span_k
  have backwards:(C).S.a m/(C).S.a k≤ L:=le_trans (div_le_div_of_nonneg_left ((C).S.a_pos m).le ((C).S.a_pos _) ((C).S.strictAnti.antitone ks)) span_m
  choose Q' r' enrolled send carried using fun i:Fin 3=>WilsonCapturedPrimaryWardRelay.original (courses i) kn mn
    ((free k base).1 i) large forwards backwards (free k base).2 (free m active).2
  intro s
  obtain ⟨y,price_y⟩:=sale per z Q' r' zero enrolled s
  refine ⟨fun i=>send i (y i),?_⟩
  intro i
  have fitted:WilsonCapturedPrimaryWardRetimed.reading (p:=per) (r' i) kn (y i)=_ := (price_y i).1
  refine ⟨((carried i (y i)).1).trans fitted,?_⟩
  let fee:=WilsonThermometerMarchReference.fee (C) s i
  have feePos:0≤fee:=by unfold fee WilsonThermometerMarchReference.fee WilsonPositionThermometerStationNorm.cost costHint;positivity
  have coef:0≤E*fee:=mul_nonneg epos feePos
  have degree:(armGrade i).val+1≤7:=by have :=(armGrade i).isLt;omega
  have factor:L^7*L=β^ε:=by
    rw [←pow_succ,←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans high)]
    congr 1
    dsimp only [τ]
    norm_num
  calc
    size (send i (y i)) ≤ L^((armGrade i).val+1)*size (y i):=(carried i (y i)).2
    _ ≤ L^7*((E*L)*fee):=mul_le_mul (pow_le_pow_right₀ large degree) (price_y i).2 (size_ge _) (pow_nonneg (zero_le_one.trans large) _)
    _ = (L^7*L)*(E*fee):=by ring
    _ ≤ (2*(Lev).clock.hatBeta m)^ε*(E*fee):=by
      rw [factor];exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (zero_le_one.trans high) clock ep.le) coef
    _ = _:=by dsimp only [fee];ring

end YM.Integration.WilsonCapturedPrimaryWardPaidThermometer
