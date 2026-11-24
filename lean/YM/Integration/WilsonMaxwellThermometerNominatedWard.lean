import YM.Integration.WilsonCapturedPrimaryWardPaidSource
import YM.Integration.WilsonMaxwellThermometerNominatedPupils

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedWard
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



open WilsonCapturedPrimaryActiveArms (Shelf)
open WilsonCapturedPrimaryFaceWallet WilsonCapturedPrimaryPhysicalArray
open WilsonCapturedPrimaryWardSeats WilsonCapturedPrimaryWardRestoration
open WilsonCapturedPrimaryWardThermometer (input)
open WilsonCapturedPrimaryWardEnrolled (Fine)
open MergeProof.Ribbons RG16.Literal WilsonCenteredCompactBooking
open Bandage Stock WilsonReflectedPhysicalRate MergeProof.Ribbons.ManyCopies OPE.Cards


open WilsonNeutralCopiedProgram WilsonNeutralOffsetCutoff WilsonNeutralNominatedFiniteTable
open WilsonMaxwellThermometerNominatedAlgebra WilsonMaxwellThermometerNominatedTrajectory
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
local notation "d₀" => WilsonOriginalThermometerPalette.levels

def reference (A:WilsonPositionThermometerCapStation.Group C 6) (N p:ℕ) (z:Fin 3→Site (R.family.side N p))
    (h:Fin 3→ℝ):Prop:=
   ∀ (caps:Fin 3→ℕ) (w:∀i,d₀ i<caps i) (phase:Fin 3→ℂ→ₗ[ℝ]ℝ) (j:ℕ) (_:j≤N) (s:Finset (Fin 3)),
    let run:=Gears (C).path.levels R.metals.O d₀ d₀ N N j
    let coords:=fun i=>Lattice.lift (z i)
    let full:=top R A N p caps w phase
    let clipped:=top R A N p caps w (fun i=>h i • phase i)
    run clipped coords s=pay h s • run full coords s ∧
      levelsO (run clipped coords) s=pay h s • levelsO (run full coords) s

/-- This is the real weight actually used in the enrolled and owned
physical field. Its complexification is precisely the original share. -/
def shareR {k:ℕ} (y:Palette R.family k):ℝ:=(WilsonThermometerMarchSource.charge y)⁻¹

def paired (Z:Group R.family 6) (N p:ℕ) (o:Fin 3→Site ((C).side N p))
    (y:∀i:Fin 3,Palette C (armGrade i).val) (fees:Fin 3→ℝ):Prop:=
  let h:=fun i=>shareR (y i)
  (∀i,(h i:ℂ)=WilsonCapturedPrimaryWardAppointment.share R (fun i:Fin 3=>(armGrade i).val) y i) ∧
  (∀s:Finset (Fin 3),0<WilsonMaxwellThermometerNominatedAlgebra.pay h s ∧
    (WilsonMaxwellThermometerNominatedAlgebra.pay h s)⁻¹≤∏i∈s,max 1 (fees i)) ∧
    reference (R:=R) Z N p o h

theorem prices (simple:G.Simple) (Z:Group R.family 6) (N p:ℕ) (o:Fin 3→Site ((C).side N p))
    (y:∀i:Fin 3,Palette C (armGrade i).val) (fees:Fin 3→ℝ) (bounded:∀i,size (y i)≤fees i):
    paired Z N p o y fees:=by
  let h:=fun i=>shareR (y i)
  refine ⟨fun i=>?_,fun s=>?_,?_⟩
  · simp only [shareR,WilsonCapturedPrimaryWardAppointment.share,Complex.ofReal_inv]
  · change 0<∏i∈s,h i ∧ (∏i∈s,h i)⁻¹≤_
    refine ⟨Finset.prod_pos (fun i _=>inv_pos.mpr (WilsonThermometerMarchSource.charged (y i))),?_⟩
    rw [←Finset.prod_inv_distrib]
    apply Finset.prod_le_prod
    · exact fun i _=>(inv_pos.mpr (inv_pos.mpr (WilsonThermometerMarchSource.charged (y i)))).le
    · intro i _
      change ((WilsonThermometerMarchSource.charge (y i))⁻¹)⁻¹≤_
      rw [inv_inv]
      exact max_le_max le_rfl (bounded i)
  · intro caps w phase j hn s
    exact WilsonMaxwellThermometerNominatedPupils.fitted R Z N p caps w phase h simple hn _ s

include M V₀ W b house
theorem original (simple:G.Simple) (panels:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (rules:Rules G) (warehouse:Warehouse G)
    (prescribed:Book (f:=f) (l:=l) (H:=H) A P) (lead:Leading F P)
    (book:OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
    (slow:WilsonWindowReportingPace.Slow R.kit) (v h j u:ℕ) (wide:4<v) (enlarged:R.family.ref h ≤ j)
    (station:∀p,Opened R.family h u p) (tiling:Stock.Tabs.opens R.family.path.levels 1 j u)
    (φ:Test 3) (μ ε:ℝ) (ep:0<ε):
    ∃t:ℕ,9 ≤ t ∧ ∃K:ℝ,1 ≤ K ∧ ∃E:ℝ,0 ≤ E ∧ ∀ᶠ r:ℝ in trail,let m:=capture R r
      let k:=launch R simple v r
      let Z:=adjusted F P V A r
      let d:=fun i:Fin 3=>(armGrade i).val
      ∃(um:u ≤ m) (mk:m+1<k),∀ᶠ N:ℕ in atTop,∃kn:k<N,∀p (o:Fin 3→Site (R.family.side N p)),
        WilsonCenteredCompactBooking.mass R φ r (N,p) o ≠ 0 →
        let loc:=WilsonCapturedPrimaryPhysicalArray.registered o (some (0:Fin 3))
        ∃S:Shelf (N:=N) (p:=p) R k d loc,
          let un:=um.trans (m.le_succ.trans (mk.le.trans kn.le))
          let w:=K*r^((h:ℝ)+1/32)
          S.serves kn.le un j (station p) w ∧ let x:=input R Z (N,p) Finset.univ
          let fees:=fun i:Fin 3=>(E*(2*(Lev).clock.hatBeta k)^ε)*WilsonThermometerMarchReference.fee R.family Finset.univ i
          ∃y:(i:Fin 3)→Palette R.family (d i),WilsonCapturedPrimaryNamedReturn.primary R (p:=p) d S.route kn.le x y ∧
            Fine t S kn.le x y ∧ WilsonCapturedPrimaryWardOwnedIntake.Owned R d loc S y t x ∧ (∀i,size (y i) ≤ fees i) ∧ paired Z N p loc y fees ∧ ∀s:Finset (Fin 3),
              let Y:=filed R d x s loc
              let c:=WilsonMacroscopicRichChildRegistration.returned R.family R.makes (station p) un Y
              Booked R.family N p h Y u un ∧ PaidAt R.family.S N p j (R.family.beta N p)
                (((∏i∈s,(1+fees i))*2^(3-s.card))*w) (Y-R.family.O N p c 0):=by
  obtain ⟨t,dt,K,one,E,nonneg,events⟩:=
    WilsonCapturedPrimaryWardPaidSource.original M V₀ W b house F P V A simple panels shop rules warehouse
      prescribed lead book slow v h j u wide enlarged station tiling φ μ ε ep
  refine ⟨t,dt,K,one,E,nonneg,?_⟩
  filter_upwards [events] with ρ campaign
  obtain ⟨um,mk,output⟩:=campaign
  refine ⟨um,mk,?_⟩
  filter_upwards [output] with N grant
  obtain ⟨late,all⟩:=grant
  refine ⟨late,?_⟩
  intro p o live loc
  obtain ⟨S,serves,arms⟩:=all p o live
  obtain ⟨y,hit,fine,owned,wallet,files⟩:=arms Finset.univ
  exact ⟨S,serves,y,hit,fine,owned,wallet,prices simple _ _ _ _ y _ wallet,files⟩

end YM.Integration.WilsonMaxwellThermometerNominatedWard
