import YM.Integration.WilsonMaxwellThermometerNominatedGroundCell
import YM.Integration.WilsonCapturedPrimaryWardPaidCompact

/-! The fixed scalar filed from the complete Wilson cylinder, using the exact
within-cell Maxwell weights and the native prior at every admitted cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedGroundCredit
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

include M V₀ W b house
theorem original (simple:G.Simple) (panels:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (rules:Rules G) (warehouse:Warehouse G)
    (prescribed:Book (f:=f) (l:=l) (H:=H) A P) (lead:Leading F P)
    (book:OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
    (slow:WilsonWindowReportingPace.Slow R.kit) (v j u:ℕ) (wide:4<v) (enlarged:R.family.ref 0 ≤ j)
    (station:∀p,Opened R.family 0 u p) (tiling:Stock.Tabs.opens R.family.path.levels 1 j u)
    (φ:Test 3) (μ:ℝ):
    ∃ψ:Test 3,∃B:ℝ,1≤B ∧ (∀x:Points 3,ψ x=(‖ψ x‖:ℂ) ∧ ‖φ x‖≤‖ψ x‖) ∧
    ∃K:ℝ,1 ≤ K ∧ ∃E:ℝ,0 ≤ E ∧ ∀ᶠ r:ℝ in trail,let m:=capture R r
      let k:=launch R simple v r
      let Z:=adjusted F P V A r
      let d:=fun i:Fin 3=>(armGrade i).val
      ∃(um:u ≤ m) (mk:m+1<k),∀ᶠ N:ℕ in atTop,∃kn:k<N,∀(p:ℕ) (τ:Badge),
        let x:=input R Z (N,p) τ
        let un:=um.trans (m.le_succ.trans (mk.le.trans kn.le))
        let field:=fun (o:Fin 3→Site (R.family.side N p)) (s:Finset (Fin 3))=>
          WilsonCapturedPrimaryWardRestoration.filed R d x s (WilsonCapturedPrimaryPhysicalArray.registered o (some (0:Fin 3)))
        let returned:=WilsonMacroscopicRichChildRegistration.returned R.family R.makes (station p) un
        let χ:=WilsonCenteredCompactBooking.site R r (N,p)
        let c:=fun o (s:Finset (Fin 3))=>WilsonMaxwellThermometerNominatedGroundWeights.ratio R φ ψ χ o
          (WilsonMaxwellThermometerNominatedGroundCell.mode s)
        let size:=WilsonCenteredCompactBooking.mass R ψ r (N,p)
        let submitted:=∑o,size o • (∑s,c o s • field o s)
        (∀U,submitted U=φ.applyTo (fun t=>∑s:Finset (Fin 3),
          WilsonThermometerCenteredAlgebra.weight (WilsonMaxwellThermometerNominatedGroundPurse.policy R t)
            (WilsonMaxwellThermometerNominatedGroundCell.mode s)*field (χ t) s U)) ∧
        Booked R.family N p 0 submitted u un ∧
        returned submitted=∑o,size o • (∑s,c o s • returned (field o s)) ∧
        PaidAt R.family.S N p j (R.family.beta N p)
          ((∫z,‖ψ z‖)*(64*B*K*(WilsonCapturedPrimaryWardSubpower.constant E (WilsonThermometerMarchReference.fee R.family τ))^3*r^((1:ℝ)/64)))
          (submitted-R.family.O N p (returned submitted) 0):=by
  obtain ⟨ψ,B,one,cover,weights⟩:=WilsonMaxwellThermometerNominatedGroundCell.actual R φ
  obtain ⟨K,ke,E,eh,events⟩:=WilsonCapturedPrimaryWardPaidCompact.original M V₀ W b house F P V A simple panels shop rules warehouse prescribed lead book slow v 0 j u wide enlarged station tiling ψ μ 0
  refine ⟨ψ,B,one,cover,K,ke,E,eh,?_⟩
  filter_upwards [events] with r atRadius
  obtain ⟨um,mk,cut⟩:=atRadius
  refine ⟨um,mk,?_⟩
  filter_upwards [cut] with N here
  obtain ⟨kn,booked⟩:=here
  refine ⟨kn,fun p τ=>?_⟩
  let c:=fun (o:Fin 3→Site (R.family.side N p)) (s:Finset (Fin 3))=>
    WilsonMaxwellThermometerNominatedGroundWeights.ratio R φ ψ (WilsonCenteredCompactBooking.site R r (N,p)) o
      (WilsonMaxwellThermometerNominatedGroundCell.mode s)
  have a:=weights r (N,p)
  have paid:=booked p τ c (8*B) (by linarith) (fun o _=>by simpa only [pow_zero,mul_one] using a.1 o)
  refine ⟨fun U=>?_,paid.1,paid.2.1,?_⟩
  · let d:=fun i:Fin 3=>(armGrade i).val
    let x:=input R (adjusted F P V A r) (N,p) τ
    have fixed:=a.2 (fun o s=>WilsonCapturedPrimaryWardRestoration.filed R d x s
      (WilsonCapturedPrimaryPhysicalArray.registered o (some (0:Fin 3))) U)
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using fixed.symm
  · simpa only [Nat.cast_zero,zero_add,show (8:ℝ)*(8*B)=64*B by ring] using paid.2.2

end YM.Integration.WilsonMaxwellThermometerNominatedGroundCredit
