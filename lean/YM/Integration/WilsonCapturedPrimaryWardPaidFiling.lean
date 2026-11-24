import YM.Integration.WilsonCapturedPrimaryWardPaidThermometer
import YM.Integration.WilsonCapturedPrimaryWardEnrolled

/-! Fund all proper faces and their fixed-date counterterms on the true supported Wilson cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardPaidFiling
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
          S.serves kn.le un j (station p) w ∧ ∀τ:Badge,let x:=input R Z (N,p) τ
          let fees:=fun i:Fin 3=>(E*(2*(Lev).clock.hatBeta k)^ε)*WilsonThermometerMarchReference.fee R.family τ i
          ∃y:(i:Fin 3)→Palette R.family (d i),WilsonCapturedPrimaryNamedReturn.primary R (p:=p) d S.route kn.le x y ∧
            Fine t S kn.le x y ∧ (∀i,size (y i) ≤ fees i) ∧ ∀s:Finset (Fin 3),
              let Y:=filed R d x s loc
              let c:=WilsonMacroscopicRichChildRegistration.returned R.family R.makes (station p) un Y
              Booked R.family N p h Y u un ∧ PaidAt R.family.S N p j (R.family.beta N p)
                (((∏i∈s,(1+fees i))*2^(3-s.card))*w) (Y-R.family.O N p c 0):=by
  let d:=fun i:Fin 3=>(armGrade i).val
  have cap(i:Fin 3):d i ≤ 6:=Nat.le_of_lt_succ (armGrade i).isLt
  obtain ⟨K,one,funds⟩:=WilsonCapturedPrimaryActiveArms.original R simple book shop slow 6 v h j u wide enlarged station tiling φ d cap
  obtain ⟨t,dt,appointments⟩:=WilsonCapturedPrimaryWardAppointment.original R simple shop 6
  obtain ⟨E,nonneg,measured⟩:=WilsonCapturedPrimaryWardPaidThermometer.original M V₀ W b house F P V A simple panels shop rules warehouse prescribed lead v (by omega) μ ε ep
  refine ⟨t,dt,K,one,E,nonneg,?_⟩
  have separate:=WilsonCapturedPrimaryWardSeats.separation R simple slow v wide φ
  have go:=WilsonMeasuredWindow.stop_tendsto (Lev) simple v (by omega)
  filter_upwards [funds,go.eventually appointments,separate,measured,
      show ∀ᶠ r:ℝ in trail,0<r from self_mem_nhdsWithin] with r current enroll apart sale positive
  obtain ⟨um,mk,arms⟩:=current
  obtain ⟨dated,panel⟩:=sale
  refine ⟨um,mk,?_⟩
  filter_upwards [panel] with N purchase
  obtain ⟨later,sold⟩:=purchase
  let kn:=lt_of_le_of_lt dated later
  refine ⟨kn,?_⟩
  intro per o supported loc
  obtain ⟨S,serves⟩:=arms N per kn o supported 0
  refine ⟨S,serves,?_⟩
  intro τ x fees
  have zero:loc 0=0:=by simp [loc,WilsonCapturedPrimaryPhysicalArray.registered]
  obtain ⟨y,exact⟩:=sold per loc S.viewer S.route zero S.receipt τ
  have hit:WilsonCapturedPrimaryNamedReturn.primary R (p:=per) d S.route kn.le x y:=by
    intro i
    have nz:((R.family.S.a (launch R simple v r):ℂ)^(d i))≠0:=
      pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos _).ne')
    have same:((R.family.S.a (launch R simple v r):ℂ)^(d i)) •
        (R.family.factory (d i) N per).terminal (finer (S.route i) kn.le (y i) (primaryLetter (d i)))=x i:=(exact i).1
    rw [←same]
    exact (inv_smul_smul₀ nz _).symm
  have bounds(i:Fin 3):size (y i) ≤ fees i:=(exact i).2
  have fine:=enroll N per kn.le 3 d cap loc (apart N per kn.le o supported 0) S (Stock.census (Fin 3)) x y hit
  refine ⟨y,hit,fine,bounds,?_⟩
  intro s
  obtain ⟨booked,paid⟩:=serves s x (WilsonCapturedPrimaryWardSeats.filled S kn.le y s)
    (WilsonCapturedPrimaryWardSeats.legal S kn.le x y hit s)
  rw [WilsonCapturedPrimaryWardSeats.occupied_size] at paid
  refine ⟨booked,⟨paid.live,paid.ticket,paid.mark.trans ?_⟩⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Finset.prod_le_prod (fun i _=>by linarith [size_ge (y i)]) (fun i _=>by linarith [bounds i])

end YM.Integration.WilsonCapturedPrimaryWardPaidFiling
