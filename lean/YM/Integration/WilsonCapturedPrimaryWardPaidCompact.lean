import YM.Integration.WilsonCapturedPrimaryWardPaidSparse

/-! The shifted face wages and their exact physical all-age gallery on the genuine original source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardPaidCompact
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
    (φ:Test 3) (μ:ℝ) (q:ℕ):

    ∃K:ℝ,1 ≤ K ∧ ∃E:ℝ,0 ≤ E ∧ ∀ᶠ r:ℝ in trail,let m:=capture R r
      let k:=launch R simple v r
      let Z:=adjusted F P V A r
      let d:=fun i:Fin 3=>(armGrade i).val
      ∃(um:u ≤ m) (mk:m+1<k),∀ᶠ N:ℕ in atTop,∃kn:k<N,∀(p:ℕ) (τ:Badge),
        let x:=input R Z (N,p) τ
        let weight:=WilsonCenteredCompactBooking.mass R φ r (N,p)
        let un:=um.trans (m.le_succ.trans (mk.le.trans kn.le))
        let field:=fun (o:Fin 3→Site (R.family.side N p)) (s:Finset (Fin 3))=>
          WilsonCapturedPrimaryWardRestoration.filed R d x s (WilsonCapturedPrimaryPhysicalArray.registered o (some (0:Fin 3)))
        let returned:=WilsonMacroscopicRichChildRegistration.returned R.family R.makes (station p) un
        ∀(c:(Fin 3→Site (R.family.side N p))→Finset (Fin 3)→ℂ) (B:ℝ),0 ≤ B →
        (∀o,weight o≠0 → (∑s,‖c o s‖) ≤ B*(1+(Lev).clock.hatBeta k)^q) →
        let submitted:=∑o,weight o • (∑s,c o s • field o s)
        Booked R.family N p h submitted u un ∧
        returned submitted=∑o,weight o • (∑s,c o s • returned (field o s)) ∧
        PaidAt R.family.S N p j (R.family.beta N p)
          ((∫z,‖φ z‖)*(8*B*K*(WilsonCapturedPrimaryWardSubpower.constant E (WilsonThermometerMarchReference.fee R.family τ))^3*r^((h:ℝ)+1/64)))
          (submitted-R.family.O N p (returned submitted) 0):=by
  obtain ⟨t,_,K,one,E,nonneg,events⟩:=WilsonCapturedPrimaryWardPaidRate.original M V₀ W b house F P V A simple panels shop rules warehouse prescribed lead book slow v h j u wide enlarged station tiling φ μ q
  refine ⟨K,one,E,nonneg,?_⟩
  filter_upwards [events,self_mem_nhdsWithin] with r campaign pos
  have rp:0<r:=pos
  obtain ⟨um,mk,panel⟩:=campaign
  refine ⟨um,mk,?_⟩
  filter_upwards [panel] with N supply
  obtain ⟨kn,base⟩:=supply
  refine ⟨kn,?_⟩
  intro per τ x weight un field returned c B bp wage submitted
  let row o:=∑s,c o s • field o s
  let cost:=8*B*K*(WilsonCapturedPrimaryWardSubpower.constant E (WilsonThermometerMarchReference.fee R.family τ))^3*r^((h:ℝ)+1/64)
  have nonnegative:0 ≤ WilsonCapturedPrimaryWardSubpower.constant E (WilsonThermometerMarchReference.fee R.family τ):=by
    unfold WilsonCapturedPrimaryWardSubpower.constant;positivity
  have cp:0≤cost:=by dsimp only [cost];positivity
  have cont o:Continuous (row o):=by
    change Continuous (fun U=>(row o) U)
    simp only [row,Finset.sum_apply,Pi.smul_apply]
    apply continuous_finsetSum
    intro s _
    have smooth:Continuous (field o s):=continuous_finsetProd _ fun i _=>R.family.continuousO N per _ _ _
    exact smooth.const_smul (c o s)
  have paid o (nz: weight o≠0):
      Booked R.family N per h (row o) u un ∧ returned (row o)=∑s,c o s • returned (field o s) ∧
      PaidAt R.family.S N per j (R.family.beta N per) cost ((row o)-R.family.O N per (returned (row o)) 0):=by
    obtain ⟨S,_,arms⟩:=base per o nz
    obtain ⟨y,_,_,_,_,faces⟩:=arms τ
    exact faces (c o) B bp (wage o nz)
  have group:=WilsonCapturedPrimaryWardPaidSparse.original R (station per) un (tiling.1.trans un) weight row (fun _=>cost) cont
    (fun o nz=>⟨(paid o nz).1,(paid o nz).2.2⟩)
  refine ⟨group.1,group.2.1.trans (Finset.sum_congr rfl fun o _=>?_ ),group.2.2.live,group.2.2.ticket,group.2.2.mark.trans ?_⟩
  · by_cases nz:weight o=0
    · simp [nz]
    · exact congrArg (fun v=>weight o • v) (paid o nz).2.1
  · rw [←Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (WilsonCenteredCompactBooking.variation R φ r (N,per)) cp

end YM.Integration.WilsonCapturedPrimaryWardPaidCompact
