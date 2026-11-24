import YM.Integration.WilsonOriginalTwoFlatPublicNativeFee
import YM.Integration.WilsonReflectedPublicTrialTuition

/-! Source fee for the literal public pooled and weak arms at every later stage. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicNamedTrialCapital
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open Next.Rank Next.Rank.Station MergeProof.East Next.UVStress
open Trace.Terrace Trace.Pilot
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open scoped Topology Classical

open WilsonInvariantActionPosition WilsonReflectedOriginalPrefixTariff
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) {l:Ultrafilter (ℕ×ℕ)} {z:Trace.Terrace.Arch R.family}
    {H:(Bel R.family.book).Hierarchy}
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta

open Function Filter Set Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land
open WilsonPositionHomogeneousFrame
open WilsonThermometerUnitFilingFourPoolShell WilsonThermometerUnitFilingFourPoolClock
open scoped Classical Topology BigOperators
open GapsContact GapsContact.Seams
open Function Filter Set MeasureTheory Analysis Table Extraction Lattice RG Wilson
open Labels Source Push Extra.Histories Bid Spec Ascent Power Stamps
open Trace Trace.Verse Trace.Terrace Trace.Pilot Trace.Over MergeProof.East Further.CorrectedLift
open Next.Rank.Price Next.Rank Next.Rank.East Next.Rank.Station Ward Climb OPE OPE.Levy
open scoped Topology InnerProductSpace BigOperators ContDiff NNReal Matrix.Norms.Frobenius Classical
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonOriginalTwoFlatPublicFare (charge)
variable (J:ℝ→tower S)(Z:WilsonPrescription G)
local notation "C" => R.family



open WilsonReflectedFundedHearing WilsonReflectedFullPanel

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F J)
    (obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (slow:WilsonWindowReportingPace.Slow R.kit)(width:∀i,((P).budget i).supportExponent ≤ 100)
    (D d T q:ℕ)(cap:d ≤ D)(y:(Spin.comparator R.family.book).Field d)(x:RG17.Free C d):
    ∃B:ℝ,0<B ∧ ∃power:ℕ,∀ᶠ r in trail,∀{k:ℕ}
      {stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T)}
      {W:Vane R.family k}{fits:D ≤ k}{U:Spin.change S d}
      (pair:Pair F stock cap W fits U r),W.checked f H k→W.wheel.r=r→
    let m:=max stock.j W.k
    let birth:=WilsonInvariantActionPosition.berth R 5 m
    let K:=WilsonInvariantActionPosition.berth R (WilsonReflectedOpticalRate.depth (q+1+2) (2*T+9) D) birth
    ∀b:Bool,let j:=station F pair b
      let v:=WilsonOriginalTwoFlatPublicNamedFare.chosen F J Z r U b y x
      ∃head:j ≤ K,∀N p (high:K ≤ N)(M:(C).label d≃ₗ[ℂ](C).label d)(jets:ℕ),
      let Y:=(pair.arm b v).source (N,p)
      receipt R d j K N p jets head high (1/32) M Y (a j^d*fee F pair b v) →
      ∀A:Arm R d N p birth K,A.w=M.symm (WilsonOriginalMicroscopicGuardedPage.full R d N p j Y) →
      ∀dose:ℂ,‖dose‖ ≤ 1 →
      ((C).labels.level d).coeffSize
        ((dose*(((a K:ℂ)^d)⁻¹)) • WilsonReflectedPublicGuardedMotion.coords R A) ≤ B*(β K)^power :=by
  obtain ⟨C₁,pos,coupon⟩:=WilsonReflectedPublicTrialTuition.original F simple bliss slow width D d T q cap
  obtain ⟨C₂,e,paid,income⟩:=WilsonOriginalTwoFlatPublicNativeFee.original F J Z simple bliss lead obedient d T y x
  let expo:=WilsonReflectedPublicTrialCalendar.span D T q*(d+1)+2
  have pos₂:0<C₂:=lt_of_lt_of_le (by norm_num:(0:ℝ)<1) paid
  refine ⟨C₁*C₂,mul_pos pos pos₂,expo+e,?_⟩
  filter_upwards [coupon,income] with r calendar salary k stock W fits U pair checked exactly m birth K b j v
  have mb:m ≤ birth:=(WilsonInvariantActionPosition.arrival R 5 m).1.le
  have bK:birth ≤ K:=(WilsonInvariantActionPosition.arrival R _ birth).1.le
  obtain ⟨before,all⟩:=calendar pair checked exactly b
  refine ⟨before,?_⟩
  intro N p high M jets Y receipt A enrolled dose small
  have bill:=all N p high v M jets receipt A enrolled dose small
  have src:=salary pair checked exactly birth mb b
  have ht:0 ≤ β birth:=le_of_lt (lt_of_lt_of_le (by norm_num:(0:ℝ)<1) ((P).fits.delayed birth).le)
  have mono:β birth ≤ β K:=WilsonReflectedOpticalStock.monotone R simple bK
  rw [Extra.Histories.Size.smul]
  refine bill.trans ?_
  calc
    _ ≤ C₁*(β birth)^expo*(C₂*(β birth)^e) :=
      mul_le_mul_of_nonneg_left src (mul_nonneg pos.le (pow_nonneg ht _))
    _ = (C₁*C₂)*(β birth)^(expo+e):=by rw [pow_add];ring
    _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht mono _) (mul_nonneg pos.le pos₂.le)

end YM.Integration.WilsonReflectedPublicNamedTrialCapital
end
