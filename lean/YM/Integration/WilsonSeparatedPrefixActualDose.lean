import YM.Integration.WilsonSeparatedPrefixRawDose

/-! Repay the actual complete source dose at a fixed common physical reporter. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixActualDose
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

open WilsonAddressedMixedStationRange (width)
open WilsonMeasuredPublicEntranceGridDebit (fitted bill settled)
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedPublicSignedFare (amplitude)
open WilsonAddressedPublicGuardFare (word)
open OPE.Therm (Poetry)



open WilsonAddressedMixedEnrolledTrial (Funded)
open WilsonMovingForkWindowBooks (Priced)
open WilsonPositionHomogeneousFrame (homogeneous)

open WilsonReflectedMixedThermalArms (rent)
open WilsonReflectedPublicCommonDose (dose)

open WilsonAddressedHomeDose (ceiling)
variable {G:Gauge}(R:Run G){I:Type}
local notation "C" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta

theorem original (grades:I→ℕ)(M:I→ℝ)(E:I→ℕ)(one:∀i,1≤M i){f N per:ℕ}(deep:f≤N)
    (names:∀i,(C).label (grades i))(home:∀a,Opened (C) (grades a) f per)
    (V:∀a,Sight (C) (grades a) per)(u:∀a,Emblems (C) (grades a))
    (enrolled:∀a,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N per (grades a)
      (digits R N per 0) (V a) (u a))(ref:∀a b,b≤grades a→(C).ref b≤N)
    (fare:∀a,Spindle.paid (C) (grades a) f N per (names a)≤M a*(β f)^(E a))(s:Finset I):
    let χ:=fun a=>WilsonThermometerMarchSource.charge (offer R (names a) (home a) deep)
    let c:=fun a=>dose (χ a) (rent R (grades a) (M a)) 1
    ∀q:ℕ,∀err:ℂ,‖err‖≤(∏a∈s,‖(c a:ℂ)‖)⁻¹*((β f)^(q+∑a∈s,E a))⁻¹ →
    ‖err‖≤(∏a∈s,ceiling (R:=R) (grades a) (M a))*((β f)^q)⁻¹:=by
  classical
  intro χ c q err paid
  let e:=∑a∈s,E a
  let bound:=∏a∈s,ceiling (R:=R) (grades a) (M a)
  have hp:1 ≤ β f:=(R.family.path.levels.fits.delayed f).le
  have bounds(j:I):(c j)⁻¹≤ceiling (R:=R) (grades j) (M j)*(β f)^(E j):=by
    have original:=WilsonAddressedAlignedColumn.original R (enrolled j) deep (le_refl f) (ref j) (home j) (names j)
    have salary:size (offer R (names j) (home j) deep) ≤ 2*(M j*(β f)^(E j)) :=
      original.2.trans (mul_le_mul_of_nonneg_left (fare j) zero_le_two)
    let bound:=ceiling (R:=R) (grades j) (M j)*(β f)^(E j)
    have base:1 ≤ (β f)^(E j):=one_le_pow₀ hp
    have inCash:2*M j ≤ ceiling (R:=R) (grades j) (M j):=le_max_left .. 
    have positive:1 ≤ ceiling (R:=R) (grades j) (M j):=(show 1 ≤ 2*M j by linarith [one j]).trans inCash
    have small:1 ≤ bound:=one_le_mul_of_one_le_of_one_le positive base
    have booked:χ j ≤ bound:=by
      refine max_le small (salary.trans ?_)
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right inCash (zero_le_one.trans base)
    have rentBound:rent R (grades j) (M j) ≤ bound:=calc
      _ ≤ ceiling (R:=R) (grades j) (M j):=le_max_right ..
      _ ≤ _:=le_mul_of_one_le_right (zero_le_one.trans positive) base
    have denom:WilsonReflectedPublicCommonDose.denominator (χ j) (rent R (grades j) (M j)) 1 ≤ bound:=by
      change max (max 1 (χ j)) (rent R (grades j) (M j)*1) ≤ bound
      exact max_le (max_le small booked) (by simpa only [mul_one] using rentBound)
    simpa only [c,WilsonReflectedPublicCommonDose.refund] using denom
  have coin (a:I):‖(c a:ℂ)‖=c a:=by
    rw [Complex.norm_real,Real.norm_of_nonneg (WilsonReflectedPublicCommonDose.positive ..).le]
  have gross:(∏a∈s,‖(c a:ℂ)‖)⁻¹≤bound*(β f)^e:=by
    rw [show (∏a∈s,‖(c a:ℂ)‖)⁻¹ = ∏a∈s,(c a)⁻¹ by simp only [coin,Finset.prod_inv_distrib]]
    dsimp only [bound,e]
    rw [←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun a _=>inv_nonneg.mpr (WilsonReflectedPublicCommonDose.positive ..).le)
      (fun a _=>bounds a)
  calc ‖err‖≤(∏a∈s,‖(c a:ℂ)‖)⁻¹*((β f)^(q+e))⁻¹:=paid
       _≤(bound*(β f)^e)*((β f)^(q+e))⁻¹:=mul_le_mul_of_nonneg_right gross
         (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hp) _))
       _=bound*((β f)^q)⁻¹:=by rw [pow_add];field_simp [(zero_lt_one.trans_le hp).ne']

end YM.Integration.WilsonSeparatedPrefixActualDose
end
