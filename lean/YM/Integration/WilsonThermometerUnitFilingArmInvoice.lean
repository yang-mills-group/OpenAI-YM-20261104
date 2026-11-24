import YM.Integration.WilsonThermometerUnitFilingReflectionBank
import YM.Integration.WilsonThermometerUnitFilingArmPrice

/-! Restoring the issued inverse at the actual primary lifts of the reflected chamber. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingArmInvoice
open Function Filter MeasureTheory Extraction Lattice Wilson Labels RG Source Extra.Histories
open Push Marker Extra.Multi PhysicalNext.Repeat.Legato MergeProof Accent
open Bid Bandage Cells Stock RG16.Literal Trace.Physical.GermGraph GridApprox
open Motion Menu Ribbons Ribbons.ManyCopies Next.Rank Ribbon Trace.Physical
open RG05Readout Native Address Many Records Harvest Copper PhysMS
open WilsonReflectedMicroscopicSites WilsonReflectedPhysicalRate OPE OPE.Log Trace.Pilot
open WilsonPositionThermometerCapStation WilsonThermometerCourseIntake
open WilsonPositionThermometerGradedSource (grade)
open WilsonPositionThermometerGradedReading (vector)
open WilsonCapturedPrimaryFaceWallet WilsonCapturedPrimaryActiveArms
open OPE.Cards XSpace XSpace.Normalize XSpace.Rose
open Table Spec Climb Next.UVStress RG12 RG17
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "C" => R.family
local notation "origin" z:max ax:max => WilsonCapturedPrimaryPhysicalArray.registered z (some ax)

local notation "dims" => WilsonCapturedPrimaryStationArms.height

open WilsonCapturedPrimaryStationArms (nominees)
open WilsonThermometerUnitFilingCylinder WilsonThermometerUnitFilingFeed
open WilsonThermometerUnitFilingReflectedShape (Key tariff)
open scoped Classical BigOperators

open WilsonThermometerUnitFilingRelative (Grid)
open WilsonThermometerAlignedCells (placedAt atOrigin mass)
open Next.UVStress OPE.Cards
local notation "J₃" => Stock.census (Fin 3)
local notation "site!" z:max c:max => (WilsonThermometerRegisteredCells.placement (R:=R) z (c).val).origin

open Primitives.GCC.Anchor
open WilsonThermometerUnitFilingReflectionBank (lifts)
open WilsonThermometerUnitFilingRelativeStation (rent)

def seats {N p:ℕ} {r:ℝ} {φ:Test 3} (y:lifts (N:=N) (p:=p) R r φ)
    (c:Grid R (N,p) r φ) (s:(J₃).Mode):ℝ:=
  (∏ i ∈ s.val, (1+size (y c s i)))*2^(3-s.val.card)

theorem original {N p:ℕ} (r K:ℝ) (φ:Test 3) (Q:Grid R (N,p) r φ→Poly J₃)
    (y:lifts (N:=N) (p:=p) R r φ) (w:Grid R (N,p) r φ→Fin 3→ℝ)
    {g M:ℝ} (gp:0<g) (small:g≤1) (nonneg:0≤K) (radius:0≤r)
    (loss:ℕ) (positive:∀c a,0<w c a) (joint:∀c,g^loss≤Poly.toll (w c) (WilsonThermometerCenteredAlgebra.full))
    (inverse:∀c,Poly.price (fun a=>g*w c a) (inverseMass (Q c))≤WilsonFiniteOrdinaryInverse.fee J₃)
    (mp:0≤M) (earned:∀c s,Poly.toll (w c) s*seats R y c s≤M):
    rent R r K φ Q y ≤
      ((∫x:Points 3,‖φ x‖)*(WilsonFiniteOrdinaryInverse.fee J₃/g^(3+loss))*M)*(K*r^(1/32:ℝ)):=by
  have bound:=WilsonThermometerUnitFilingArmPrice.original R (N,p) r φ Q w positive gp small
    loss joint inverse (seats R y) mp earned
  calc rent R r K φ Q y = (∑c:Grid R (N,p) r φ,∑s:(J₃).Mode,
      ‖WilsonThermometerAlignedCells.mass (R:=R) r (N,p) φ c.val*WilsonThermometerUnitFilingCylinder.wallet (Q c) s‖ * seats R y c s)*
      (K*r^(1/32:ℝ)):=by simp only [rent,seats,Finset.sum_mul,Finset.sum_product,mul_assoc]
    _≤_:=mul_le_mul_of_nonneg_right bound (mul_nonneg nonneg (Real.rpow_nonneg radius _))

end YM.Integration.WilsonThermometerUnitFilingArmInvoice
