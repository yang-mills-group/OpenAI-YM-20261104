import YM.Integration.WilsonAddressedHomeDose

/-! The native before-position source fare already repays the complete dose on a homogeneous public field. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixRawDose
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

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "meshSize" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open MS MS.Land FVA2 FVA2.Register


open WilsonOriginalTwoFlatPublicNamedFare (chosen)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)



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
set_option warningAsError true
set_option maxHeartbeats 850000

open WilsonAddressedHomeDose (ceiling)

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem original {D T:ℕ}(d:I → Fin (D+1))(x:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(r:{r:ℝ // 0<r ∧ r<δ}) → WilsonOriginalTwoFlatPublicBooks.Book F (l:=l) H z D T r.val)
    (ρ:I → {r:ℝ // 0<r ∧ r<δ})(M:I → ℝ)(E:I → ℕ)(one:∀i,1 ≤ M i)
    (f N per:ℕ)(deep:f<N)(ref:∀e ≤ D,(C).ref e ≤ N)
    (homes:∀i b,WilsonReflectedPublicStationFare.station F ((books (ρ i)).rows (d i)) b ≤ f)
    (fare:∀i b,let v:=homogeneous F Jr Z (ρ i).val (d i).val (x i)
      WilsonOriginalTwoFlatPublicFare.charge F ((books (ρ i)).rows (d i)) f b v ≤ M i*(β f)^(E i))
    (V:(e:Fin (D+1)) → Sight C e.val per)(u:(e:Fin (D+1)) → Emblems C e.val)
    (est:∀e:Fin (D+1),Opened C e.val f per)
    (enrolled:∀e,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N per e.val
      (digits R N per 0) (V e) (u e))
    {J:Type}[DecidableEq J](pick:J → I)(branch:J → Bool)(s:Finset J):
    let v:=fun i=>homogeneous F Jr Z (ρ i).val (d i).val (x i)
    let raw:=fun j=>(((books (ρ (pick j))).rows (d (pick j))).arm (branch j) (v (pick j))).source (N,per)
    let χ:=fun j=>WilsonThermometerMarchSource.charge (offer R (raw j) (est (d (pick j))) deep.le)
    let c:=fun a=>dose (χ a) (rent R (d (pick a)).val (M (pick a))) 1
    ∀q:ℕ,∀err:ℂ,‖err‖≤(∏a∈s,‖(c a:ℂ)‖)⁻¹*((β f)^(q+∑a∈s,E (pick a)))⁻¹ →
    ‖err‖≤
      (∏a∈s,ceiling (R:=R) (d (pick a)).val (M (pick a)))*((β f)^q)⁻¹:=by
  classical
  intro v raw χ c q err paid
  let e:=∑a∈s,E (pick a)
  let bound:=∏a∈s,ceiling (R:=R) (d (pick a)).val (M (pick a))
  have hp:1 ≤ β f:=((P).fits.delayed f).le
  have bounds(j:J):(c j)⁻¹≤ceiling (R:=R) (d (pick j)).val (M (pick j))*(β f)^(E (pick j)):=by
    let i:=pick j
    let L:=(books (ρ i)).rows (d i)
    have original:=WilsonAddressedAlignedColumn.original R (enrolled (d i)) deep.le (le_refl f)
      (fun e he=>ref e (he.trans (Nat.le_of_lt_succ (d i).isLt))) (est (d i)) (raw j)
    have stock:=WilsonOriginalTwoFlatPublicFare.issued F L (books (ρ i)).checked (branch j) (v i)
      (p:=per) (homes i (branch j)) deep
    have salary:size (offer R (raw j) (est (d i)) deep.le) ≤ 2*(M i*(β f)^(E i)) :=
      original.2.trans (mul_le_mul_of_nonneg_left (stock.trans (fare i (branch j))) zero_le_two)
    let bound:=ceiling (R:=R) (d i).val (M i)*(β f)^(E i)
    have base:1 ≤ (β f)^(E i):=one_le_pow₀ hp
    have inCash:2*M i ≤ ceiling (R:=R) (d i).val (M i):=le_max_left .. 
    have positive:1 ≤ ceiling (R:=R) (d i).val (M i):=(show 1 ≤ 2*M i by linarith [one i]).trans inCash
    have small:1 ≤ bound:=one_le_mul_of_one_le_of_one_le positive base
    have booked:χ j ≤ bound:=by
      refine max_le small (salary.trans ?_)
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right inCash (zero_le_one.trans base)
    have rentBound:rent R (d i).val (M i) ≤ bound:=calc
      _ ≤ ceiling (R:=R) (d i).val (M i):=le_max_right ..
      _ ≤ _:=le_mul_of_one_le_right (zero_le_one.trans positive) base
    have denom:WilsonReflectedPublicCommonDose.denominator (χ j) (rent R (d i).val (M i)) 1 ≤ bound:=by
      change max (max 1 (χ j)) (rent R (d i).val (M i)*1) ≤ bound
      exact max_le (max_le small booked) (by simpa only [mul_one] using rentBound)
    simpa only [c,WilsonReflectedPublicCommonDose.refund] using denom
  have coin (a:J):‖(c a:ℂ)‖=c a:=by
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

end YM.Integration.WilsonSeparatedPrefixRawDose
end
