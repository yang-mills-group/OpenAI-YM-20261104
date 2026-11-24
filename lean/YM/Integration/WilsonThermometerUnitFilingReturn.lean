import YM.Integration.WilsonThermometerCourseIntake
import YM.RG16.Unmasked.Report

/-! The full normalized older return of every slot of the intrinsic
thermometer, on the original stored Wilson prior at any intervening date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingReturn

open Filter Function Set MeasureTheory Table Spec Lattice Wilson RG Source Marker Extraction Climb Trace.Pilot
open Next.UVStress Next.Rank RG12 RG17 PhysMS PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.East
open FVA1 OriginalForcedAddresses XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open RG16.Literal WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple)
local notation "C" => R.family


private theorem scalar_push (N p : ℕ) {j i : ℕ} (hi : i≤j) (Y : Config G (R.family.side j p) → ℂ) :
    gust R.family.path N p j Y i hi = pushTo R.family.path N p hi Y := by
  induction hi using Nat.decreasingInduction with
  | self => rw [gust_base,pushTo_self]
  | of_succ i hi ih => rw [gust_step R.family.path N p j Y hi,Birth.push_first R.family.path N p hi,ih]

private theorem smooth (z : UVIndex) (o : Fin 3 → Site (R.family.side z.1 z.2)) (s : Badge) :
    Continuous (placed R A z s o) := by
  apply continuous_finsetProd
  intro i _
  exact R.family.continuousO z.1 z.2 _ _ _

def reading {N p k : ℕ} (upper : k≤N) (o : Positions (Fin 3) (R.family.side N p)) (s : (Stock.census (Fin 3)).Mode) : ℂ :=
  (∫ U, (incoming R A simple upper o U).part s ∂prior G (R.family.side k p)) /
    (∫ U, ((R.family.path.rep N p k).eval U : ℂ) ∂prior G (R.family.side k p))

include simple in
/-- On the seven complete faces, including every cutoff placement, the earlier
stored Wilson density is exactly the numerator credited to that face at the same date. -/
theorem density {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t) = (Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ k (upper : k≤z.1)
      (o : Positions (Fin 3) (R.family.side z.1 z.2)) (s : (Stock.census (Fin 3)).Mode),
      (fun U => (incoming R A simple upper o U).part s) =
        credit C z.1 z.2 0 (placed R A z s.val o.origin) k upper := by
  filter_upwards [WilsonThermometerCourseIntake.original R A simple checked unit] with z hearing k upper o s
  funext U
  rw [hearing k upper o s U,actualTransport_unnormalize C R.makes le_rfl,scalar_push]
  have top (W : Config G (R.family.side z.1 z.2)) : (R.family.path.rep z.1 z.2 z.1).eval W = bare (R.family.beta z.1 z.2) W := congrFun (R.makes.wilson.starts z.1 z.2).2 W
  simp only [credit,pow_zero,one_smul,top,Complex.real_smul]

include simple in
theorem original {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t) = (Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, ∀ k (upper : k≤z.1)
      (o : Positions (Fin 3) (R.family.side z.1 z.2)) (s : (Stock.census (Fin 3)).Mode),
      reading R A simple upper o s =
        row A z o.origin s.val := by
  filter_upwards [density R A simple checked unit] with z held k upper o s
  change (∫ U, (fun W => (incoming R A simple upper o W).part s) U ∂prior G (R.family.side k z.2)) / _ = _
  rw [held k upper o s]
  rw [credit_moment C z.1 z.2 0 R.makes _ (smooth R A z o.origin s.val) upper,pow_zero,one_mul]
  have denom : (∫ U, ((R.family.path.rep z.1 z.2 k).eval U : ℂ) ∂prior G (R.family.side k z.2)) ≠ 0 := by
    have mass : (∫ U, ((R.family.path.rep z.1 z.2 k).eval U : ℂ) ∂prior G (R.family.side k z.2)) =
        (partition G (R.family.side z.1 z.2) (R.family.beta z.1 z.2) : ℂ) :=
      (integral_ofReal ..).trans (congrArg Complex.ofReal (History.partition_eq R.family.path R.makes.wilson z.1 z.2 k upper))
    exact mass ▸ Complex.ofReal_ne_zero.mpr (partition_pos _).ne'
  rw [mul_div_cancel_left₀ _ denom]
  rfl

end YM.Integration.WilsonThermometerUnitFilingReturn
