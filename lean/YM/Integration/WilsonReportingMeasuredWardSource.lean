import YM.Integration.WilsonReportingMeasuredWardFees

/-! The complete prescribed curvature source at its measuring date, including its scalar part. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingMeasuredWardSource

open Function Finset Lattice RG Wilson Precision Source
open PhysicalNext.Repeat.Legato MS MS.Land MS.Menus MS.Local.Physical MS.Theater
open WilsonReportingPrescribedOldFreeArms WilsonReportingPrescribedOldWardWallet
open WilsonReportingPrescribedOldWardTree WilsonReportingMeasuredWardFees
open WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalIndependentFields WilsonMatrixOriginalCurvatureField
open private fee registered from YM.Integration.WilsonMatrixOriginalCurvatureField
open scoped Classical BigOperators

variable {G:Gauge} {B:Deck G} (R:Run G) (Q:Prescription B)
local notation "I" => B.BIndex (4:ℤ) 2

/-- This scalar is evaluated on the identity configuration, before choosing a torus or a site. -/
def scalar (z:Stock B) (clock:ℝ) (k:ℕ):ℂ :=
  operand R Q z clock k 1 0 1 - stencil R (projected Q clock k z) 1 0 1

private theorem unchanged (z:Stock B) (clock:ℝ) (k:ℕ) (n:Side) (o:Site n):
    operand R Q z clock k n o 1=operand R Q z clock k 1 0 1 := by
  unfold operand
  congr 1
  apply sum_congr rfl
  intro i _
  rw [ActualOriginalCalibratedColumns.weighted_observable_original,
    ActualOriginalCalibratedColumns.weighted_observable_original]
  rfl

private theorem unshifted (z:Stock B) (n:Side) (o:Site n):stencil R z n o 1=stencil R z 1 0 1 := by
  unfold stencil
  apply sum_congr rfl
  intro i _
  rw [ActualOriginalDictionary.original_section,ActualOriginalDictionary.original_section]
  rfl

theorem split (simple:G.Simple) (z:Stock B) (clock:ℝ) (k:ℕ) (n:Side) (o:Site n) (U:Config G n):
    operand R Q z clock k n o U=scalar R Q z clock k+stencil R (projected Q clock k z) n o U := by
  have h:=centered R Q simple z clock k n o U 1
  rw [unchanged R Q z clock k n o,unshifted R (projected Q clock k z) n o] at h
  unfold scalar
  linear_combination h

def coordinates (z:Stock B):R.family.label 4:=∑i:I,z.2 i • (warehouse R).fits B 4 2 i

/-- The actual finite input in the original family. The two terms are booked in their native units. -/
def submitted (m per:ℕ) (z:Stock B) (clock:ℝ) (k:ℕ):R.family.label 4 :=
  scalar R Q z clock k • R.family.refUnit 4+
    (normalization R m)⁻¹ • (R.family.factory 4 m per).terminal (coordinates R (projected Q clock k z))

theorem original (simple:G.Simple) (m per:ℕ) (age:R.family.ref 4 ≤ m)
    (z:Stock B) (clock:ℝ) (k:ℕ) (o:Site (R.family.side m per)) (U:Config G (R.family.side m per)):
    R.family.O m per (submitted R Q m per z clock k) o U=operand R Q z clock k _ o U := by
  let A:=(R.family.linearO m per 4 o).mk' _
  let s:=scalar R Q z clock k
  let x:=projected Q clock k z
  have ht:(R.family.path.levels.clock.threshold m)≠0:=(R.family.path.levels.budget m).threshold_pos.ne'
  have hp:normalization R m≠0:=mul_ne_zero
    (inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos m).ne')))
    (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (inv_ne_zero ht)))
  have hx: R.family.O m per ((R.family.factory 4 m per).terminal (coordinates R x)) o U=
      normalization R m*stencil R x _ o U := by
    change detector R m per o U ((R.family.factory 4 m per).terminal.symm
      ((R.family.factory 4 m per).terminal (coordinates R x)))=_
    rw [LinearEquiv.symm_apply_apply]
    unfold coordinates stencil
    rw [map_sum,mul_sum]
    apply sum_congr rfl
    intro i _
    exact ((detector R m per o U).map_smul (x.2 i) ((warehouse R).fits B 4 2 i)).trans
      ((congrArg (fun c:ℂ=>x.2 i*c) (fee R B m per o U i)).trans (mul_left_comm ..))
  rw [split R Q simple z clock k _ o U]
  change A (s • R.family.refUnit 4 +
    (normalization R m)⁻¹ • (R.family.factory 4 m per).terminal (coordinates R x)) U=s+stencil R x _ o U
  rw [map_add,map_smul,map_smul]
  change s*R.family.O m per (R.family.refUnit 4) o U+
    (normalization R m)⁻¹*R.family.O m per ((R.family.factory 4 m per).terminal (coordinates R x)) o U=_
  rw [R.family.constant R.makes 4 age o,hx,inv_mul_cancel_left₀ hp]
  simp

end YM.Integration.WilsonReportingMeasuredWardSource
