import YM.Integration.WilsonReportingMeasuredWardSource
import YM.Integration.WilsonMatrixOriginalGermMarket

/-! The full germ of the independently registered operand, at the actual earlier-history temperature. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingMeasuredWardSourceGerm
open Function Finset Lattice RG Wilson Precision Source Labels
open MS.Local.Physical MS.Theater MS.Land PhysicalNext.Repeat.Legato FVA2
open Trace.Physical Trace.Physical.GermGraph Next.Rank.Price
open WilsonReportingPrescribedOldFreeArms WilsonReportingMeasuredWardFees
open WilsonReportingMeasuredWardSource WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalCurvatureField
open scoped BigOperators Classical

variable {G:Gauge} {B:Deck G} (R:Run G) (Q:Prescription B)
local notation "F" => R.family.labels.level 4

def bank (m:ℕ) (z:Stock B) (clock:ℝ) (k:ℕ):R.family.label 4:=
  scalar R Q z clock k • (F).e0+
    ((R.family.path.levels.clock.threshold m^2:ℝ):ℂ) • coordinates R (projected Q clock k z)

theorem frame (m per:ℕ) (age:R.family.ref 4 ≤ m) (z:Stock B) (clock:ℝ) (k:ℕ):
    (R.family.factory 4 m per).terminal.symm (submitted R Q m per z clock k)=
      ((R.family.S.a m:ℂ)^4) • bank R Q m z clock k := by
  let T:=(R.family.factory 4 m per).terminal
  let a:ℂ:=(R.family.S.a m:ℂ)^4
  have ap:a≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos m).ne')
  have unit:T.symm (R.family.refUnit 4)=a • (F).e0:=by
    apply T.injective
    rw [T.apply_symm_apply,T.map_smul,WilsonMatrixOriginalIndependentUnit.original R.family R.makes m per age]
    change _=a • (a⁻¹ • R.family.refUnit 4)
    rw [smul_smul,mul_inv_cancel₀ ap,one_smul]
  have price:(normalization R m)⁻¹=a*((R.family.path.levels.clock.threshold m^2:ℝ):ℂ):=by
    unfold normalization a
    simp only [mul_inv_rev,inv_inv,Complex.ofReal_pow,Complex.ofReal_inv,inv_pow]
    ring
  unfold submitted bank
  change T.symm (_ • R.family.refUnit 4+_ • T _)=a • _
  rw [map_add,T.symm.map_smul,T.symm.map_smul,T.symm_apply_apply,unit,smul_add,smul_smul,smul_smul,
    smul_smul,price]
  rw [mul_comm (scalar R Q z clock k) a]

private theorem born (m per:ℕ) (age:R.family.ref 4 ≤ m) (x:R.family.label 4):
    Trace.Physical.GermGraph.page (C:=R.family) 4 per m ((R.family.factory 4 m per).entries m x)=x := by
  let E:=R.makes.calibrated 4 m per age
  have zero:Germ.vector F R.family.params (plank R.family m).threshold
      (0:Site (R.family.side m per)) (0:Config G (R.family.side m per)→ℂ)=0:=by
    unfold Germ.vector Germ.label
    split
    next h =>
      rw [show h.choose=0 from Next.Foundations.JetTest.unique h.choose_spec
        ((Next.Foundations.jetTest_zero_iff ..).mpr (fun i=>⟨contDiffAt_const,fun k _=>by simp⟩)),map_zero,map_zero]
    next => simp
  unfold Trace.Physical.GermGraph.page Germ.projection
  rw [show ((R.family.factory 4 m per).entries m x).x=x from E.bare_coord x,
    show ((R.family.factory 4 m per).entries m x).regular=0 from E.bare_germ x]
  simp only [Pi.zero_apply,zero,tsum_zero,add_zero]

theorem measured (m per:ℕ) (age:R.family.ref 4 ≤ m) (z:Stock B) (clock:ℝ) (k:ℕ):
    WilsonMatrixOriginalGermMarket.normalized R m m per (submitted R Q m per z clock k)=
      bank R Q m z clock k := by
  unfold WilsonMatrixOriginalGermMarket.normalized
  rw [born R m per age,frame R Q m per age,Complex.ofReal_pow,smul_smul]
  rw [inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos m).ne')),one_smul]

private theorem thermal (t:ℝ) (z:Stock B): (F).scaled t (coordinates R z)=((t^2:ℝ):ℂ) • coordinates R z := by
  unfold coordinates
  rw [map_sum,Finset.smul_sum]
  apply sum_congr rfl
  intro i _
  exact (((F).scaled t).map_smul (z.2 i) ((warehouse R).fits B 4 2 i)).trans
    ((congrArg (z.2 i • ·) ((F).scaled_pure t (4,2) (Warehouse.label_grade B i))).trans (smul_comm ..))

/-- The cutoff N enters through the real running coupling of the held m law. -/
theorem calibrated (m N per:ℕ) (age:R.family.ref 4 ≤ m) (z:Stock B) (clock:ℝ) (k:ℕ):
    (F).scaled (shrink R.family m N per)
      (WilsonMatrixOriginalGermMarket.normalized R m m per (submitted R Q m per z clock k))=
      scalar R Q z clock k • (F).e0+
        ((Pert.Asymptotics.regulatorRun R.family N per m^2:ℝ):ℂ) • coordinates R (projected Q clock k z) := by
  let t:=shrink R.family m N per
  let θ:=R.family.path.levels.clock.threshold m
  have hp:θ≠0:=(R.family.path.levels.budget m).threshold_pos.ne'
  have size:(↑(θ^2:ℝ):ℂ)*(↑(t^2:ℝ):ℂ)=(↑(Pert.Asymptotics.regulatorRun R.family N per m^2:ℝ):ℂ):=by
    rw [←Complex.ofReal_mul]
    congr 1
    change θ^2*((Real.sqrt (R.family.path.β N per m))⁻¹/θ)^2=((Real.sqrt (R.family.path.β N per m))⁻¹)^2
    field_simp
  rw [measured R Q m per age,bank,map_add,((F).scaled t).map_smul,((F).scaled t).map_smul,(F).scaled_unit,
    thermal R t,smul_smul,size]

end YM.Integration.WilsonReportingMeasuredWardSourceGerm
