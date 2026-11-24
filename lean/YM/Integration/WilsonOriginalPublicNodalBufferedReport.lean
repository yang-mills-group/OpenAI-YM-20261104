import YM.Integration.WilsonIndependentSpoutMasterCutoff
import YM.Integration.WilsonOriginalPublicNodalReportedDegree
import YM.Integration.WilsonPositionProgramTrialPublicSlope

/-! A common K clock reports the actual old and reprinted ordinary scalar, including its unit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalBufferedReport
open PowerSeries Function Finset Lattice Wilson RG Precision Source Labels WilsonCoeffUV
open WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Power XSpace RegulatorIR RegulatorIR.Clocks RegulatorIR.Profiles
open WilsonIndependentPublicReportComplex (apply row)
open WilsonOriginalPublicNodalReportedDegree (lift)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonIndependentSpoutDoseBoundary (into)
open scoped Classical BigOperators

def tariff (K:Feeds)(D q:ℕ)(B:Cost):ℝ:=
  ∑ j∈Finset.range (q+1),‖row K D q j‖*∑ i∈Finset.range (j+1),‖coeff j ((B*X)^i)‖

def read (K:Feeds)(D q:ℕ)(B:Cost)(P:Cost):ℂ:=coeff q (apply K D (lift (reel B P)))

theorem bought (K:Feeds)(D q:ℕ)(B P T:Cost)(fee:ℝ)
    (paid:∀i≤q,‖coeff i P-coeff i T‖≤fee):
    ‖read K D q B P-read K D q B T‖≤tariff K D q B*fee:=by
  have axis:constantCoeff (B*X)=0:=by simp
  have price (j:ℕ)(hj:j ≤ q):‖coeff j (reel B P)-coeff j (reel B T)‖ ≤
      (∑i∈Finset.range (j+1),‖coeff j ((B*X)^i)‖)*fee:=by
    rw [reel_apply,reel_apply,XSpace.FPS.coeff_substituted P axis,XSpace.FPS.coeff_substituted T axis,
      ←Finset.sum_sub_distrib,Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi=>?_ )
    rw [smul_eq_mul,smul_eq_mul,←sub_mul,norm_mul,mul_comm]
    exact mul_le_mul_of_nonneg_left (paid i (by have:=Finset.mem_range.mp hi;omega)) (norm_nonneg _)
  rw [read,read,WilsonIndependentPublicReportComplex.coefficients,
    WilsonIndependentPublicReportComplex.coefficients,←Finset.sum_sub_distrib,tariff,Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj=>?_ )
  simp only [WilsonOriginalPublicNodalReportedDegree.lift,coeff_map,←sub_mul,norm_mul]
  change ‖((coeff j (reel B P):ℝ):ℂ)-((coeff j (reel B T):ℝ):ℂ)‖*‖(row K D q j:ℂ)‖ ≤ _
  rw [←Complex.ofReal_sub,Complex.norm_real,Complex.norm_real,mul_comm,mul_assoc]
  exact mul_le_mul_of_nonneg_left (price j (by have:=Finset.mem_range.mp hj;omega)) (norm_nonneg _)

theorem intrinsic (B T:Cost)(b:constantCoeff B=1)(t:constantCoeff T=1)
    (K:Feeds)(D q:ℕ)(low:q≤1)(P:Cost):read K D q B P=read K D q T P:=by
  have first:=WilsonPositionProgramTrialPublicSlope.kinetic B P b
  have last:=WilsonPositionProgramTrialPublicSlope.kinetic T P t
  rw [read,read,WilsonIndependentPublicReportComplex.coefficients,
    WilsonIndependentPublicReportComplex.coefficients]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  simp only [WilsonOriginalPublicNodalReportedDegree.lift,coeff_map]
  have hj':j≤1:=by have:=Finset.mem_range.mp hj;omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj' with rfl|rfl
  · simp only [coeff_zero_eq_constantCoeff,first.1,last.1]
  · rw [first.2,last.2]

end YM.Integration.WilsonOriginalPublicNodalBufferedReport
