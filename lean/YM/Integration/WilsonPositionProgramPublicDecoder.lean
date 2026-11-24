import YM.Integration.WilsonPositionProgramPublicGram
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! One signed decoder on the whole test array with a uniform finite-basis
price, also for measured data outside the exact limiting range. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicDecoder
open Function Filter BigOperators
open scoped Classical Topology
variable {E P I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [Fintype I]

def fee (b : Module.Basis I ℂ E) : ℝ := ∑ i, ‖(b.coord i).toContinuousLinearMap‖ * ‖b i‖

theorem original (b : Module.Basis I ℂ E) (A : E →ₗ[ℂ] P) {K : ℝ} (hk : 0 ≤ K)
    (seen : ∀ v, ‖v‖ ≤ K*‖A v‖) :
    ∃ L : P →L[ℂ] E, (∀ v, L (A v) = v) ∧ ‖L‖ ≤ fee b * K := by
  have inj : Injective A := by
    intro x y eq
    have q := seen (x-y)
    rw [map_sub,eq,sub_self,norm_zero,mul_zero] at q
    exact sub_eq_zero.mp (norm_le_zero_iff.mp q)
  let U := LinearEquiv.ofInjective A inj
  let back := U.symm.toLinearMap.toContinuousLinearMap
  have raw (y : LinearMap.range A) : ‖back y‖ ≤ K*‖y‖ := by
    have eq : A (U.symm y) = y.val := congrArg Subtype.val (U.apply_symm_apply y)
    change ‖U.symm y‖ ≤ K*‖y.val‖
    simpa only [eq] using seen (U.symm y)
  have normBack : ‖back‖ ≤ K := back.opNorm_le_bound hk raw
  let coord (i : I) := (b.coord i).toContinuousLinearMap.comp back
  choose g same normG using fun i => exists_extension_norm_eq (LinearMap.range A) (coord i)
  let L : P →L[ℂ] E := ∑ i, (g i).smulRight (b i)
  have out (y : P) : L y = ∑ i, g i y • b i := by simp [L]
  refine ⟨L,fun x => ?_,?_⟩
  · rw [out,←b.sum_repr x]
    apply Finset.sum_congr rfl
    intro i _
    have hi := same i (U x)
    change g i (A x) = (b.coord i) (U.symm (U x)) at hi
    rw [LinearEquiv.symm_apply_apply] at hi
    rw [b.sum_repr]
    exact congrArg (fun a : ℂ => a • b i) hi
  · have pos : 0 ≤ fee b * K :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hk
    apply L.opNorm_le_bound pos
    intro x
    rw [out]
    calc
      _ ≤ ∑ i, ‖g i x • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, (‖(b.coord i).toContinuousLinearMap‖*‖b i‖)*(K*‖x‖) := by
        apply Finset.sum_le_sum
        intro i _
        have bound : ‖g i‖ ≤ ‖(b.coord i).toContinuousLinearMap‖*K := by
          rw [normG i]
          exact ((b.coord i).toContinuousLinearMap.opNorm_comp_le back).trans
            (mul_le_mul_of_nonneg_left normBack (norm_nonneg _))
        rw [norm_smul]
        calc
          _ ≤ (‖(b.coord i).toContinuousLinearMap‖*K*‖x‖)*‖b i‖ := mul_le_mul_of_nonneg_right
            ((g i).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right bound (norm_nonneg _))) (norm_nonneg _)
          _ = _ := by ring
      _ = _ := by rw [←Finset.sum_mul,mul_assoc];rfl

end YM.Integration.WilsonPositionProgramPublicDecoder
