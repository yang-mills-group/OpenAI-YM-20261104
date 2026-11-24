import YM.Next.MAXWELL.Covariance

set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder InnerProductSpace
variable {G: Gauge}
lemma volumes {G : Gauge} (x : WickPol G) (c : ℝ) : (c:ℂ) • x=c • x := (RCLike.real_smul_eq_coe_smul (K:=ℂ) c x).symm
/-- Recover the real span from the complex span. -/
lemma real_scale (p : WickPol G) (c : ℂ) : realForm (c • p)=star c • realForm p := by
  simp [realForm,← MvPolynomial.C_mul']
end YM.Maxwell.Free
