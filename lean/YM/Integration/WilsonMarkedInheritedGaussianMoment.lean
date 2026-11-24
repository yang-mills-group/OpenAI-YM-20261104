import YM.MSbar.Kelvin.Mead
import YM.AllOrder.Fire.PriceR

/-! Absolute moments on the full native Gaussian, including correlated
coordinates, and their use on a purchased angular coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedInheritedGaussianMoment
open Function Filter Finset MeasureTheory Further.GaussianScalar Matrix MSbar.Cacao AllOrder.Fire
open scoped Topology BigOperators Classical

variable {I:Type} [Fintype I] [DecidableEq I]

def charge (I:Type) [Fintype I] (c:ℝ) (p:ℕ) : ℝ :=
  1+(Fintype.card I:ℝ)*(2*Real.exp (c*(p:ℝ)^2/2))

omit [DecidableEq I] in
theorem survey (x:I→ℝ) (p:ℕ) : (1+‖x‖)^p≤1+∑i:I,(1+|x i|)^p := by
  cases isEmpty_or_nonempty I
  · simp [Subsingleton.elim x (0:I→ℝ)]
  obtain ⟨a,_,largest⟩:=Finset.exists_max_image univ (fun i:I=>|x i|) Finset.univ_nonempty
  have hx:‖x‖≤|x a|:=(pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i=>largest i (mem_univ _)
  have one:(1+|x a|)^p≤∑i:I,(1+|x i|)^p:=
    single_le_sum (f:=fun i:I=>(1+|x i|)^p) (fun i _=>by positivity) (mem_univ a)
  exact (pow_le_pow_left₀ (by positivity) (add_le_add_right hx 1) p).trans (one.trans (le_add_of_nonneg_left zero_le_one))

theorem complete {k:Matrix I I ℝ} (h:k.PosDef) (c:ℝ) (hc:∀i,k i i≤c) (p:ℕ) :
    Integrable (fun x:I→ℝ=>(1+‖x‖)^p) (fieldLaw k) ∧
    (∫x:I→ℝ,(1+‖x‖)^p ∂fieldLaw k)≤charge I c p := by
  have marginal:=MSbar.Kelvin.pol h c hc
  let total (x:I→ℝ):=∑i:I,(1+|x i|)^p
  have ht:Integrable total (fieldLaw k):=integrable_finsetSum _ fun i _=>(marginal i p).1
  have hall:= (integrable_const (μ:=fieldLaw k) (1:ℝ)).add ht
  have hfull:Integrable (fun x:I→ℝ=>(1+‖x‖)^p) (fieldLaw k) :=
    hall.mono' (by fun_prop) (ae_of_all _ fun x=>by
      rw [Real.norm_of_nonneg (show 0≤(1+‖x‖)^p by positivity)]; exact survey x p)
  refine ⟨hfull,(integral_mono hfull hall (fun x=>survey x p)).trans ?_⟩
  change (∫x:I→ℝ,1+total x ∂fieldLaw k)≤_
  rw [integral_add (integrable_const _) ht,integral_const,probReal_univ,one_smul]
  unfold total charge
  rw [integral_finsetSum _ fun i _=>(marginal i p).1]
  apply add_le_add_right
  exact (sum_le_sum (fun i _=>(marginal i p).2)).trans_eq (by simp)

variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The full measured insertion may have either sign. The bound is on its
absolute integral after the submitted affine change of variables. -/
theorem insertion {k:Matrix I I ℝ} (h:k.PosDef) (c:ℝ) (hc:∀i,k i i≤c) (p:ℕ) {b:ℝ}
    {F:E→ℝ} (spent:Prices p b F) (A:(I→ℝ)→E) (regular:Continuous A) (M:ℝ) (hm:0≤M)
    (growth:∀x,1+‖A x‖≤M*(1+‖x‖)) :
    Integrable (fun x=>F (A x)) (fieldLaw k) ∧
    (∫x,|F (A x)| ∂fieldLaw k)≤b*M^p*charge I c p := by
  obtain ⟨moment,measured⟩:=complete h c hc p
  have estimate (x:I→ℝ):|F (A x)|≤(b*M^p)*(1+‖x‖)^p:=by
    calc _ ≤ b*(1+‖A x‖)^p:=spent.2.2 _
         _ ≤ b*(M*(1+‖x‖))^p:=mul_le_mul_of_nonneg_left
             (pow_le_pow_left₀ (by positivity) (growth x) p) spent.1
         _ = _:=by rw [mul_pow,mul_assoc]
  have continuous:Continuous (fun x=>F (A x)):=spent.2.1.read.smooth.continuous.comp regular
  have htop:=moment.const_mul (b*M^p)
  have integr:Integrable (fun x=>F (A x)) (fieldLaw k):=
    htop.mono' continuous.aestronglyMeasurable (ae_of_all _ fun x=>estimate x)
  refine ⟨integr,(integral_mono integr.abs htop estimate).trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left measured (mul_nonneg spent.1 (pow_nonneg hm _))

end YM.Integration.WilsonMarkedInheritedGaussianMoment
end
