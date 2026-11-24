import YM.MSbar.Kelvin.Coke
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Kelvin
open Function Filter MeasureTheory Cacao PowerSeries Finset Whisk
open scoped Topology BigOperators Classical
open Lattice Matrix Further.GaussianScalar ProbabilityTheory Set
variable {ι σ τ:Type}[Fintype σ][Fintype ι][Fintype τ][DecidableEq σ] [DecidableEq ι]
    {n:Side} {l:σ→ Site n}{k:Matrix σ σ ℝ}
    (h:k.PosDef)(c:ℝ)(hc:∀ i,k i i ≤c)
local notation "F"=>View σ
local notation "p!"=>fieldLaw k
open WithLp
include h
lemma keeper (i:σ): MeasurePreserving (fun u:View σ=> u i) (fieldLaw k) (gaussianReal 0 (k i i).toNNReal) :=by
    refine ⟨(continuous_apply i).measurable, ?_⟩; unfold fieldLaw; rw [Measure.map_map (by fun_prop) (by fun_prop)]; exact (measurePreserving_eval_multivariateGaussian (μ:=0) (i:=i) h.posSemidef|>.map_eq)
local notation "E!"=>fieldLaw
include hc
-- M uncertain gaussian.T.Leaf.Bounds.
lemma laplace (c':ℝ) (i:σ) : (∫ v:View σ,Real.exp (c'*v i)∂fieldLaw k) ≤ Real.exp (c * c'^2 / 2) :=by
   have hp:= mgf_gaussianReal ((keeper h i).map_eq) c'; unfold mgf at hp; rw [hp]; apply Real.exp_monotone; have he:=hc i; have hh:0< k i i:= h.diag_pos; simp only [zero_mul, zero_add,Real.coe_toNNReal _ hh.le]; gcongr
-- tail μΩ.General c test.
lemma chorus (i:σ)(t b:ℝ)(ht:0 ≤ b): (fieldLaw k).real {v:View σ | t < |v i|} ≤ 2 * Real.exp (-(b*t)+ c*b^2/2) :=by
   let X: Set (View σ):= {v | t < |v i|}; let a:= Real.exp (b*t); let f(t:ℝ)(v:View σ):= Real.exp (t * v i); let K(v:View σ):= f b v + f (-b) v; have he(t): Integrable (f t) p! := (keeper h i).integrable_comp_of_integrable (integrable_exp_mul_gaussianReal t)
   have ht(x):X.indicator (fun i=> a) x ≤ K x:=by
        by_cases hp:x∈X; rw [Set.indicator_of_mem hp]; have hi: t< |x i|:=hp; unfold a K f; rcases lt_abs.mp hi with ha|ha; exact (Real.exp_monotone (mul_le_mul_of_nonneg_left ha.le ht)).trans (le_add_of_nonneg_right (Real.exp_pos _|>.le))
        exact (Real.exp_monotone (show b*t ≤ -b*x i by linarith only [mul_le_mul_of_nonneg_left ha.le ht])).trans (le_add_of_nonneg_left (Real.exp_pos _|>.le))
        rw [Set.indicator_of_notMem hp]; exact add_nonneg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le)
   have hX : MeasurableSet X:= (isOpen_lt continuous_const ((continuous_apply i).abs)).measurableSet
   apply le_of_mul_le_mul_right _ (a:=a) (Real.exp_pos _); have hh:=integral_mono ((integrable_const (μ:=p!) _).indicator hX) ((he b).add (he (-b))) ht; rw [integral_indicator hX, setIntegral_const, smul_eq_mul, integral_add' (he b) (he (-b))] at hh; -- fix
   apply hh.trans; refine (add_le_add (laplace h c hc b i) (laplace h c hc (-b) i)).trans_eq ?_; rw [neg_sq, mul_assoc,show a=Real.exp (b*t) from rfl,←Real.exp_add,show -(b*t)+c*b^2/2+(b*t)=c*b^2/2 by ring]; ring -- graphic
-- Noncompact heights.Native. exp norm.|C.We powers.P.Core. exp_le.We
lemma pol (i:σ)(p:ℕ): Integrable (fun v:View σ=>(1+ |v i|)^p) p! ∧
      (∫ v:View σ,(1+|v i|)^p∂fieldLaw k) ≤ 2*Real.exp (c*(p:ℝ)^2/2) :=by
   let f(v:ℝ)(x:View σ):=Real.exp (v*x i); let g(x:F):=(1+|x i|)^p; let u:ℝ:=p
   have he(v): Integrable (f v) p! := (keeper h i).integrable_comp_of_integrable (integrable_exp_mul_gaussianReal v); let k':= f u + f (-u); have hk :0 ≤ u:=Nat.cast_nonneg _
   have hv(x): g x ≤ k' x:= by
       unfold g; have he:(1+ |x i|)^p ≤ Real.exp (u*|x i|):=by rw [Real.exp_nat_mul]; apply pow_le_pow_left₀ (by positivity) (le_trans (le_of_eq (add_comm 1 _)) (Real.add_one_le_exp _))
       apply he.trans; rcases le_total 0 (x i) with hp|hp; rw [abs_of_nonneg hp]; exact le_add_of_nonneg_right (Real.exp_pos _).le
       rw [abs_of_nonpos hp,mul_neg,← neg_mul]; exact le_add_of_nonneg_left (Real.exp_pos _).le
   have ht: Integrable k' p! :=  (he u).add (he (-u)); have hh: Integrable g p! := ht.mono' (((continuous_const.add (continuous_apply i).abs).pow p).aestronglyMeasurable) (ae_of_all _ fun x=> by rw [Real.norm_of_nonneg (show 0≤g x from by unfold g; positivity)]; exact hv x)
   refine ⟨hh,?_⟩; apply (integral_mono hh ht hv).trans; rw [show k'= f u + f (-u) from rfl,integral_add' (he u) (he (-u))]; apply (add_le_add (laplace h c hc u i) (laplace h c hc (-u) i)).trans_eq; rw [neg_sq]; unfold u; ring
end YM.MSbar.Kelvin
