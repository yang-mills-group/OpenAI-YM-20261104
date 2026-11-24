import YM.XSpace.LapCon
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Compact Gram sampling

An alternative to invoking the First Fundamental Theorem of classical invariant
theory. Every pair transmitted by the probe can implement an interior differential.
To interpret vanishing of all moments against such probes integrate over an ordinary
compact ball of ALL matrices, where there's a simple by-parts rule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Snow
open Function Set Filter MeasureTheory Lap
open scoped BigOperators Topology RealInnerProductSpace ContDiff Classical
variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (r : ℝ) (n : ℕ)
def bag (n : ℕ) (t : ℝ) := max 0 t ^(n+1)
lemma pile (t : ℝ) : HasDerivAt (bag (n+1)) ((n+2:ℕ)*bag n t) t:= by
  have he x (hx : 0≤x) : bag (n+1) x=x^(n+2):=by simp only [bag,max_eq_right hx,Nat.add_assoc]
  have hs x (hx : x≤0) : bag (n+1) x=0:=by simp [bag,max_eq_left hx]
  have hh x : HasDerivAt (fun t:ℝ=> t^(n+2)) (((n+2:ℕ):ℝ)*x^(n+1)) x:= by
    exact hasDerivAt_pow (n+2) x
  rcases lt_trichotomy t 0 with h|h|h
  · have hz : bag n t=0:=by simp [bag,max_eq_left h.le]
    rw [hz,mul_zero]; apply (hasDerivAt_const _ (0:ℝ)).congr_of_eventuallyEq; exact (gt_mem_nhds h).mono fun x hx=> hs x (le_of_lt hx)
  · subst t; have hx : HasDerivAt (fun t:ℝ=> t^(n+2)) 0 0:=by simpa using hh 0
    rw [show (bag n 0)=0 by simp [bag],mul_zero]
    rw [← hasDerivWithinAt_univ]; convert! (hx.hasDerivWithinAt (s:=Ici 0) |>.congr_of_mem he (self_mem_Ici)).union (((hasDerivAt_const 0 (0:ℝ)).hasDerivWithinAt (s:=Iic 0)).congr_of_mem hs (self_mem_Iic)) using 1
    rw [Ici_union_Iic]
  rw [bag,max_eq_right h.le]; apply (hh _).congr_of_eventuallyEq; exact (lt_mem_nhds h).mono fun i hi=> he i (le_of_lt hi)

def coeff (n : ℕ) : ℝ:= 2*(n+2:ℕ)
def point (r:ℝ) (n:ℕ) (x:F):ℝ:=bag n (r^2-‖x‖^2)
omit [InnerProductSpace ℝ F] in
lemma point_cont : Continuous (point r n (F:=F)):=by unfold point bag; fun_prop
lemma fusion (x:F) : HasFDerivAt (point r (n+1)) (-(coeff n*point r n x) • (innerSL ℝ x)) x:=by
  convert! (pile n (r^2-‖x‖^2)).comp_hasFDerivAt x ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub (r^2)) using 1
  ext u; simp [innerSL_apply_apply,point,coeff]; ring
lemma down (x v : F) : fderiv ℝ (point r (n+1)) x v = -(coeff n*point r n x)*⟪v,x⟫:=by rw [(fusion ..).fderiv, real_inner_comm x v]; rfl
omit [InnerProductSpace ℝ F] in
lemma point_pos {r : ℝ} (h : 0<r) {x:F} (he : ‖x‖<r) : 0 < point r n x:= pow_pos (lt_max_of_lt_right (by nlinarith [norm_nonneg x])) _
omit [InnerProductSpace ℝ F] in
lemma point_nonneg (x:F): 0≤ point r n x:= pow_nonneg (le_max_left ..) _
omit [InnerProductSpace ℝ F] in
lemma dead (x:F) (hx : |r| ≤ ‖x‖): point r n x=0:=by simp [point,bag,max_eq_left (show r^2-‖x‖^2≤ 0 by nlinarith [sq_abs r,abs_nonneg r])]
variable [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma finite (g:F→ E) (hg : Continuous g): Integrable (fun x=> point r n x • g x):=by
  refine ((point_cont ..).smul hg).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (K:=Metric.closedBall (0:F) |r|) (isCompact_closedBall ..) (fun x hx=>?_)
  change point r n x • g x=0; rw [dead r n x (le_of_lt (by simpa [Metric.mem_closedBall] using hx)),zero_smul]
lemma ibp (g : F→ E) (hg : ContDiff ℝ 1 g) (v : F) :
    (∫ x, point r (n+1) x • fderiv ℝ g x v)= coeff n • ∫ x,point r n x • (⟪v,x⟫ • g x) :=by
  have h (x:F): fderiv ℝ (point r (n+1)) x v • g x = (-coeff n) • (point r n x • (⟪v,x⟫ • g x)):=by rw [down]; simp_rw [smul_smul]; rw [neg_mul, neg_mul,mul_assoc]
  rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable ?_ ?_ (finite r (n+1) _ hg.continuous) (fun y _=> (fusion ..).differentiableAt) (fun x _=> hg.differentiable (by decide) x)]
  · simp_rw [h]; rw [integral_smul,neg_smul,neg_neg]
  · simp_rw [h]; exact (finite _ _ _ (((innerSL ℝ v).continuous).smul hg.continuous)).smul _
  exact finite r _ _ ((hg.continuous_fderiv (by decide)).clm_apply continuous_const)
end YM.XSpace.Snow
