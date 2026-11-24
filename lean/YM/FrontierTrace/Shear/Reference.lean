import YM.FrontierTrace.Shear.Contrast
import YM.Pert.Asymptotics.RawAxis
import YM.Next.STATIONARY.OneLoop.MomentumIntegral

/-!
Reference constants for the `signal` contrast. We normalize the conditional
order-2 **claim** in terms of the actual gauge & candidate log residue (evaluated
here by an existing annulus theorem); not asserting that the 3/4*d shear rule
in position space from that perturbative interpretation, or even the poleVec
normalization of stress generally, has been shown yet. Also free Wick norm on
`[1,2]`. KEEP the numerical Wick & pole references independent of the physical
reports.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FrontierTrace
open Function Filter Set Analysis Trace MeasureTheory Table
open Next.UVStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace Interval
variable {G:Gauge}

noncomputable def candidate2 (G:Gauge) : ℝ := - (Trace.anomalyCoefficient G)/2
noncomputable def signal2 (G:Gauge) : ℝ:= (5/4:ℝ)*Trace.anomalyCoefficient G*Trace.theoryDensity G
noncomputable def full4 (G:Gauge) : ℝ:=(4*candidate2 G)^2*Trace.theoryDensity G
lemma candidate_negative (h:G.Simple): candidate2 G<0:=by
   unfold candidate2; have := anomalyCoefficient_pos h; linarith
lemma signal2_pos (h:G.Simple): 0<signal2 G:=by unfold signal2; positivity [anomalyCoefficient_pos h, theoryDensity_pos h]
lemma full4_pos (h:G.Simple): 0<full4 G:=mul_pos (sq_pos_of_ne_zero (mul_ne_zero (by norm_num) (candidate_negative h).ne)) (theoryDensity_pos h)
-- Determinant pole normalization. This is the local pure-gauge annular ingredient,
-- separate from matching it to WilsonX/the position-scheme stress.
lemma equals_pole_target (G:Gauge) (μ:ℝ) (h:0<μ)(he:μ<1):
    candidate2 G = Stationary.cartWeight * (∫ x in Stationary.orbShell μ, Stationary.poleVec G (Stationary.exileE x))/(4*Real.log μ⁻¹) := by
   rw [Stationary.poleSpin h he.le]
   rw [← Pert.Asymptotics.b0_normalizes]
   have ht : 0<Real.log μ⁻¹ := Real.log_pos ((one_lt_inv₀ h).mpr he)
   unfold candidate2; change -(Pert.Asymptotics.b0 G)/2=_
   rw [eq_div_iff (mul_ne_zero (by norm_num) ht.ne')]; ring

noncomputable def K0 (G:Gauge)(t:ℝ):ℂ:= (↑((Trace.theoryDensity G)/t^8):ℂ)
noncomputable def determinant0 (G:Gauge) : ℝ:= -(15/8:ℝ)*Trace.theoryDensity G
lemma determinant0_neg (h:G.Simple): determinant0 G<0:=by unfold determinant0; have := theoryDensity_pos h; linarith
lemma K0_cont (G:Gauge): ContinuousOn (K0 G) [[1,2]]:= fun x hx=>by
   have ht:0<x:=by rw [uIcc_of_le (by norm_num)] at hx; exact zero_lt_one.trans_le hx.1
   exact (Complex.continuous_ofReal.continuousAt.comp
     (continuousAt_const.div (continuousAt_id.pow 8) (by exact pow_ne_zero _ ht.ne'))).continuousWithinAt
lemma K0_norm (h:G.Simple) (t:ℝ)(ht: t∈ [[(1:ℝ),2]]): ‖K0 G t‖≤ Trace.theoryDensity G:= by
   rw [uIcc_of_le (by norm_num)] at ht
   have ht : 1≤t:=ht.1; have hK:= theoryDensity_pos h
   rw [K0,Complex.norm_real,Real.norm_of_nonneg]
   · exact div_le_self hK.le (one_le_pow₀ ht)
   positivity

lemma determinant_free (G:Gauge): intervalView (K0 G)=(determinant0 G:ℂ):=by
   let M:= Trace.theoryDensity G; let F(t:ℝ):=(4*t^3) • K0 G t
   have he:∫ t in (1:ℝ)..2, F t = (15/16:ℝ) • (M:ℂ):=by
       rw [intervalIntegral.integral_congr (g:=fun t:ℝ=> t^(-5:ℤ) • ((↑(4*M):ℂ))) ?_]; swap
       · intro x hx; rw [uIcc_of_le (by norm_num : (1:ℝ)≤2)] at hx
         have hh:0<x:=zero_lt_one.trans_le hx.1
         change (4*x^3) • K0 G x = (x^(-5:ℤ)) • ((↑(4*M):ℂ))
         unfold K0
         rw [Complex.real_smul, Complex.real_smul,←Complex.ofReal_mul, ← Complex.ofReal_mul]; congr 1; unfold M; field_simp
       rw [intervalIntegral.integral_smul_const, integral_zpow (a:=(1:ℝ)) (b:=(2:ℝ)) (Or.inr ⟨(show (-5:ℤ) ≠ -1 by norm_num),by norm_num [uIcc_of_le]⟩) ]; norm_num [Complex.real_smul]; ring
   unfold intervalView; change _- ∫ t in (1:ℝ)..2, F t = _; rw [he]; unfold K0 determinant0 M
   norm_num [Complex.real_smul]; ring
lemma pole_consistent (G:Gauge) : candidate2 G * determinant0 G = (3/4:ℝ)*signal2 G:= by
   unfold candidate2 determinant0 signal2; ring

-- Exact free reference as coefficient-state two point, no A-scheme hypotheses.
lemma free_value (G:Gauge) (L:Labels.Frames G) {ℓ:E4}(h:‖ℓ‖=1)(t:ℝ)(ht:0<t):
   Ward.disc (fun _:Fin 2 => (⟨4,scalarLabel L⟩ : (Maxwell.Free.Model L).Tag)) (atShape (t • ℓ)) = K0 G t := by
   have he : atShape (t • ℓ)= Maxwell.Free.pairPoints (t • ℓ) 0:=by ext1 i; fin_cases i <;> rfl
   rw [he, reference_pair L (aim_ne ℓ h t ht),sub_zero,norm_smul_of_nonneg ht.le,h,mul_one]; simp [K0,theoryDensity]
lemma stableView {f g : ℝ→ℂ}{ε:ℝ} (hf : ContinuousOn f [[1,2]])(hg:ContinuousOn g [[1,2]])
    (h:∀ t:ℝ,t∈[[(1:ℝ),2]]→ ‖f t-g t‖≤ε): ‖intervalView f-intervalView g‖≤ (49:ℝ)*ε:=by
   let a:=fun (t:ℝ)=>(4*t^3:ℝ)
   let W t:=f t-g t
   let p:= ∫ t in (1:ℝ)..2, a t • W t
   have ha: Continuous a:=by unfold a; fun_prop
   have hh : ‖p‖ ≤ 32*ε := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C:=32*ε) (f:=fun t=> a t • W t) (a:=(1:ℝ)) (b:=2) ?_).trans_eq (by norm_num); intro x hx
      rw [uIoc_of_le (by norm_num)] at hx; have hx' : 0<x:= zero_lt_one.trans hx.1
      unfold a; rw [norm_smul_of_nonneg (by positivity)]; have H : ‖W x‖≤ε:= h x (by rw [uIcc_of_le (by norm_num)]; exact ⟨hx.1.le,hx.2⟩)
      have ht:x^3 ≤ 8:= (pow_le_pow_left₀ hx'.le hx.2 3).trans_eq (by norm_num)
      exact mul_le_mul (by linarith) H (norm_nonneg _) (by norm_num)
   rw [show intervalView f-intervalView g = (16:ℝ) • W 2-W 1-p from ?_]
   · calc
       _ ≤ ‖(16:ℝ) • W 2-W 1‖+‖p‖:= norm_sub_le ..
       _ ≤ (16*ε + ε)+32*ε:=add_le_add ((norm_sub_le ..).trans (add_le_add (by
         rw [norm_smul_of_nonneg (by norm_num : (0:ℝ)≤16)]
         apply mul_le_mul_of_nonneg_left (h 2 right_mem_uIcc) (by norm_num)) (h 1 left_mem_uIcc))) hh
       _ = _:= by ring
   unfold intervalView p a W at *
   simp_rw [smul_sub]
   rw [intervalIntegral.integral_sub]; swap
   · exact ((ha.continuousOn (s:=[[1,2]])).smul hf).intervalIntegrable
   swap
   · exact ((ha.continuousOn (s:=[[1,2]])).smul hg).intervalIntegrable
   abel
end YM.FrontierTrace
