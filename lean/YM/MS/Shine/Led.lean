import YM.MS.Arc.House
import Mathlib.Analysis.Calculus.LineDeriv.Basic
/-!
# Laurent regularity I: strong integrals of uniformly Veg families

`veg 0 f a` SUP all derivatives on any chart,
 α index cost integrable; AE suffices. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc ContinuousLinearMap
open scoped Topology ContDiff
variable {A I E F:Type}[MeasurableSpace A]
  [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
  [NormedAddCommGroup F][NormedSpace ℝ F]
variable {μ:Measure A}{f:A→ E→F} (h:∀ᵐ a∂μ, ContDiff ℝ ∞ (f a))
-- meas
lemma twins (p:E)(hs:∀ᵐ a∂μ, DifferentiableAt ℝ (f a) p)(hv:∀ p,AEStronglyMeasurable (fun a=> f a p) μ): AEStronglyMeasurable (fun a=> fderiv ℝ (f a) p) μ:= by
   let B:= Module.finBasis ℝ E; let D := fun a:A=> fderiv ℝ (f a) p; let U := Finset.univ (α:=Fin (Module.finrank ℝ E)); let V (i:Fin (Module.finrank ℝ E)) := (B.coord i).toContinuousLinearMap
   have he(v:E): AEStronglyMeasurable (fun a=>D a v) μ:= aestronglyMeasurable_of_tendsto_ae (f:=fun (t:ℝ) (a:A)=>t⁻¹ • (f a (p+t • v)- f a p)) (𝓝[≠] (0:ℝ)) (fun t=> ((hv (p+t • v)).sub (hv p)).const_smul _) (hs.mono fun a h=> (h.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero)
   have ht(_a:A) (t:E→L[ℝ] F): t= ∑ i, smulRightL ℝ E F (V i) (t (B i)):= by
       ext w; obtain H:= congr_arg t (B.sum_repr w); rw [map_sum] at H; simp_rw [map_smul] at H; rw [_root_.sum_apply]; exact H.symm
   change AEStronglyMeasurable D μ; rw [show D=(fun a=> ∑ i, smulRightL ℝ E F (V i) (D a (B i))) from funext fun i=> ht i _]; exact U.aestronglyMeasurable_fun_sum fun i _=> (smulRightL ℝ E F (V i)).continuous.comp_aestronglyMeasurable (he _)
include h
lemma riders (hv:∀ p,AEStronglyMeasurable (fun a=> f a p) μ)(n:ℕ): ∀ p:E,AEStronglyMeasurable (fun a=> iteratedFDeriv ℝ n (f a) p) μ:= by
   induction n with
   | zero=> intro p; exact (continuousMultilinearCurryFin0 ℝ E F).symm.continuous.comp_aestronglyMeasurable (hv p)
   | succ n ih=>
       intro p; have hz:=twins p (f:=fun a=> iteratedFDeriv ℝ n (f a)) (h.mono fun a h=> h.differentiable_iteratedFDeriv (by norm_cast; exact WithTop.coe_lt_top n) p) ih; exact (continuousMultilinearCurryLeftEquiv ℝ _ _).symm.continuous.comp_aestronglyMeasurable hz
omit h
def Lawn (μ:Measure A)(f:I→A→ E→F)(a:A→ℝ): Prop:=∀ j:ℕ,∃ C:ℝ,0<C ∧ ∃ b:ℕ,∀ i,∀ᵐ t∂μ,∀ p:E, ‖iteratedFDeriv ℝ j (f i t) p‖≤C*(1+‖p‖)^b*a t
variable {a:A→ℝ} {g:I→ A→E→F}(ha:Integrable a μ)(hs:∀ i,∀ᵐ t∂μ, ContDiff ℝ ∞ (g i t))(hm:∀ i p,AEStronglyMeasurable (fun t=> g i t p) μ)(HP:Lawn μ g a)
include ha hs hm HP
lemma lawn (i:I): Majorant μ (g i) where
    smooth:= hs i
    borel := fun n p=> riders (hs i) (hm i) n p
    major:= by
       intro j p; obtain ⟨C,hC,b,hb⟩:=HP j; refine ⟨Metric.ball 0 (‖p‖+1), Metric.isOpen_ball.mem_nhds (by simp),_, ha.const_mul (C*(1+(‖p‖+1))^b), (hb i).mono fun t ht q hq=>?_⟩; refine (ht q).trans ?_; have hq : ‖q‖ < ‖p‖+1:= (by simpa using hq); have ht : 0≤a t:= nonneg_of_mul_nonneg_right ((norm_nonneg _).trans (ht p)) (by positivity); gcongr -- right argument
lemma plush [CompleteSpace F] : veg 0 (fun i x=> ∫ t,g i t x ∂μ) 1:= by
    let V:= max 1 (∫ t, a t ∂μ); have hV:V>0:= lt_max_of_lt_left zero_lt_one
    refine hike (fun i=>(lawn ha hs hm HP i).contDiff) ?_; intro j; obtain ⟨C,hC,b,hb⟩:=HP j; refine ⟨C*V,mul_pos hC hV,b,fun i p=>?_⟩; simp only [Pi.zero_apply,Pi.one_apply,abs_zero,add_zero,one_mul,mul_one,(lawn ha hs hm HP i).identity]; refine (norm_integral_le_of_norm_le (ha.const_mul (C*(1+‖p‖)^b)) ((hb i).mono fun t ht=> ht p)).trans ?_; rw [integral_const_mul, mul_right_comm]; gcongr; exact le_max_right ..
end YM.MS.Shine
