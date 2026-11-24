import YM.X.Gauss.Tide
/-!
Vanishing by averaging linear functional with global symmetry. For use with total divergence uncomputed.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gauss
open Function Set Filter MeasureTheory PertExtension PertExtension.GaussianScore
open scoped BigOperators Topology ContDiff Classical
variable {E F J : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
section
variable [MeasurableSpace E][BorelSpace E][MeasurableSpace F][BorelSpace F]
variable (P:Law E)(μ:Measure E)[μ.IsAddHaarMeasure]
variable [MeasurableSpace J] (ν:Measure J)[IsProbabilityMeasure ν]
local notation "E₁"=>P.average μ
variable (T:J→ E→ₗ[ℝ] E)(B:J→E→ₗ[ℝ] E)
variable (H:∀ i x y,P.P (B i x) y=P.P x (T i y))(ht:∀ i,T i ∘ₗ B i=LinearMap.id)
include ν H ht
lemma untouched (hA:∀ x,Integrable (fun i=> T i x) ν)(hx:∀ x, ∫ i,T i x ∂ν = 0) (f:E→ℝ)(hf:Plausible f)(hm:∀ i x,f (T i x)=f x)(v: Module.Dual ℝ E): E₁ (f* (⇑v))=0:= by
   let b:= Module.finBasis ℝ E
   let y (i:J)(j):=v (T i (b j)); let m i:=v.comp (T i)
   have hh i : E₁ (f*(⇑v))= ∑ j:Fin (Module.finrank ℝ E), y i j * E₁ (f* (⇑(b.coord j))) := by
      have he i : f* (⇑(m i))=(f*(⇑v)) ∘ T i:= by ext x; rw [comp_apply]; simp only [Pi.mul_apply,hm];rfl
      rw [← moves P μ P μ (T i) (tangent_proj _ _ _ _ (ht i) (H i)) (hf.times (a:=v)), ← he i]
      have H : f*(⇑(m i)) = ∑ j:Fin (Module.finrank ℝ E), y i j • (f*(⇑(b.coord j))) := by ext x; rw [Finset.sum_apply]; change f x*m i x=_; rw (occs:=.pos [2]) [← b.sum_repr x]; rw [map_sum,Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [map_smul (m i)];change f x*(b.coord j x *y i j)=y i j*(f x*b.coord j x); ring
      rw [H, average_sum _ _ (fun j _ => (Plausible.times f (b.coord j) hf).scale _)]; simp only [average_scale]
   calc
      _ = ∫ _ : J,E₁ (f* (⇑v)) ∂ν := by simp
      _ = _ := by
       have he {k:ℕ} (j) : Integrable (fun i=> y i j) ν:= v.toContinuousLinearMap.integrable_comp (hA (b j))
       have hz j : (∫ i,y i j ∂ν)=0:= by rw [show (∫ i,y i j ∂ν) = v.toContinuousLinearMap (∫ i,T i (b j) ∂ν) from v.toContinuousLinearMap.integral_comp_comm (hA _),hx,map_zero]
       conv_lhs=> rhs; intro i; rw [hh i]
       rw [MeasureTheory.integral_finsetSum _ (fun i _=> (he (k:=0) i).mul_const _ )]; simp_rw [integral_mul_const,hz,zero_mul,Finset.sum_const_zero]
end
section
variable (X: E→L[ℝ] E→L[ℝ] F) (T:F→L[ℝ] E)
def ebi (v:E) := X v v
lemma plaus_bi (L: F→ₗ[ℝ] ℝ): Plausible (fun v:E=> L (X v v)):= by
   let U (a:E):= L.toContinuousLinearMap.comp (X a)
   let b:=Module.finBasis ℝ E
   suffices H:(fun v:E=> L (X v v))=∑ i:Fin (Module.finrank ℝ E), (⇑(b.coord i))*(fun y:E=> L (X y (b i))) by rw [H]; exact Plausible.sum fun i _=> (Plausible.line _).times (a:=(L.toContinuousLinearMap.comp ((ContinuousLinearMap.apply ℝ F (b i)).comp X)).toLinearMap) -- method notation see
   funext x; rw [Finset.sum_apply]; change U x x=_; nth_rw 2 [← b.sum_repr x]; rw [map_sum]; exact Finset.sum_congr rfl (fun i _=> map_smul (U x) _ _)
lemma linearize_bi (x:E): fderiv ℝ (ebi X) x=X x+X.flip x:= by
   have he:= (X.hasFDerivAt (x:=x)).clm_apply (hasFDerivAt_id (𝕜:=ℝ) x) 
   convert he.fderiv using 1 <;> first | rfl | exact ContinuousLinearMap.ext (fun v=> rfl)

end
section
variable (X:E→L[ℝ] E→L[ℝ] F)(T:F→L[ℝ] E)
lemma ebi_nice : ContDiff ℝ ω (ebi X) := X.contDiff.clm_apply contDiff_id
lemma eSpray_trace (x:E): trace (T ∘ ebi X) x= LinearMap.trace ℝ E (T ∘L (X x+X.flip x)).toLinearMap:= by rw [trace,fderiv_comp x T.differentiableAt (ebi_nice X|>.differentiable (by simp) x),T.fderiv,linearize_bi]
def eTrace : Module.Dual ℝ E := LinearMap.trace ℝ E ∘ₗ ( {toFun x := (T ∘L (X x+ X.flip x)).toLinearMap, map_add' x y:= by apply LinearMap.ext; intro v; change T (_+_)= T (_+_)+T (_+_); rw [← map_add]; apply congr_arg _; simp [add_add_add_comm], map_smul' c x:= by apply LinearMap.ext; intro v; change T (_+_)= c • T (_+_); rw [← map_smul]; apply congr_arg _; simp [smul_add]} : E →ₗ[ℝ] Module.End ℝ E)
lemma trace_eq : trace (T ∘ ebi X) = eTrace X T:= funext (fun i=>eSpray_trace X T i)
end
end YM.PositionX.Gauss
