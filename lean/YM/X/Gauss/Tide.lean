import YM.X.Gauss.Milk
import Mathlib.LinearAlgebra.Trace
/-!
First-order Gaussian response interchange E→B preserving leading action, no mark assumptions beyond polynomial and invariant. Pays total divergence on E, force pairing eliminated via projection cost.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gauss
open Function Filter Set MeasureTheory PertExtension PertExtension.GaussianScore Next.Rank Next.Rank.Normal MvPolynomial
open scoped BigOperators Topology ContDiff Classical
variable {E F J : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable [MeasurableSpace E][BorelSpace E][MeasurableSpace F][BorelSpace F]
variable (P:Law E)(μ:Measure E)[μ.IsAddHaarMeasure]
local notation "E₁"=>P.average μ

def trace (H:E→E)(x:E): ℝ:= LinearMap.trace ℝ E (fderiv ℝ H x).toLinearMap
omit [MeasurableSpace E] [BorelSpace E] in
lemma trace_calc (H:E→ E){K:Type*}[Fintype K](b:Module.Basis K ℝ E)(x:E) : trace H x=∑ i:K,b.coord i (fderiv ℝ H x (b i)):= by rw [trace,LinearMap.trace_eq_matrix_trace ℝ b]; simp [Matrix.trace,LinearMap.toMatrix_apply]

-- polynomial projections for applying to P(v)(x) and arbitrary nozzle
omit [MeasurableSpace E] [BorelSpace E] in
lemma pSpray {H:E→E}{f:E→ℝ}(hh:∀ v:Module.Dual ℝ E,Plausible (v ∘ H)) (hp:Plausible f) : Plausible fun x=>fderiv ℝ f x (H x) := by
    let b:=Module.finBasis ℝ E; let A (i):= b.coord i ∘ H; have he : (fun x=> fderiv ℝ f x (H x))=∑ i:Fin (Module.finrank ℝ E), A i * diff' (b i) f := by
       funext x; rw [Finset.sum_apply, ← b.sum_equivFun (H x),map_sum]; exact Finset.sum_congr rfl (fun i _=> map_smul ..)
    rw [he]; exact Plausible.sum (fun i _=>(hh _).mul (hp.ds _))
lemma windless (H:E→E)(hh:∀ v:Module.Dual ℝ E,Plausible (v ∘ H))(hv:Differentiable ℝ H){f:E→ℝ}(hp:Plausible f) : E₁ (fun x=>fderiv ℝ f x (H x) - f x * P.P (H x) x + f x * trace H x) = 0:= by
   let b:=Module.finBasis ℝ E; let A (i):= b.coord i ∘ H
   let d (i):= diff' (b i) (A i*f); let r (i): E→ℝ := A i*f*P.P (b i)
   have he : (fun x=>fderiv ℝ f x (H x) - f x* P.P (H x) x + f x * trace H x)=∑ i: Fin (Module.finrank ℝ E),(d i-r i):= by
      funext x; let F(i):= fderiv ℝ f x (b i); let V(i):= P.P (b i) x
      have he i : d i x= A i x*F i+ f x * b.coord i (fderiv ℝ H x (b i)) := by
         have hg := hh (b.coord i); change fderiv ℝ (A i * f) _ _= _; rw [fderiv_mul (hg.smooth.differentiable (by simp) _) (hp.smooth.differentiable (by simp) _)]
         rw [show fderiv ℝ (A i) x= (b.coord i).toContinuousLinearMap ∘L (fderiv ℝ H x) from ((b.coord i).toContinuousLinearMap.hasFDerivAt.comp x (hv x).hasFDerivAt).fderiv]
         rfl
      rw [Finset.sum_apply]; simp only [Pi.sub_apply,he,dif_pos]; simp_rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← trace_calc ]; rw [add_sub_right_comm]; apply congr_arg (fun t=> t+f x * trace H x)
      rw [← b.sum_repr (H x),map_sum,map_sum, LinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i hi; rw [map_smul,map_smul,LinearMap.smul_apply]; change A i x * F i- f x * (A i x*V i)=A i x * F i-(A i x*f x)*V i; ring
   rw [he, average_sum,Finset.sum_eq_zero]; swap
   · intro i hi; let K:= (hh (b.coord i)).mul hp; exact (K.ds (b i)).sub (Plausible.times _ (P.P (b i)) K) -- type
   intro i hi; have K:= (hh (b.coord i)).mul hp; exact (average_sub _ _ (K.ds (b i)) (Plausible.times _ (P.P (b i)) K)).trans (sub_eq_zero.mpr (byParts P μ K (b i)))

variable (Q:Law F) (ν:Measure F)[ν.IsAddHaarMeasure]
variable (T:E→ₗ[ℝ] F)(B:F→ₗ[ℝ] E)(hb:T ∘ₗ B=LinearMap.id)(h:∀ x y, P.P (B x) y=Q.P x (T y))
local notation "E₂"=>Q.average ν
include B hb h
lemma tangent_proj (v:Module.Dual ℝ F) : T (P.inverse (v.comp T))=Q.inverse v:= by
   have he : P.P (B (Q.inverse v))= v.comp T:= LinearMap.ext (fun x=> (h _ _).trans (by rw [Q.applies];rfl))
   rw [← he,Law.solves]; exact DFunLike.congr_fun hb _
lemma traverse (H:E→F)(hf:∀ v:Module.Dual ℝ F,Plausible (v ∘ H))(he:Differentiable ℝ H)(f g:F→ℝ)(hp:Plausible f)(hg:Plausible g)(ht:Plausible (trace (B ∘ H)))(h0:E₁ ((f ∘ T)*trace (B ∘ H))=0):
    E₁ (fun x=> g (T x) + (fderiv ℝ f (T x) (H x)- f (T x)*Q.P (H x) (T x)))= E₂ g:= by
    let t:= B ∘ H; let w:= f ∘ T; have hh (a:Module.Dual ℝ E):Plausible (a ∘ t):= hf (a.comp B)
    have hw := windless P μ t hh (B.toContinuousLinearMap.differentiable.comp he) (hp.app T)
    have hy : (fun x=> fderiv ℝ f (T x) (H x) - f (T x)* Q.P (H x) (T x))=(fun x=> fderiv ℝ w x (t x)- w x*P.P (t x) x):= by
       funext x; rw [show fderiv ℝ w x=(fderiv ℝ f (T x)) ∘L T.toContinuousLinearMap from ((hp.smooth.differentiable (by simp) (T x)).hasFDerivAt.comp x T.toContinuousLinearMap.hasFDerivAt).fderiv]; change _ = fderiv ℝ f (T x) (T (B (H x))) - f (T x)*P.P (B (H x)) x; rw [h,show T (B (H x))=H x from DFunLike.congr_fun hb _]
    let F' (x:E):= fderiv ℝ w x (t x)-w x*P.P (t x) x
    suffices ht:Plausible F' by
       change E₁ (F' + w*trace t)=0 at hw; rw [average_add P μ ht (show Plausible (w*trace t) from (hp.app T).mul ‹_›),show E₁ (w*trace t)=0 from h0,add_zero] at hw
       rw [show (fun x=>_)=g ∘ T + F' from funext (fun x=> congr_arg (fun a=>g (T x)+a) (congr_fun hy x)), average_add _ _ (hg.app T) ht,(show E₁ F'=0 from hw),add_zero]
       exact moves P μ Q ν T (tangent_proj P Q T B hb h) hg
    refine (pSpray hh (hp.app T)).sub ((hp.app T).mul ?_)
    let b:=Module.finBasis ℝ E
    rw [show (fun (x:E)=>P.P (t x) x)=∑ i:Fin (Module.finrank ℝ E), (b.coord i ∘ t)*(P.P (b i):E→ℝ) from funext (fun x=>by rw [Finset.sum_apply, ← b.sum_repr (t x),map_sum,LinearMap.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul];rfl )]
    exact Plausible.sum fun i _=>(hh _).mul (Plausible.line _)
end YM.PositionX.Gauss
