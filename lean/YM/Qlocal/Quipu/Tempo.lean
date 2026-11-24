import YM.Qlocal.Quipu.Albums
import YM.Comparison.RG02.Assembly.Shift
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet
open Function Filter Lattice Laurent RG Wilson Stationary Lasso Zora Work.F02 Metric
open Marker Multi Finset Set
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
open ConnectedActivityE6.Blaze Extra.Iteration Push Uniform Comparison.RG02.Assembly
variable {V:Type}[DecidableEq V]{ι E:Type} {G:Gauge}{k n j r i:ℕ} {c:Side} {d t a v u C:ℝ}{R:Census V}
open Vase Album
variable (p:ι→Prop)(o:V→Site c) {s:Senses R}(A:Album ι s G n)(x:Site c)(U:Config G c)(t':ℕ)(F:Vase s G n)
variable [NormedAddCommGroup E][NormedSpace ℝ E] {y:E}(T:E→ Config G c)(hv: T 0=1)
abbrev Weather (T:E→ Config G c) (y:E):= ∀ i, ContDiffAt ℝ ω (fun t=> G.mat (T t i)) y
namespace Album
variable (h:A.Health a C)(ha:0<a)
variable (H:Weather T y)(hH:Weather T 0)
include H
lemma habitat (k:ℕ):∃ d:ℝ, ∀ᶠ y' in 𝓝 y, Mode T y' k d:= by
 let v:= royalty G; choose f hf h₁ using fun i=> Brush.neighborhood y ((H i).of_le (le_top (a:=(↑k :WithTop ℕ∞))))
 let p:= ∑ i,f i; refine ⟨(1+p)*(1:ℝ),?_⟩; filter_upwards [eventually_all.mpr h₁] with y hv -- shadow H
 refine ⟨by unfold p; exact mul_nonneg (add_nonneg zero_le_one (sum_nonneg fun i _=>(hf i).le)) zero_le_one,fun i=>?_⟩; apply (thicken (f:=fun z=> T z i) (hv i)).climb le_rfl; gcongr; exact single_le_sum (f:=f) (fun i _=> (hf i).le) (mem_univ _)
omit H
-- often enough to get ν brush on all E.P async.Leg
section births
include hv hH
private lemma needle (s: Ink G n)(i:Fin n): GradeAt 1 (fun y=> amend G t' (F.tan i) (travel (T y) x (F.maps i).tour) (s i)) := by
 let f := physical ∘ T; let u:= (F.maps i).tour; let g:= brand (F.tan i) G t' x u; let l:=F.tan i; have hx:ContDiffAt ℝ ω f 0:=physical_contDiffAt hH; have hG: ContDiffAt ℝ ω (g ∘ f) 0:= ((brand_l x t' l u|>.restrict_scalars ℝ).contDiffAt).comp _ hx; let L : CColor G→L[ℝ]ℂ:= ContinuousLinearMap.proj (s i); refine GradeAt.anchored ?_ ?_
 · have hf(y:E): amend G t' l (travel (T y) x u) (s i)=Complex.reCLM (L ((g∘f) y)):=by unfold g f; simp only [Function.comp_apply, physical_,colorUp_apply]; rfl
   rw [funext hf]; exact Complex.reCLM.contDiff.contDiffAt.comp _ (L.contDiff.contDiffAt.comp _ hG)
 rw [hv, AnalyticBridge.VerifiedReset.unitTravel,amend];split<;>simp only [Function.comp_apply,G.curvature_unit,thetaZero]<;>rfl
lemma Vase_rank : GradeAt n (F.read x t' ∘ T):= by
 let f(s:Ink G n)(i:Fin n)(y:E):= amend G t' (F.tan i) (travel (T y) x (F.maps i).tour) (s i); have he(s:Ink G n)(p:Finset (Fin n)): GradeAt p.card (fun y=>∏ i∈p,f s i y):= by
   induction p using Finset.cons_induction with
   | empty => simp only [Finset.prod_empty,Finset.card_empty]; exact GradeAt.unchecked contDiffAt_const
   | cons s₀ p hx ih=> simp_rw [Finset.card_cons,Finset.prod_cons,mul_comm (f _ s₀ _ )]; exact ih.mul (needle x t' F T hv hH s s₀) -- binder
 refine (?_ : (F.read x t' ∘ T)=(fun y=>∑ s:Ink G n, F.ink s*∏ i,f s i y)) ▸ (show GradeAt _ (fun y=>∑ s:Ink G n, F.ink s*∏ i,f s i y) from GradeAt.list_sum _ (fun s=>(fun _=> F.ink s)* (fun y=>∏ i,f s i y)) (fun s _=>?_)) -- cast
 swap; · have hx:= (GradeAt.unchecked (show ContDiffAt ℝ ω (fun _:E=> F.ink s) 0 from contDiffAt_const)).mul (he s Finset.univ); simpa only [Finset.card_univ,Fintype.card_fin, Nat.zero_add] using hx
 exact funext fun _=> F.globe ..
include h ha
lemma rank : GradeAt n (A.realize p x t' ∘ T):= by
 -- comment
 refine ⟨winter p A x t' h ha T hH,fun i hi=>?_⟩; obtain ⟨d, hd⟩:= habitat T hH i; rw [← (printing p A x t' h ha T hH hd (le_refl i)).tsum_eq]; apply Eq.trans (b:=∑' _:ι,(0:ContinuousMultilinearMap ℝ (fun _:Fin i=>E) ℝ)); apply tsum_congr; intro j; change iteratedFDeriv ℝ i (A.readout p x t' j ∘ T) 0= 0; unfold readout; split; exact (Vase_rank x t' (A j) T hv hH).vanish i hi; exact (GradeAt.grade_zero n).vanish _ hi -- inspect
 exact tsum_zero
end births
end Album
end YM.Qlocal.Quipu.Sonnet
