import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inc
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.ComplexBrush
open Function Filter Set ConnectedActivityE6.Blaze
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {k i j : ℕ} {u v w C d : ℝ} {f : F→ℝ} {g : F→ℂ}
variable {x : F}
lemma smul_left (z : ℂ)(h:Brush j u v g x): Brush j (‖z‖*u) v (fun y=> z*g y) x:=by
  simpa only [zero_add] using! (Brush.certified (k:=j) (le_refl (0:ℝ)) z).paints h
lemma cast (h:Brush j u v f x) : Brush j u v (fun y=> Complex.ofReal (f y)) x:= by
  let L:=Complex.ofRealCLM
  have hL:‖L‖ ≤1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a=> (by rw [one_mul,show L a=a from rfl,Complex.norm_real])
  refine ⟨L.contDiff.contDiffAt.comp x h.smooth,h.pos,fun i hi=>?_⟩
  refine le_trans (L.norm_iteratedFDeriv_comp_left h.smooth (Nat.cast_le.mpr hi)) ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (h.order i hi))
lemma cast_scale (z:ℂ)(h:Brush j u v f x): Brush j (‖z‖*u) v (fun y=> z*(f y:ℂ)) x:= smul_left _ (cast h)
lemma allProd {ι : Type*}(I : Finset ι) (a b : ι→ℝ) (F : ι→E → ℂ) {y:E} (h:∀ i∈I,Brush j (a i) (b i) (F i) y):
    Brush j (∏ i∈I,a i) (∑ i∈I,b i) (fun x=> ∏ i∈I,F i x) y :=by
   classical
   induction I using Finset.induction_on with
   | empty=> simp only [Finset.prod_empty,Finset.sum_empty]; simpa only [norm_one] using! Brush.certified (k:=j) (x:=y) (le_refl (0:ℝ)) (1:ℂ)
   | insert i s hi ht=> simp_rw [Finset.prod_insert hi,Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).paints (ht fun j hj=> h j (Finset.mem_insert_of_mem hj))
section exp
lemma exp_cost (j:ℕ):∃ C : ℝ,1≤C∧∀ z:ℂ, Brush j (C*‖Complex.exp z‖) 1 Complex.exp z:=by
  obtain ⟨c,hc,h⟩:=Brush.neighborhood (f:=Complex.exp) (k:=j) 0 (by fun_prop)
  refine ⟨c,by simpa only [Complex.exp_zero,norm_one] using h.self_of_nhds.bound,fun z=>?_⟩
  let S := fun w=>Complex.exp (w-z)
  have hS : Brush j c 1 S z:= by refine ⟨Complex.contDiff_exp.contDiffAt.comp _ (contDiffAt_id.sub contDiffAt_const),zero_le_one,fun i hi=> ?_⟩; unfold S; rw [normJ,iteratedFDeriv_comp_sub (n:=i),sub_self]; exact h.self_of_nhds.order _ hi
  exact (smul_left (Complex.exp z) hS).shimmy (Eventually.of_forall fun w=>(by unfold S; dsimp only; rw [← Complex.exp_add]; congr 1; ring)) |>.climb (mul_comm ..).le le_rfl
lemma exp_lift {g:E → ℂ}(j : ℕ)(hC : ∀ z:ℂ,Brush j (C*‖Complex.exp z‖) 1 Complex.exp z) {y:E} (hu:Brush j u d g y) (hY:‖Complex.exp (g y)‖≤w) (hc:0≤C): Brush j w ((1+j.factorial*C)*(1+u)*d) (fun v=>Complex.exp (g v)) y:=by
  have h:= hu.pine ((hC _).climb (mul_le_mul_of_nonneg_left hY hc) le_rfl)
  refine ⟨h.smooth,mul_nonneg (mul_nonneg (by positivity) (add_nonneg zero_le_one hu.nonneg)) hu.pos,fun i hi=>?_⟩
  by_cases hi':i=0
  · subst i; simpa only [normJ,norm_iteratedFDeriv_zero,pow_zero,mul_one] using hY
  have hh := (norm_nonneg _).trans hY
  refine (h.order i hi).trans ?_
  rw [show (j.factorial:ℝ)*(C*w) = w*((j.factorial:ℝ)*C) by ring,show (1+(j.factorial:ℝ)*C)*(1+u)*d = (1+(j.factorial:ℝ)*C)*((1+u)*d) by ring,mul_pow (1+(j.factorial:ℝ)*C),mul_assoc w]
  apply mul_le_mul_of_nonneg_left _ hh
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (mul_nonneg (add_nonneg zero_le_one hu.nonneg) hu.pos) _)
  refine (le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hc)) (by omega))
lemma exp_small (j:ℕ) {C:ℝ}(hC : ∀ z:ℂ,Brush j (C*‖Complex.exp z‖) 1 Complex.exp z)(hc:0≤C) :
    let P := 2+j.factorial*(C*Real.exp 1+1)
    0≤P ∧ ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f:E → ℂ)(x:E) (t d:ℝ), Brush j t d f x → t ≤ 1 → Brush j (P*t) d (fun y=>Complex.exp (f y)-1) x:=by
 intro P; refine ⟨add_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (mul_nonneg hc (Real.exp_pos _).le) zero_le_one)),?_⟩
 intro E _ _ f x t d hf ht
 let i:=f x
 have hn : ‖i‖ ≤ 1 := hf.bound.trans ht
 have hg := hC (f x)|>.separating ((Brush.certified zero_le_one (1:ℂ)).climb (by simp : ‖(1:ℂ)‖≤1) le_rfl)
 have he : Brush j (C * Real.exp 1+1) 1 (fun x:ℂ => Complex.exp x-1) (f x) := hg.climb (add_le_add_left (mul_le_mul_of_nonneg_left (by rw [Complex.norm_exp]; exact Real.exp_monotone ((le_abs_self _).trans ((Complex.abs_re_le_norm _).trans hn))) hc) 1) le_rfl
 apply Brush.even hf he ht (show (0:ℝ)≤2 by norm_num)
 exact (le_trans (b:=2*‖i‖) (by rw [← sub_add_cancel (Complex.exp i-1) i]; have hd:=Complex.norm_exp_sub_one_sub_id_le hn; have h:=norm_add_le (Complex.exp i-1-i) i; nlinarith only [h,hd,hn,norm_nonneg i]) (by gcongr;exact hf.bound))
end exp
end YM.Frontier.Tuning.ComplexBrush
