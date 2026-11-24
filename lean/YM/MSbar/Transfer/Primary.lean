import YM.MSbar.Transfer.Toll

/-! Transfer endpoint with vanishing theorem; independence of choices by Mellin cost estimator. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Transfer
open Complex Metric Filter Set MeasureTheory Function
open Dim.Dual
open scoped Topology ContDiff BigOperators Classical
variable {j m n : ℕ} {f g : ℂ→ℂ} {X : Type} [TopologicalSpace X] {K:Set X} {F G:ℂ×X→ℂ} {C T : ℝ} {z : ℂ}
lemma analytic_Γ (z : ℂ) : AnalyticAt ℂ Γ z:= by
   apply Differentiable.analyticAt
   let f(z:ℂ):= (↑Real.pi:ℂ)^z
   exact (differentiable_id.const_cpow (Or.inl (by exact_mod_cast Real.pi_ne_zero) ) : Differentiable ℂ f).mul differentiable_one_div_Gamma -- Γ product? order!
lemma main_zero (hf : Differentiable ℂ f) (hb : ∀ z:ℂ,T ≤ z.re → ‖f z‖ ≤ toll j m n C z)(hh : ∀ᶠ n:ℕ in atTop,f n=0): f=0:=by
   obtain ⟨k,ht,he⟩:= ((eventually_ge_atTop 1).and (tendsto_natCast_atTop_atTop.eventually_ge_atTop T)).exists
   let p(z:ℂ):=z+k; let D(z:ℂ):= Γ z^j * Complex.exp (m*z)* z^n; let g(z):= f (p z)/D (p z)
   have hl(z:ℂ)(hz:z∈half):0<(p z).re ∧ T ≤ (p z).re:=by
       unfold p; change 0<z.re at hz; simp only [add_re,natCast_re]
       exact ⟨add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg _),by linarith⟩
   have hd(z:ℂ)(hz:0<z.re):D z≠0:=mul_ne_zero (mul_ne_zero (pow_ne_zero j (gamma hz)) (Complex.exp_ne_zero _)) (pow_ne_zero n (by intro h; simp [h] at hz))
   have hp : Differentiable ℂ p:= differentiable_id.add_const _
   have hD : Differentiable ℂ D := by
       unfold D; have hh : Differentiable ℂ Γ:= fun z=>(analytic_Γ z).differentiableAt
       fun_prop
   have hg : DifferentiableOn ℂ g half:= (hf.comp hp).differentiableOn.div (hD.comp hp).differentiableOn fun z hz=> hd _ (hl z hz).1
   have hM(z:ℂ)(hz:z∈half): ‖g z‖≤ C:=by
       unfold g; rw [norm_div]; apply (div_le_iff₀ (norm_pos_iff.mpr (hd _ (hl z hz).1))).mpr
       exact (hb (p z) (hl z hz).2).trans_eq (by unfold toll D; simp [Complex.norm_exp,mul_re,mul_assoc])
   have hK : Tendsto (fun n:ℕ=>n+k) atTop atTop:= tendsto_atTop_mono (f:=id) (fun n=> by change n ≤ n+k;omega) tendsto_id
   have hh' : ∀ᶠ n:ℕ in atTop,g n=0:=by filter_upwards [hK.eventually hh] with n H; unfold g p; rw [← Nat.cast_add,H,zero_div]
   apply real_unique (T:=(k:ℝ)+1) hf; intro x hx; have ht:=real_zero hg hM hh' (show 1 ≤ x-k by linarith only [hx]); have hT : (p (↑(x-k:ℝ):ℂ))=(↑x:ℂ):=by unfold p; push_cast; ring
   have he:0 < (x:ℂ).re:= by change 0<x; linarith [Nat.cast_nonneg k (α:=ℝ)]
   unfold g at ht; rw [hT] at ht; exact (div_eq_zero_iff.mp ht).resolve_right (hd _ he)
lemma Centered.price (hF : Centered j F K)(hG : Centered j G K) {x:X} (hx:x∈K) (hf : Differentiable ℂ (fun z=> F (z,x))) (hg:Differentiable ℂ (fun z=>G (z,x))) (he: ∀ᶠ m:ℕ in atTop,F (m,x)=G (m,x)) (z:ℂ) : F (z,x)=G (z,x):=by
   obtain ⟨t,C,-,-,m,n,h⟩:= (hF.sub hG).books 0
   apply sub_eq_zero.mp; exact congr_fun (main_zero (hf.sub hg) (fun z hz=> h z hz x hx) (he.mono fun y hy=> sub_eq_zero.mpr hy)) z
lemma Market.price (hF : Market j F)(hG : Market j G) (x:X) : Differentiable ℂ (fun z=> F (z,x))→ Differentiable ℂ (fun z=> G (z,x))→ (∀ᶠ m:ℕ in atTop,F (m,x)=G (m,x)) → ∀ z:ℂ,F (z,x)=G (z,x):=
    (hF _ isCompact_singleton).price (hG _ isCompact_singleton) (mem_singleton x)
end YM.MSbar.Transfer
