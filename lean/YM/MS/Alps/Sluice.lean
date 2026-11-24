import YM.MS.Alps.Billow
/-!
# Homogeneity of primitive radial operation as tested on ports

No constraint net at residual (orientation tree). Arc.Θ independent m yields factor.
 Real measure n axes. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum
open Momentum Metric
open scoped Topology ContDiff Pointwise
variable {G:Gauge}{I A B E P:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
  {m:ℕ}
variable {s:ℝ} {a b:ℂ} {f g: Tree E ℂ}
lemma stock_dr (x:E)(h:ContDiff ℝ ∞ f)(hk:ContDiff ℝ ∞ g)(hp:∀ t,f (t,x)=b*g (exp s*t,x))(t:ℝ): Arc.d f (t,x)=b*(exp s:ℂ)*Arc.d g (exp s*t,x):= by
   obtain hx:= dr h x t; rw [funext hp] at hx; apply hx.unique; convert! (((dr hk x (exp s*t)).scomp t ((hasDerivAt_id' t).const_mul (exp s))).const_mul b) using 1 -- order argument he type
   simp [mul_assoc,Complex.real_smul]
lemma crop (x:E)(h:ContDiff ℝ ∞ f)(hk:ContDiff ℝ ∞ g)(hp:∀ t,f (t,x)=b*g (exp s*t,x))(t:ℝ): chop f (t,x) = b*(exp s:ℂ)^2* chop g (exp s*t,x):=by
   unfold chop; simp_rw [stock_dr x (fresh h) (fresh hk) (stock_dr x h hk hp), show ∀ a,exp s*(a*t)=a*(exp s*t) from fun a=> mul_left_comm ..]; rw [intervalIntegral.integral_const_mul]; ring
lemma prunes (x:E)(h:ContDiff ℝ ∞ f)(hk:ContDiff ℝ ∞ g)(hp:∀ t,f (t,x)=b*g (exp s*t,x))(n:ℕ)(t:ℝ): pruning n f (t,x) = b * (exp s:ℂ) ^ (2*n)* pruning n g (exp s*t,x):=by
   induction n generalizing f g b with| zero=>simp [Arc.met,hp]| succ n ih=> change pruning n _ _=_; rw [ih (c_chop h) (c_chop hk) (crop x h hk hp)]; simp only [mul_add,pow_add,mul_one]; unfold pruning; rw [Function.iterate_succ, Function.comp_apply]; ring -- shape
lemma amount_inv (a:ℂ)(t:ℝ): (amount a t)⁻¹=amount (-a) t:= by rw [amount, amount,mul_neg,Complex.exp_neg]
lemma candle (t:ℝ)(ht:0<t)(a:ℂ)(s:ℝ): cloud a (exp s*t)=amount (2*a+1) s*cloud a t:=by rw [cloud,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) ht.le,Complex.cpow_def_of_ne_zero (x:= ((Real.exp s:ℝ):ℂ)) (by exact_mod_cast (exp_pos s).ne'), ← Complex.ofReal_log (exp_pos s).le,Real.log_exp]; rfl
lemma group_volume (s:ℝ)(L:ℝ→ℂ): (∫ x,L (exp s*x) ∂μhalf)=(exp s)⁻¹ • ∫ x,L x ∂μhalf:= by
    apply Eq.trans ( Measure.setIntegral_comp_smul volume L (Ioi 0) (exp_pos s).ne'); have he: exp s • Ioi (0:ℝ)=Set.Ioi (0:ℝ):= by
        ext x; constructor; · rintro ⟨i,hi,rfl⟩; exact mul_pos (exp_pos _) hi
        intro hx; exact ⟨(exp s)⁻¹*x,mul_pos (inv_pos.mpr (exp_pos _)) hx, show exp s*((exp s)⁻¹*x)=x by field_simp⟩
    simp [he,μhalf]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma asset (x:E)(hp:∀ t,f (t,x)=b*g (exp s*t,x))(a:ℂ): fetching f (cloud a) x= amount (-(2*a+1)) s*(Real.exp s:ℂ)⁻¹*b*fetching g (cloud a) x:= by
    unfold fetching; let X(t:ℝ):= fetchP (cloud a) g t x; let k:= amount (2*a+1) s; have he : k≠0:= Complex.exp_ne_zero _
    have ht(t:ℝ)(ht:0<t): fetchP (cloud a) f t x= k⁻¹*b* X (exp s*t):= by unfold fetchP X k; rw [hp]; unfold fetchP; rw [candle t ht]; simp only [smul_eq_mul]; unfold k at he; field_simp
    refine Eq.trans (integral_congr_ae (Eventually.mono (ae_restrict_mem measurableSet_Ioi) (fun t h=> ht t h))) ?_; rw [integral_const_mul, group_volume]; unfold k X; rw [amount_inv,Complex.real_smul,Complex.ofReal_inv]; ring
lemma amount_power (s:ℝ)(n:ℕ): (rexp s:ℂ)^n=amount (n:ℂ) s:= by rw [← Complex.ofReal_pow,← Real.exp_nat_mul, ← Complex.ofReal_natCast, amount_mint]
lemma estimate (x:E)(h: ContDiff ℝ ∞ f)(hk:ContDiff ℝ ∞ g)(hp:∀ t,f (t,x)=b*g (exp s*t,x))(a:ℂ)(m:ℕ): coreC (cloud a) m f x= amount (-(2*a) + 2*m) s * b* coreC (cloud a) m g x:= by
   have hP(u:Tree E ℂ)(hu:ContDiff ℝ ∞ u)(j:ℕ): ContDiff ℝ ∞ (pruning j u):= by induction j with | zero=>exact hu| succ n ih=> rw [spent]; exact c_chop ih
   unfold coreC; rw [Pi.smul_apply, asset x (prunes x h hk hp (m+1))];
   let V(a:ℂ):=amount a s; have hh : (Real.exp s:ℂ)=amount 1 s:= by convert amount_power s 1 <;> simp
   rw [amount_power,hh,amount_inv,Pi.smul_apply, show amount (-(2*a)+(2*(m:ℂ))) s = amount (-(2*a+1)) s* amount (-1) s* amount (2*(m+1:ℕ):ℕ) s by rw [← amount_add,← amount_add]; congr 1; push_cast; ring]; simp only [Complex.real_smul]; ring
end YM.MS.Alps
