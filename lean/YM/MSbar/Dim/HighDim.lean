import YM.MSbar.Dim.Twice

/-! In high-dimensional half-plane, drop stage and collect weights. Pairs units. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Dim
open Function Set Filter Metric Complex MeasureTheory Symbol
open scoped Topology ContDiff BigOperators Classical NNReal
variable {m n : ℕ} {K H : ℝ} {z : ℂ} {f g : Hat (m+1)→ℂ}
namespace Dual
abbrev Cells (m:ℕ) := Hat m × ℝ
def collar (m:ℕ)(K:ℝ) : Set (Cells m) := closedBall (0:Hat m) K ×ˢ Icc 0 (K^2)
lemma collar_compact (m:ℕ)(K:ℝ) : IsCompact (collar m K) := IsCompact.prod (isCompact_closedBall ..) isCompact_Icc
def seed (q: Cells m):= push m (q.1,Real.sqrt q.2)
def Γ (z:ℂ):= (↑Real.pi:ℂ)^z*(Gamma z)⁻¹
def weight (z:ℂ) (q: Cells m):= (↑q.2:ℂ)^(z-1)
lemma weight_c (hz:1<z.re): Continuous (weight (m:=m) z):= (continuous_ofReal_cpow_const (by simpa using hz : 0<(z-1).re)).comp continuous_snd
lemma seed_c : Continuous (seed (m:=m)):= tame_push.1.continuous.comp (continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd))
lemma gamma (hz:0<z.re): Γ z ≠0:= mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast Real.pi_ne_zero))) (inv_ne_zero (Gamma_ne_zero_of_re_pos hz))

lemma lifted (hp:Packed m K f)(hz : 1<(z-m).re): plate z f= Γ (z-m)*(∫ a in collar m K,weight (z-m) a*f (seed a)):=by
   let s:=z-(m:ℂ);let w(u:ℝ):=(↑u:ℂ)^(s-1); let J:=Icc 0 (K^2)
   have he(u):face z f u=Γ s*(∫ t in J,w t*f (seed (u,t))) := by
        unfold face; rw [actual (hp.radius u) (zero_lt_one.trans hz),support_mellin (hp.radius u) (U:=K^2) le_rfl,intervalIntegral.integral_of_le (sq_nonneg K)]; unfold J; rw [integral_Icc_eq_integral_Ioc]; rfl
   change plate z f= Γ s * ∫ a in collar m K,weight s a*f (seed a) ∂Measure.prod volume volume
   unfold collar;rw [hp.read,setIntegral_prod]; simp_rw [he]; exact integral_const_mul ..
   exact ((weight_c hz).continuousOn.mul ((hp.smooth.1.continuous.comp seed_c).continuousOn)).integrableOn_compact (collar_compact m K)

variable {T:ℕ→Type} {S:Motion T} {F:Dual T} (h:Uses S K F) (x:T m)
def load (F:Dual T)(S:Motion T)(x:T m) (q:Cells m×Cells (m+1)):= F (m+2) ((above S (above S x),up (m+1) (seed q.1)),seed q.2)
abbrev district (m:ℕ)(K:ℝ) := collar m K ×ˢ collar (m+1) K
include h
lemma load_c : Continuous (load F S x):= (h.ready _ (above S (above S x))).1.continuous.comp (Continuous.prodMk ((up (m+1)).continuous.comp (seed_c.comp continuous_fst)) (seed_c.comp continuous_snd))
-- delta parameter = z-(m+3)
lemma factor (hs : m+3 ≤ z.re): tower S F z m x =
    Γ (z-m)*Γ (z-(m+1:ℕ))*(∫ a in district m K,weight (z-m) a.1*weight (z-(m+1:ℕ)) a.2*load F S x a):=by
   let L:=Γ (z-m); let P:=Γ (z-(m+1:ℕ));let s:=z-(m:ℂ); let u:=z-(m+1:ℕ)
   let R:=district m K;let y:= load F S x; let f(a:Cells m×Cells (m+1)):=weight s a.1*weight u a.2*y a
   have hs' :1<s.re:=by unfold s; simp only [sub_re,natCast_re];linarith only [hs]
   have hu' :1<u.re:=by unfold u; simp only [sub_re,natCast_re];push_cast;linarith only [hs]
   have hc : Continuous f := (((weight_c hs').comp continuous_fst).mul ((weight_c hu').comp continuous_snd)).mul (load_c h x)
   have hZ (v:Cells m):weight s v*inner S F z (m+1) (above S x,seed v)=P* (∫ w in collar (m+1) K,f (v,w)):=by
       unfold inner request;rw [lifted (h.packed _) hu']; change weight s v*(P*(∫ w in _,weight u w * y (v,w))) = _; rw [mul_left_comm,← integral_const_mul]; simp [f,mul_assoc]
   unfold tower request; rw [lifted (h.packed2 z x) hs']
   change L * (∫ a in _,weight s a * _)= L*P* ∫ a in R,f a ∂Measure.prod volume volume
   unfold R district; rw [setIntegral_prod]
   · rw [mul_assoc,← integral_const_mul (μ:=volume.restrict (collar m K)) P]; exact congr_arg (L* ·) (integral_congr_ae (Eventually.of_forall hZ))
   exact hc.continuousOn.integrableOn_compact ((collar_compact m K).prod (collar_compact ..))

omit h in
def wick (a:Cells m × Cells (m+1)):= a.1.2*a.2.2

def payload (F:Dual T)(S:Motion T)(x:T m)(a:Cells m × Cells (m+1)):= (a.1.2 :ℂ)^2 * (a.2.2:ℂ) * load F S x a
lemma payload_c : Continuous (payload F S x):= (((continuous_ofReal.comp (continuous_snd.comp continuous_fst)).pow 2).mul (continuous_ofReal.comp (continuous_snd.comp continuous_snd))).mul (load_c h x)
lemma clean (hs:m+3 ≤ z.re): tower S F z m x=Γ (z-m)*Γ (z-(m+1:ℕ))*(∫ a in district m K,(wick a : ℂ)^(z-m-3)*payload F S x a):=by
   let s:=z-(m:ℂ)-3;let t:=z-(m+1:ℕ); have he:t-1=s+1:=by unfold t s; push_cast; ring
   have hp:z-m-1=s+2:=by unfold s; ring
   rw [factor h x hs]; congr! 1
   refine setIntegral_congr_fun ((collar_compact m K).prod (collar_compact ..)).measurableSet (fun w hw=> ?_)
   have hA : 0 ≤ s.re:=by unfold s; norm_num; linarith only [hs]
   let r (u:ℝ):ℂ:=u; have hu (a:ℝ)(ha:0≤a) (n:ℕ)(hN:0<n): (r a)^(s+n)= (r a)^s * (r a)^n:=by
       rcases eq_or_ne a 0 with rfl|h
       · unfold r; rw [Complex.ofReal_zero]; have ht : 0<(n:ℝ):= by exact_mod_cast hN
         have hk:s+(n:ℂ)≠0:= fun he => absurd (congr_arg Complex.re he) (by simp; linarith only [hA,ht])
         rw [zero_cpow hk,zero_pow hN.ne',mul_zero]
       unfold r; rw [cpow_add _ _ (by exact_mod_cast h),cpow_natCast]
   let a:=w.1.2; let b:=w.2.2;have ha:0≤a:= hw.1.2.1; have hb:0≤b:=hw.2.2.1
   change r a ^ (z-m-1)* r b^(t-1)*_=r (a*b)^s * (r a^2*r b*_);rw [hp,he]
   have h1:=hu a ha 2 (by norm_num); have h2:=hu b hb 1 zero_lt_one; norm_num at h1 h2; rw [h1,h2]; unfold r; rw [ofReal_mul,mul_cpow_ofReal_nonneg ha hb]; ring
end Dual
end YM.MSbar.Dim
