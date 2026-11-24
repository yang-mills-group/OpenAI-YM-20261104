import YM.MSbar.Pole.Symbol.Mark

/-! # Pass marked slot properties through UV operations -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Symbol
open Function Set Filter MeasureTheory Ambient Radial Momentum Age Ray Mellin
open scoped Topology ContDiff Classical BigOperators
variable {I : Type} [Fintype I]

-- equality of finite linear relations on angular momentum paths passes to all scale orders.
lemma one_step {R} {F : ℂ→Cloud I} (h : Meridian (zone R) F) (d : Age) {z} (hz : z∈zone R) (hr : ∀ w∈zone R,2≤(d.alpha w).re+d.safety) (A : Finset I) {n:ℕ} (x y p : External I n) (c l : ℂ)
    (hh : ∀ t:ℝ,F z n (move A t x)= c*F z n (move A t y)+l*F z n (move A t p)) :
    step A d F z n x=c*step A d F z n y + l*step A d F z n p:=by
  let f(i:ℕ) (x:External I n) (t:ℝ):= spill^[i] (augments A n F) z (t,x)
  have hk i w : ContDiff ℝ ∞ (f i w):= contDiff_iff_contDiffAt.mpr fun t=> ((terms Metric.isOpen_ball (puts h n (B:=A)) i).stream.smooth (z,t,w) ⟨hz,mem_univ _⟩).comp (f:=fun t:ℝ=>(z,t,w)) t (by fun_prop)
  have he (i:ℕ) : ∀ t:ℝ,f i x t= c*f i y t+l*f i p t:=by
    induction i with
    | zero=> exact hh
    | succ i ih=>
      intro t; unfold f; simp_rw [iterate_succ_apply'];
      change (∫ s : ℝ in Ioc (0:ℝ) 1, deriv (f i x) (s*t))=c*(∫ s in Ioc (0:ℝ) 1,deriv (f i y) (s*t))+l*∫ s in Ioc (0:ℝ) 1,deriv (f i p) (s*t)
      have hv(s:ℝ): deriv (f i x) s = c*deriv (f i y) s+l*deriv (f i p) s := by
        have hj w:= (((hk i w).differentiable (by simp)) s).hasDerivAt
        exact (((hj y).const_mul c|>.add ((hj p).const_mul l)).congr_of_eventuallyEq (Eventually.of_forall ih)).deriv
      have hl w : Integrable (fun s:ℝ=>deriv (f i w) (s*t)) (volume.restrict (Ioc (0:ℝ) 1)):= (((hk i w).continuous_deriv (by simp)).comp (continuous_id.mul_const t)).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
      simp_rw [hv]; rw [integral_add ((hl y).const_mul c) ((hl p).const_mul l),integral_const_mul,integral_const_mul]
  have hb u := (Ray.carrying Metric.isOpen_ball (terms Metric.isOpen_ball (puts h n (B:=A)) d.safety) d.linear ((d.a:ℂ)-1+d.safety) (fun w hw=>by
    have hv := hr w hw; simp only [Age.alpha,Complex.add_re,Complex.sub_re,Complex.one_re,Complex.natCast_re] at *; linarith)).2 z hz u
  let Q (x:External I n) t:= f d.safety x t * (t:ℂ)^(d.alpha z-1+d.safety)
  have hQ (u:External I n): Integrable (Q u) (volume.restrict (Ioc (0:ℝ) 1)) := by
    unfold Q; rw [show d.alpha z-1+d.safety=d.a-1+d.safety+d.linear*z by unfold alpha; abel]; exact hb u
  have hP (u:External I n): step A d F z n u=(∫ t :ℝ in Ioc (0:ℝ) 1,Q u t)+∑ i∈Finset.range d.safety,(d.increment i z)⁻¹*f i u 0:=area A d z u
  simp_rw [hP,show ∀ t,Q x t=c*Q y t+l*Q p t from fun t=>by unfold Q; rw [he]; ring]
  rw [integral_add ((hQ y).const_mul c) ((hQ p).const_mul l),integral_const_mul,integral_const_mul]
  simp_rw [he,mul_add,mul_left_comm _ c,mul_left_comm _ l,Finset.sum_add_distrib,← Finset.mul_sum]; ring

lemma sweep_shapes {R} {F : ℂ→Cloud I} {U V : Finset I} (h : Meridian (zone R) F) (d : Age) {z} (hz : z∈zone R) (hr : ∀ w∈zone R,2≤(d.alpha w).re+d.safety) {A : Finset I} (hs : Disjoint A V) (hx : Shape U V (F z)) :
    Shape U V (step A d F z) := by
  have he t : Shape U V (fun n x=> F z n (move A t x)):= hx.move_by A hs t
  constructor
  · intro n x y hh
    simpa using (one_step h d hz hr A x y y 1 0 (fun t=>by rw [one_mul,zero_mul,add_zero]; exact (he t).sees n x y hh))
  intro i hi n x; constructor
  · intro a b; simpa only [one_mul] using (one_step h d hz hr A (update x i (a+b)) (update x i a) (update x i b) 1 1 (fun t=>by simp only [one_mul]; exact ((he t).angle i hi n x).add a b))
  intro r a; simpa only [Complex.real_smul,zero_mul,add_zero] using! (one_step h d hz hr A (update x i (r • a)) (update x i a) x r 0 (fun t=>by rw [zero_mul,add_zero,← Complex.real_smul]; exact ((he t).angle i hi n x).smul r a))

def Acts (U V : Finset I) (F:ℂ→Cloud I):= ∀ᶠ z in approaching, Shape U V (F z)
lemma whirl {F : ℂ→Cloud I} {U V A:Finset I} {k} (h:Vortex k F)(p:Acts U V F) (d:Age)(hv:Disjoint A V) : Acts U V (step A d F):=by
  obtain ⟨R,G,hr,H,hh⟩:=h
  obtain ⟨S,hS,hp⟩:=Metric.mem_nhds_iff.mp d.safely
  unfold Acts
  filter_upwards [neighborhood (lt_min hr hS),p] with z hz hs
  have hk : z∈slit R:=⟨zone_le (min_le_left ..) hz.1,hz.2⟩
  have hz' : z≠0:=hk.2
  have he : G z=z^k • F z:= by funext n x; exact (hh z hk n x).symm
  have ht := sweep_shapes (H.mono (zone_le (min_le_left ..))) d hz.1 (fun x hx=> hp (zone_le (min_le_right ..) hx)) hv (by rw [he]; exact hs.scale (z^k))
  rw [show step A d F z=(z^k)⁻¹ • step A d G z by
    funext n x; exact finite_mul A d H n x x hk.1 _ (fun r=> by rw [he]; change _=(z^k)⁻¹*(z^k*_); rw [inv_mul_cancel_left₀ (pow_ne_zero k hz')])]
  exact ht.scale _
lemma Acts.sum {U V:Finset I} {Z:Type*} (s:Finset Z)(F: Z→ℂ→Cloud I)(h:∀ i∈s,Acts U V (F i)):Acts U V (∑ i∈s,F i):=by
  unfold Acts; filter_upwards [eventually_all_finset s|>.mpr h] with z hz; rw [Finset.sum_apply]; exact Shape.sum _ _ hz
end YM.MSbar.Pole.Symbol
