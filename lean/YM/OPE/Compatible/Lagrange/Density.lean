import YM.OPE.Compatible.Lagrange.Holes
import YM.OPE.Compatible.Signals.Credited
/-! Center point price from a badly normalized analytic bound and a scale-independent aligned price on a thick punctured grid -/
set_option autoImplicit false
noncomputable section
namespace YM.FrameRead
open Function Filter Metric Polynomial Finset OPE
open scoped BigOperators Topology
variable {δ R c g : ℝ}{k n:ℕ}{B:Type}{ψ:Filter B}{T s p:B→ℝ}
-- multiplier t paid within absol bound. use f on disk.
def Shines (R A:ℝ)(f:ℝ→ℂ) := ∃ g:ℂ→ℂ,DifferentiableOn ℂ g (closedBall 0 R)∧(∀ x:ℝ,|x|≤R→ g (x:ℂ)= f x)∧ ∀ z:ℂ, ‖z‖=R→ ‖g z‖ ≤ A
lemma thicker {t δ u:ℝ}(a:Finset ℝ) {f:ℝ→ℂ}(x:ℝ) (ht:Shines R c f)(hp:0<R)(hq :0 ≤ t)(hδ:0<δ)(ha:a.card<k) (hk:(↑n+1:ℝ)*(2*(k:ℝ)*δ) ≤ R/3)(hf:∀ x':ℝ,|x'|≤R/3 →(x'∉a)→ (∃ i:ℤ, x'+x=(i:ℝ)*δ) → t*‖f x'‖ ≤ u): t*‖f 0‖ ≤ t*c*(1/2:ℝ)^(slice n).card + (slice n).card*u:=by
   obtain ⟨y,hy,hc,hY⟩:=ht
   obtain ⟨b,hb,hr,he⟩:=disjoint_grid (s:=a) ha hδ x
   let w:= 2*(k:ℝ)*δ; have hj : 0 < k:=Nat.zero_le a.card|>.trans_lt ha; have hw:0 < w:=by unfold w; positivity
   have hz:b≤ w/2:= hr.trans_eq (by unfold w; ring)
   rw [← hc 0 (by simp [hp.le]), Complex.ofReal_zero]; refine dot_price hq hw hb hz hp hk hy hY (fun i hi=>?_); let x':ℝ:=i*w+b; have hi':|x'|≤R/3:=by simpa only [pin, Complex.norm_real,Real.norm_eq_abs] using fits_pin hw hb hz hk i hi
   change t* ‖y (x':ℂ)‖ ≤ _; rw [hc _ (hi'.trans (by linarith only [hp] : R/3 ≤ R))]; exact hf x' hi' (he i).1 (he i).2
lemma count (n:ℕ) : (slice n).card=2*n+1:=by rw [slice,Int.card_Icc]; omega
variable (hr:Tendsto T ψ atTop)(hR: 0 < R)
include hr hR
lemma knurls (k:ℕ)(hS:Score ψ T p)(c g:ℝ):∃ v:B→ℝ, Score ψ T v∧ ∀ᶠ i in ψ,∀ (f:ℝ→ℂ)(t:ℝ),Shines R (Real.exp (c*T i)) f → 0≤t → t≤ Real.exp (g*T i) → ∀ x δ:ℝ,0<δ→ δ ≤ 1/T i^2 → ∀ a:Finset ℝ,a.card < k → (∀ x':ℝ,|x'|≤ R/3 → x'∉a → (∃ u:ℤ,x'+x=(u:ℝ)*δ)→ t*‖f x'‖ ≤ p i) → t * ‖f 0‖ ≤ v i:=by
   let L:= max ((g+c)/Real.log 2) 1; have hL:0 < L:= lt_of_lt_of_le zero_lt_one (le_max_right ..); let n (i:B):ℕ:= Nat.ceil (L*T i); let m(i:B):ℝ:= (slice (n i)).card
   have he:∀ᶠ i in ψ,0<T i:= hr.eventually_gt_atTop 0
   have hJ: Score ψ T (fun i=> (n i:ℝ)) := ((Score.steady _ hr).product (Score.time hr)).ceiling hr (he.mono fun _ he=>(mul_pos hL he).le); have hv: Score ψ T m := by
       refine (((Score.steady (2:ℝ) hr).product hJ).plus (Score.steady (1:ℝ) hr) hr).congr ?_
       filter_upwards with i; unfold m; rw [count]; push_cast; rfl
   have hl:Tendsto (fun i=>(L*T i+2)*(2*(k:ℝ)*(1/(T i)^2))) ψ (𝓝 0):=by
       have hf:=tendsto_inv_atTop_zero.comp hr; have hz:Tendsto (fun i=> ((T i)⁻¹)) ψ (𝓝 0):=hf; have hp:=hz.pow 2
       have h:Tendsto (fun i=> (L*(T i)⁻¹+2*((T i)⁻¹)^2)*(2*(k:ℝ))) ψ (𝓝 0):=by simpa using (((hz.const_mul L).add (hp.const_mul 2)).mul_const (2*(k:ℝ)))
       apply h.congr'; filter_upwards [he] with i hi; field_simp
   refine ⟨fun i=>1+m i*p i,(Score.steady _ hr).plus (hv.product hS) hr,?_⟩
   filter_upwards [he,hl.eventually (ge_mem_nhds (div_pos hR (by norm_num : (0:ℝ)<3)))] with i hi hk f t hF hp hh x δ ha hw a hA hM
   have hb: (↑(n i)+1:ℝ)*(2*(k:ℝ)*δ) ≤ R/3:=by
      apply le_trans _ hk; exact mul_le_mul (by linarith only [(show (n i:ℝ)<L*T i+1 from Nat.ceil_lt_add_one (mul_pos hL hi|>.le))]) (mul_le_mul_of_nonneg_left hw (by positivity)) (by positivity) (by positivity)
   refine (thicker a x hF hR hp ha hA hb hM).trans (add_le_add ?_ (le_of_eq rfl))
   have h: Real.exp (g*T i)*Real.exp (c*T i) ≤ (2:ℝ)^((slice (n i)).card):=by
       have h₀:0 < Real.log 2:=Real.log_pos one_lt_two
       have hp:(g+c) ≤ L*Real.log 2:= (div_le_iff₀ h₀).1 (le_max_left ..); have hf:L*T i ≤ (m i:ℝ):= (Nat.le_ceil _).trans (by unfold m; rw [count]; exact_mod_cast (show n i ≤ 2*n i+1 by omega))
       rw [← Real.exp_add, ← Real.exp_log (show 0 < (2:ℝ)^((slice (n i)).card) by positivity),Real.log_pow]
       exact Real.exp_monotone (by change _ ≤ m i *_; nlinarith only [hp,hf,mul_le_mul_of_nonneg_right hf h₀.le, mul_le_mul_of_nonneg_right hp hi.le])
   apply (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)).trans h) (by positivity : 0≤(1/2:ℝ)^((slice (n i)).card))).trans_eq
   rw [← mul_pow]; norm_num
end YM.FrameRead
