import YM.PertExtension.PlateBounds
import YM.PertExtension.MixedRule

/-! Limits of fully scaled individual curl differences on the inversion regulator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace YM.PertExtension.LatticePT
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Next.Rank.Beamer Air Orb Orbit GaussianScore Function Finset
open scoped ContDiff Topology BigOperators Classical NNReal RealInnerProductSpace
open Projection
variable {G : Gauge} (q : ℕ+)
abbrev magnify (m : ℕ):ℝ := (q.val:ℝ)^m
theorem side_rate {q : ℕ+} (h:1<q.val) (d:ℕ):Tendsto (fun m=> magnify q m ^ d / ((side q m).val:ℝ)) atTop (𝓝 0):=by
   refine squeeze_zero' (Eventually.of_forall (fun m=> by positivity)) (g:=fun m=>epsilon q m) ?_ ((epsilon_zero h).mono_right inf_le_left)
   filter_upwards [eventually_ge_atTop (d+1)] with m hm
   apply (div_le_iff₀ (show 0< ((side q m).val:ℝ) from Nat.cast_pos.mpr (side q m).pos)).mpr
   change ((q.val:ℝ)^m)^d≤((q.val:ℝ)^m)⁻¹ * ((nativePeriod q m:ℕ):ℝ)
   rw [← pow_mul]; unfold nativePeriod; push_cast
   rw [pow_succ]; have hr:0<(q.val:ℝ)^m:=pow_pos (Nat.cast_pos.mpr q.pos) _
   have hQ:1≤(q.val:ℝ) := by exact_mod_cast h.le
   calc
    ((q.val:ℝ)^(m*d)) ≤ (q.val:ℝ)^m^2 := pow_le_pow_right₀ (Nat.one_le_cast.mpr (by omega)) (by nlinarith)
    _ ≤ (8*(q.val:ℝ))*((q.val:ℝ)^m^2):= le_mul_of_one_le_left (by positivity) (show _≥1 from by linarith)
    _ = _:= by change 8*↑q.val*((q.val:ℝ)^m^2)= _; rw [pow_two m]; field_simp

local notation "rateQ" => (Filter.atTop : Filter ℕ)
theorem scale_inv {q : ℕ+} (hq:1<q.val): Tendsto ((magnify q)⁻¹) rateQ (𝓝 0):=(epsilon_zero hq).mono_right inf_le_left
lemma price_scaling {q : ℕ+}{Z : ℕ→E4}{a:E4}(h:1<q.val)(hz:a∈away)(he:Tendsto (fun t=>epsilon q t • Z t) rateQ (𝓝 a)) (d:ℕ): Tendsto (fun t=>magnify q t ^ (4+d) *stature d (Z t) ((side q t).val:ℝ)) rateQ (𝓝 0):= by
  let w t:=magnify q t; let U t:ℝ:=‖w t ^(-1:ℤ) • Z t‖
  have h' (t): 0<w t:=pow_pos (by exact_mod_cast q.pos) _
  have ht:=scale_inv h
  have hs:Tendsto U rateQ (𝓝 ‖a‖):=by simpa [U,w,epsilon, magnify] using he.norm
  let H (t:ℕ):=U t^(d+5)
  have hw: ‖a‖≠0:=norm_ne_zero_iff.mpr hz
  let S t:=((side q t).val:ℝ)
  have hP:= ht.div (hs.pow (d+5)) (pow_ne_zero _ hw)
  have hD := side_rate h (4+d)
  have hy:= (side_rate h (5+d)).mul hs
  have hb:= hP.add (hD.add hy)
  let V t:=‖Z t‖
  have hx:= eventually_ne_nhds hw
  suffices hEq: (fun t=>w t^(4+d)*stature d _ _)=ᶠ[rateQ](fun t=>(w t)⁻¹/(U t^(d+5))+(w t^(4+d)/S t+w t^(5+d)/S t * U t)) by
    apply (Tendsto.congr' hEq.symm ?_ : Tendsto (fun t=>w t^(4+d)*stature d (Z t) _) _ _)
    simpa only [one_div,zero_div,zero_mul,zero_add,Pi.inv_apply] using! hb
  filter_upwards [hs.eventually hx] with t htt; let r:=w t; let v:=V t
  have hg : U t=r⁻¹*v:=by unfold U;rw [zpow_neg_one,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (h' t).le)]
  have hsZ: v≠0 := fun h=>htt (by rw [hg,h,mul_zero])
  have h'':r≠0:=(h' t).ne'
  change r ^ _*(1/v^_ + (1+v)/S t)=r⁻¹/U t^_+(_+_*_)
  rw [hg]; simp_rw [show d+5=(4+d)+1 by omega,show 5+d=(4+d)+1 by omega,pow_succ, inv_mul_eq_div]
  rw [show w t=r from rfl]
  simp only [one_div, mul_pow, inv_pow, mul_inv, div_eq_mul_inv]; field_simp [h''] <;> ring

namespace Projection
variable {q : ℕ+}{x y : ℕ→Cover}{shift : ℕ→Cover}
abbrev PricePath (q : ℕ+) (u v : ℕ→Cover) (t : ℕ) (a b : Degree G) := amount (magnify q t) a * amount (magnify q t) b * mourn (gesture a) (gesture b) (direct G (side q t) (u t) (v t))

theorem captured_step (b x v y: Cover): captured b v x y=mapZ (b-v)+mapZ (x-y):=by unfold captured; rw [show b+x-(v+y)=b-v+(x-y) by abel];ext i; exact Int.cast_add ..

lemma far_direct {u v : ℕ→Cover}{z0:E4}(hq:1<q.val)(hz:z0∈away)(h:Tendsto (fun t=>epsilon q t • mapZ (u t-v t)) rateQ (𝓝 z0))(a b : Degree G) :
 Tendsto (fun t=> PricePath q u v t a b) rateQ (𝓝 (Prayer.gleam a b z0)):= by
    let sQ:=magnify q
    let P t:=captured (u t) (v t) a.point b.point
    let s t:= (sQ t)⁻¹ • P t
    have he : Tendsto s rateQ (𝓝 z0):=by
         have hh := h.add ((scale_inv hq).smul_const (mapZ (a.point-b.point)))
         convert! hh using 2 <;> [skip; simp]
         change (sQ _)⁻¹ • P _ = _;unfold P; rw [captured_step,smul_add];rfl
    have h₀ :∀ᶠ k:ℕ in rateQ,s k∈away:= he.eventually (Maxwell.open_away.mem_nhds hz)
    have ht k : 0<sQ k:=pow_pos (by exact_mod_cast q.pos) _
    have hb k: P k=(sQ k) • s k:= by rw [show sQ k • s k=P k from by unfold s;rw [smul_smul,mul_inv_cancel₀ (ht _).ne',one_smul]]
    have hZ k: ‖P k‖=sQ k*‖s k‖:= by conv_lhs => rw [hb k,norm_smul,Real.norm_of_nonneg (ht k).le]
    have hp:Tendsto (fun t=>‖P t‖) rateQ atTop:= by simp_rw [hZ]; exact (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hq : (1:ℝ) < q)).atTop_mul_pos (norm_pos_iff.mpr hz) he.norm
    let r k:= (sQ k)^(4+(a.degree+b.degree))
    let M k:= mourn (gesture a) (gesture b) (direct G (side q k) (u k) (v k))
    let F:= Prayer.gleam a b
    have hy k: amount (sQ k) a * amount (sQ k) b=r k:=by unfold amount r; rw [← pow_add]; congr 1; omega
    have hh:= price_scaling (Z:=P) hq hz he (a.degree+b.degree)
    let T(k:ℕ):= r k *M k;let D k:= T k-F (s k)
    have htD : Tendsto D rateQ (𝓝 0):=by
        obtain ⟨c,hc,h⟩:=direct_cost a b
        have hw:= hh.mul_const c
        refine squeeze_zero_norm' (a:=fun t=> r t * stature (a.degree+b.degree) (P t) _ * c) ?_ (by simpa only [zero_mul] using! hw)
        filter_upwards [h₀,hp.eventually_ge_atTop 1] with k ht₁ ht₂
        have H: r k * F (P k)=F (s k):= by
           rw [← hy,hb k];exact Prayer.grown a b (ht k) (s k) ht₁ -- args
        unfold D;rw [← H]
        change ‖r k*M k- _‖≤_;rw [←mul_sub,norm_mul,Real.norm_of_nonneg (show 0≤r k by unfold r;positivity)]
        exact (mul_le_mul_of_nonneg_left (show ‖M k-F (P k)‖≤c*_ from h (side q _) _ _ ht₂) (by unfold r;positivity)).trans_eq (by ring)
    have hF:= (Prayer.gleam_diff a b|>.continuousAt (Maxwell.open_away.mem_nhds hz)).tendsto.comp he -- syntax
    convert! htD.add hF using 2 <;> [skip;simp]; change amount (sQ _) a*_ * M _ = _; dsimp [D,T];rw [hy,sub_add_cancel]
end Projection
end YM.PertExtension.LatticePT
