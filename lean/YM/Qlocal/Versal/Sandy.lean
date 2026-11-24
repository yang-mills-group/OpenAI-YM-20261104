import YM.Qlocal.Versal.Rain
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet.Vase
open Function Filter Lattice Laurent RG Wilson Stationary Lasso Zora Work.F02 Metric
open Marker Multi Finset
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
open ConnectedActivityE6.Blaze ConnectedActivityE6
variable {V:Type}[DecidableEq V] {ι E:Type} {G:Gauge}{k n j r i:ℕ} {c:Side} {d t a v u C:ℝ}{R:Census V}
variable (l:Lattice.Order){s:Senses R}(A:Vase s G n)(x:Site c)(W:Config G c)(o:Site c)(p:BudgetPoint)
set_option quotPrecheck false
local notation "θ"=> p.threshold
local notation "t₀"=> p.supportExponent
local notation "ξ"=> A.momentum
noncomputable abbrev dew (k r:ℕ) (G:Gauge)(q s:ℕ):= bloom G r*q+(1+velocity G s (rune G k))^k * rate G k r
noncomputable def basin (G:Gauge)(P k m r:ℕ)(g:ℕ):= (2+(g:ℝ))^(P*k) * shoot G k r m 1
lemma basin_nn (G:Gauge)(P k m r:ℕ)(g:ℕ):0≤ basin G P k m r g:= mul_nonneg (pow_nonneg (by positivity) _) (weather_ge _ _ _ _ _ _ (rune_pos ..).le)
def fall (k p m:ℕ):= p*k+(k+1)*m
lemma cloudy (G:Gauge)(k r i:ℕ)(hd:0≤d): cloud G k r d i ≤ cloud G k r d 1 * (1+i:ℝ)^(k+1) := by
 let w:= velocity G 1 d
 unfold cloud; let y:ℝ:= 1+i; have hy : 1≤ y:=le_add_of_nonneg_right (Nat.cast_nonneg _); have he : 0≤w:= by unfold w velocity; have hh:=royalty_ge G; positivity
 have hx:1+velocity G i d≤ (1+w)*y:= by rw [show velocity G i d=(i:ℝ)*w by unfold w velocity; ring]; unfold y; linarith only [he,Nat.cast_nonneg (α:=ℝ) i]
 have hF:= (pow_le_pow_left₀ (show 0≤1+velocity G i d from by unfold velocity; have hh:=royalty_ge G; positivity) hx k); rw [mul_pow] at hF
 have ht:=rated G k r; have hm:(i:ℝ) ≤ (1+(i:ℝ))^(k+1):= (le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ hy (by omega)) -- lemma shape check
 have hg:=springGe G r; push_cast; rw [mul_one,add_mul]; refine add_le_add (mul_le_mul_of_nonneg_left hm (zero_le_one.trans hg)) ?_
 refine (mul_le_mul_of_nonneg_right hF (zero_le_one.trans ht)).trans ?_; rw [mul_right_comm ((1+w)^k)]; refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy (by omega)) (mul_nonneg (by positivity) (zero_le_one.trans ht))
open Extra.Iteration
lemma flood_control (k r m i q:ℕ)(G:Gauge) : flood p k r m G i (i+q) ≤ basin G p.power k m r q * (1+i:ℝ)^fall k p.power m:= by
 unfold basin flood shoot weather fall; -- issue shoot before weather
 push_cast
 let x:ℝ:=2+q; let y:ℝ:=1+i
 have hf:1+(i:ℝ)+(i+q) ≤ x*y := by unfold x y; nlinarith only [Nat.cast_nonneg (α:=ℝ) i,Nat.cast_nonneg (α:=ℝ) q]
 have hd:=rune_pos G k; have hh:= cloudy G k r i hd.le
 refine le_trans (mul_le_mul (pow_le_pow_left₀ (by positivity) hf _) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (fog G k r i hd.le) hh m) (by positivity)) (mul_nonneg (pow_nonneg (fog G k r i hd.le) _) (by positivity)) (pow_nonneg (mul_nonneg (by unfold x; positivity) (by unfold y; positivity)) _)) ?_; unfold x y
 apply le_of_eq; rw [mul_pow,mul_pow,pow_add (1+(i:ℝ)) (p.power*k),pow_mul (1+(i:ℝ)) (k+1)]; ring -- ring handles α powers?
-- prices at runtime.W.Strong.P.Ewor.Horizon engulf Ξ support costs
noncomputable abbrev Sus (p:BudgetPoint)(r:ℕ)(i:ℕ) := A.sizeC*p.threshold^n*flood p p.order r n G A.momentum (A.momentum+i)
noncomputable def humid (G:Gauge)(P k m r q i:ℕ)(t a:ℝ):= basin G P k m r q * momentPrice (fall k P m) a * Real.exp (t*i)
lemma humid_nn (G:Gauge)(P k m r q i:ℕ)(t:ℝ)(ha:0<a):0≤humid G P k m r q i t a:= mul_nonneg (mul_nonneg (basin_nn ..) (momentPrice_pos _ ha).le) (Real.exp_nonneg _)
local notation "I₀"=> humid G p.power p.order n
-- parameter `t` any explicit tariff exponent for Ledger, not p.exponent. true width allocation a, incidence, exterior weighting, reserve u.
variable {X:Support c}{q:ℕ}
lemma Suspend (X' : Carrier l A x i q p.B X)(r:ℕ): 0 ≤ Sus A p r q ∧ p.Regular X (A.read x r) ∧ ∀ o∈ X,p.supBounds o X (A.read x r) (Sus A p r q) := by
 let h(o:Site c)(hi:o∈X):= A.consulted l x o p r (X'.reach o hi); exact ⟨(h x (X'.used ..)).1,AnalyticBridge.VerifiedReset.reg_larger (A.autumn ..) X'.complete,fun o hi=>AnalyticBridge.VerifiedReset.sup_larger (h o hi) X'.complete⟩
local notation "ℓ"=> p.order
lemma economical (H:Carrier l A x i q p.B X)(r:ℕ) (ha:0<a)(he:0≤t)(hs:t/p.B≤d) : Sus A p r q * Real.exp (t*coverNumber p.B X+u*A.momentum) ≤ p.threshold^n * humid G p.power ℓ n r q i t a * A.fare (d+a+u) := by
 have hh: Real.exp (t*coverNumber p.B X+u*ξ) ≤ Real.exp (t*i)* Real.exp ((d+u)*ξ):= by
   have hp:t*↑(coverNumber p.B X) ≤ t*(i:ℝ)+d*ξ:= by
     let v:ℝ:=ξ; let w:ℝ:= p.B; have hw:0<w:= Nat.cast_pos.mpr p.B_pos; have hy: (coverNumber p.B X:ℝ) ≤ i+v/w:= by field_simp; apply (le_trans (b:=w*i + v) _ (by linarith)); rw [mul_comm]; unfold w v; exact_mod_cast H.cost
     refine (mul_le_mul_of_nonneg_left hy he).trans ?_; rw [mul_add]; apply add_le_add_right; rw [← mul_div_assoc, mul_comm t, mul_div_assoc,mul_comm]; exact mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _)
   rw [← Real.exp_add]; apply Real.exp_monotone; linarith only [hp]
 let K:ℝ:= basin G p.power ℓ n r q; let M:=momentPrice (fall ℓ p.power n) a; have hK:0≤K:= basin_nn ..
 have h1 : flood p ℓ r n G ξ (ξ+q) ≤ K*(M*Real.exp (a*ξ)):= (flood_control p ℓ r n _ q G).trans (mul_le_mul_of_nonneg_left (spendMoment _ ha (Nat.cast_nonneg _)) hK)
 unfold Sus; apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_left h1 (mul_nonneg A.nn_size (pow_nonneg p.threshold_pos.le _))) hh (Real.exp_nonneg _) ?_) ?_; swap; · exact le_of_eq (by unfold K M humid fare; rw [show (d+a+u)*↑ξ= a*ξ+(d+u)*ξ by ring,Real.exp_add]; ring)
 exact (mul_nonneg (mul_nonneg A.nn_size (pow_nonneg p.threshold_pos.le _)) (mul_nonneg hK (mul_nonneg (momentPrice_pos _ ha).le (Real.exp_nonneg _))))
end YM.Qlocal.Quipu.Sonnet.Vase
