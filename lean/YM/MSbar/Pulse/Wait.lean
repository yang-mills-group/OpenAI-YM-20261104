import YM.MSbar.Pulse.Grind
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery.Portal
open Function Filter MeasureTheory Cacao PowerSeries Finset
open scoped Topology Classical BigOperators
local notation "G"=> PowerSeries ℝ
local notation "µ"=>PowerSeries.coeff
variable {g h : PowerSeries ℝ}{α ε p K A B D X σ S t b r :ℝ}{n m : ℕ}
-- pointwise
lemma exp_rate {x y a : ℝ}(hx:x ≤ a)(hy:y ≤ a):|Real.exp x-Real.exp y|≤ Real.exp a*|x-y|:=by
    refine (convex_Iic (𝕜:=ℝ) a).norm_image_sub_le_of_norm_deriv_le (fun i hi=> Real.differentiable_exp _) (fun i hi=> ?_) (show y∈Set.Iic a from hy) hx
    rw [Real.deriv_exp, Real.norm_of_nonneg (Real.exp_pos _|>.le)]; exact Real.exp_monotone hi
lemma cents {x:ℝ} :|Real.exp x - (1+x)| ≤ |x| ^ (2:ℕ)*Real.exp |x| :=by simpa [sum_range_succ,add_comm] using exp_leash x 2
-- Data path. K bound on Σ tape. t means coupling. A error in integrand. r small. Margin λ <= tp...

def deltaC (a r K D S b t:ℝ)(p:ℕ) := bores p t K b + Real.exp (b+r+a)*a + (Real.exp b*(r^2*Real.exp r) + r*Real.exp b*(t*K))
lemma stat {f : PowerSeries ℝ} (p:ℕ)(t K x a A B:ℝ) (hg:Kind f)(he : Belt p f ≤ K)(hp : t*K ≤ B) (ht:0≤t)(hz:t ≤1)(hr:|a|≤r)(hu:|x -taste p f t-a|≤ A) : |Real.exp x-taste p (Spring f) t - a| ≤ deltaC A r K D S B t p ∧ Real.exp x ≤ Real.exp (B+r+A):=by
    let F:= taste p f t; let Y:= taste p (Spring f) t; let v:= Real.exp; have hZ:= sauce f p ht hz; rw [hg,sub_zero] at hZ
    have hL : |F| ≤ t*K:= hZ.trans (mul_le_mul_of_nonneg_left he ht); have hb : |F| ≤ B:= hL.trans hp; have hp' :0 ≤ B:=(abs_nonneg _).trans hb
    have hA : 0 ≤ A:= (abs_nonneg _).trans hu; have hx: x ≤ B+r+A:= by linarith only [(abs_le.mp hu).2,show F ≤ B from (abs_le.mp hb).2,(abs_le.mp hr).2] -- F defin simpl
    have hm: F+a ≤ B+r+A:=by linarith only [hA,(abs_le.mp hb).2,(abs_le.mp hr).2]
    have hh: |v x-v (F+a)| ≤ v (B+r+A)*A:= (exp_rate hx hm).trans (mul_le_mul_of_nonneg_left (show |x - (F+a)|≤ A from by rw [←sub_sub]; exact hu) (Real.exp_pos _).le)
    have hc : |v F -1| ≤ v B*(t*K):=by rw [← Real.exp_zero]; have he:= exp_rate (abs_le.mp hb).2 hp'; unfold v; rw [sub_zero] at he; exact he.trans (mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le)
    have hk:|v F-Y|≤ bores p t K B:=by rw [abs_sub_comm]; exact sauceUp f hg t B ht hz he hp
    let d₀:= deltaC A r K D S B t p; have hQ := cents (x:=a); have hx' : |v a - (1+a)| ≤ r^2* Real.exp r:= hQ.trans (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hr _) (Real.exp_monotone hr) (Real.exp_pos _).le (sq_nonneg _))
    refine ⟨?_,Real.exp_monotone hx⟩; have hV:|a*(v F-1)|≤ r*v B*(t*K):=by rw [abs_mul]; exact (mul_le_mul hr hc (abs_nonneg _) ((abs_nonneg _).trans hr)).trans_eq (by ring)
    have ha: |v F*(v a-(1+a))|≤ v B*(r^2 *Real.exp r):=by rw [abs_mul,abs_of_pos (Real.exp_pos _)]; exact mul_le_mul (Real.exp_monotone (abs_le.mp hb).2) hx' (abs_nonneg _) (Real.exp_pos _).le
    change |v x-Y-a| ≤ _
    rw [show v x-Y-a=(v F-Y)+(v x-v (F+a))+(v F*(v a-(1+a))+a*(v F-1)) from (by unfold v; rw [Real.exp_add]; ring)]
    exact (abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add hk hh)) ((abs_add_le ..).trans (add_le_add ha hV)))
-- weight has exact put.
def debit (p :ℕ)(K B r a t w δ :ℝ)(c : ℝ) := Real.exp (B+r+a)*w + c*δ + r*t*c +t^(p+1)*(bag p K*c)
lemma scan {f g:PowerSeries ℝ}(p:ℕ)(K x a A B c u w d0:ℝ)(hg:Kind f)(ht:0≤t)(hz:t≤1)(hc:Belt p g ≤ c)(hf:Belt p f≤K)(hp: |Real.exp x - taste p (Spring f) t-a|≤ d0) (hy:Real.exp x ≤ Real.exp (B+r+A))(hr:|a| ≤ r)(he :|u- taste p g t| ≤ w): |Real.exp x*u - taste p (g*Spring f) t - a*µ 0 g| ≤ debit p K B r A t w d0 c :=by
    let F:=taste p f t; let v:=taste p (Spring f) t; let s' := taste p g t; have hb := sauce g p ht hz
    have hx:|a * (s'-µ 0 g)| ≤ r*t*c := by rw [abs_mul]; apply le_trans (mul_le_mul hr (hb.trans (mul_le_mul_of_nonneg_left hc ht)) (abs_nonneg _) ((abs_nonneg _).trans hr)); exact le_of_eq (by ring)
    have hm : |Real.exp x * (u-s')|≤ Real.exp (B+r+A)*w := by rw [abs_mul,abs_of_nonneg (Real.exp_pos _|>.le)]; exact mul_le_mul hy he (abs_nonneg _) (Real.exp_pos _).le
    have h :0 ≤ c := (Belt_pos ..).trans hc; have hv : |(Real.exp x-v-a)*s'|≤ c*d0:=by rw [abs_mul,mul_comm c]; exact mul_le_mul hp ((taste_pays ht hz g).trans hc) (abs_nonneg _) ((abs_nonneg _).trans hp)
    let z:=taste p (g*Spring f) t; have hl:|s'*v-z|≤ t^(p+1)*(bag p K*c):=by rw [abs_sub_comm];exact (taste_mul p t ht hz g (Spring f)).trans (mul_le_mul_of_nonneg_left ((mul_le_mul hc (lavish f hg p hf) (Belt_pos ..) h).trans_eq (mul_comm ..)) (by positivity))
    change |_ - z-a*µ 0 g|≤ _; unfold debit; rw [show _ - z-a*µ 0 g = (Real.exp x*(u-s')+(Real.exp x-v-a)*s')+ a*(s'-µ 0 g)+(s'*v-z) by ring]; exact (abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add hm hv)) hx)) hl)
end YM.MSbar.Bakery.Portal
