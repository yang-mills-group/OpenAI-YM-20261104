import YM.MSbar.Rolling.Palm
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Function Filter MeasureTheory Set Cacao
open scoped Topology Classical BigOperators ContDiff
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
variable {σ : Type*} {X :ℝ→σ→Prop}{z : ℝ→σ→ℝ}
open Price Bakery
local notation "µ"=> PowerSeries.coeff
namespace Price
lemma absR {e} (h:Price X e z) : Price X e (fun x y=> |z x y|):=h.bounds (Eventually.of_forall fun x h q=> by simp)
end Price
open Portal
variable {ι:Type}[Fintype ι]
open MvPolynomial
local notation "H"=>View ι
local notation "P"=>PowerSeries (Pot ι)
local notation "µ₀"=> (µ 0)
variable (w:ℝ→σ→View ι)(h:Price X 0 w)
include h
lemma volley (f:Pot ι):Price X 0 (fun x y=>eval (w x y) f):=by
   induction f using MvPolynomial.induction_on with
   | C a=>simp_rw [eval_C]; exact fromConst _
   | add p q hp hq=>simp only [map_add]; exact hp.nsum hq
   | mul_X p i ih=>simp only [map_mul,eval_X]; refine ih.product (q:=0) ?_; obtain ⟨d,ha⟩:=h; refine ⟨d,ha.mono fun x hh p hp=>?_⟩; exact (norm_le_pi_norm (w x p) _).trans (hh _ hp)
local notation "q!"=>w
variable (A:PowerSeries (Pot ι))
lemma girth (p:ℕ): Price X 0 (fun x y=> Belt p (picture (w x y) A)):= Price.bag (Finset.range ..) _ (fun i _=> by simpa only [picture,PowerSeries.coeff_map] using (volley w h (µ i A)|>.absR)) -- notation
lemma draw (n:ℕ):Price X 0 (fun x y=> taste n (picture (w x y) A) x):=(girth w h A n).bounds (width.mono fun x he y hy=> (taste_pays he.1.le he.2.1 _).trans (le_abs_self _))
lemma sense (n:ℕ)(hf : Kind A) : Price X 1 (fun x y=>taste n (picture (w x y) A) x):=by
    refine ((xunit X).product (girth w h A n)).bounds ?_; filter_upwards [width] with x ⟨hu,hx,he⟩ y hy;  apply le_trans _ (le_abs_self _); have hv:=sauce (picture (w x y) A) n hu.le hx; have hz:µ 0 (picture (w x y) A)=0:= by unfold picture; rw [PowerSeries.coeff_map,hf,_root_.map_zero]
    rw [hz,sub_zero] at hv; exact hv
omit h in
lemma winters (_i:ℝ→σ→View ι) (g :ℝ→σ→ℝ) (p:ℕ)(h: Price X 0 g): Price X (p+1) (fun x y=>bores p x (g x y) 1) := by
    let s:= xunit X; have hp : Price X (p+1) (fun x y=> (x * g x y)^(p+1)) := by simpa only [Nat.add_zero, Nat.one_mul] using (Price.pow (s.product h) (p+1))
    refine (hp.product (q:=0) (fromConst (Real.exp 1))).nsum ((Price.bag _ (fun (i:ℕ) x y=> ((i:ℝ)*x^(p+1)*g x y^i)/(i.factorial:ℝ)) ?_)); intro i _
    have hv : Price X (p+1) (fun x y=> (i:ℝ)*x^(p+1)):= by simpa only [Nat.zero_add] using (fromConst (i:ℝ)).product (xrise X (p+1))
    have ht:Price X 0 (fun x y=>g x y^i):=(Nat.zero_mul i) ▸ h.pow i
    exact ((hv.product (q:=0) ht).product (fromConst (i.factorial:ℝ)⁻¹)).egress (Eventually.of_forall (fun _ _ _=> by simp only [div_eq_mul_inv]))
lemma away (p:ℕ) (a:Kind A) :Price X (p+1) (fun x y=> taste p (picture (w x y) (Spring A)) x - Real.exp (taste p (picture (w x y) A) x)):=by
    let f(x:ℝ)(y:σ):= picture (w x y) A; let u x y:=Belt p (f x y); have hh : Price X 1 (fun x y=>x*u x y):=(xunit X).product (girth w h A p); refine (winters w u p (girth w h A p)).bounds ?_
    filter_upwards [width,hh.reach 1 zero_lt_one (by simp)] with x ⟨hx,hh',hc⟩ he y hY
    have hK:(picture (w x y) (Spring A))=Spring (f x y):= (sunshine (aeval (R:=ℝ) (w x y))).symm; rw [hK]; apply le_trans _ (le_abs_self _)
    have ha:Kind (f x y):=by unfold f Kind picture; rw [PowerSeries.coeff_map,a,map_zero]
    exact sauceUp _ ha _ _ hx.le hh' le_rfl ((le_abs_self _).trans (he y hY).le)
-- charge actual log and convert along input price. Useful Δ
variable (t:ℕ)(hA:Kind A)(hz:Price X (t+1) (fun x y=> z x y-taste t (picture (w x y) A) x))
include h hA hz
lemma early : Price X (t+1) (fun x y=> Real.exp (z x y)-taste t (picture (w x y) (Spring A)) x):=by
    let f:=fun x y=>taste t (picture (w x y) A) x
    have a:=sense w h A t hA; have ht: Price X 1 z:= ((hz.poorly (by omega : 1≤t+1)).nsum a).egress (Eventually.of_forall fun x y _=> by ring)
    have hv:Price X (t+1) (fun x y=>Real.exp (z x y)-Real.exp (taste t (picture (w x y) A) x)):=by
       have he:= hz.product (fromConst (Real.exp 1)); apply he.bounds; filter_upwards [a.reach 1 zero_lt_one (by simp),ht.reach 1 zero_lt_one (by simp)] with x hd hb y hy; simp only [Real.norm_eq_abs]; rw [abs_mul,abs_of_nonneg (Real.exp_pos _|>.le), mul_comm]; exact exp_rate ((le_abs_self _).trans (hb y hy|>.le)) ((le_abs_self _).trans (hd y hy|>.le))
    exact (hv.cut (away w h A t hA)).egress (Eventually.of_forall fun x y _=> by ring)
omit hz
lemma unveil (hu : Price X (t+1) (fun x y=>z x y - taste t (picture (w x y) (Spring A)) x)):
    Price X (t+1) (fun x y=> Real.log (z x y) - taste t (picture (w x y) A) x):=by
    let f:=fun x y=> taste t (picture (w x y) A) x; let g x y := Real.exp (f x y)
    have hf: Price X (t+1) (fun x y=> z x y -Real.exp (f x y)):= (hu.nsum (away w h A t hA)).egress (Eventually.of_forall (fun x y _=> by unfold f;ring))
    let a:=Real.exp (-1); let b:=a/2; have hb:0<b:=half_pos (Real.exp_pos _)
    refine (hf.product (fromConst b⁻¹)).bounds ?_; filter_upwards [width,hf.reach _ hb (by omega),(sense w h A t hA).reach 1 zero_lt_one (by omega)] with x hd he ht y hy
    have hh :2*b≤ g x y :=by unfold b a g; rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] -- syntax `mul_div_cancel₀` argument which?
                                               ; apply Real.exp_monotone; exact (abs_le.mp (ht y hy).le).1
    have ha:b ≤ z x y:=by linarith only [hh,(show -b≤ z x y-g x y from (abs_le.mp (he y hy).le).1)]
    have hu: b ≤ g x y:=by linarith only [hb,hh]
    have h(i:ℝ)(hi:i∈ Set.Ici b): 0 < i := hb.trans_le hi
    have hx := (convex_Ici (𝕜:=ℝ) b).norm_image_sub_le_of_norm_deriv_le (fun i hi=> Real.differentiableAt_log (h i hi).ne') (fun i hi=> show ‖deriv Real.log i‖≤ b⁻¹ from by rw [Real.deriv_log,Real.norm_of_nonneg (inv_nonneg.mpr (h i hi|>.le))]; exact inv_anti₀ hb hi) (show g x y∈Set.Ici b from hu) (show z x y∈ Set.Ici b from ha); unfold g at hx; rw [Real.log_exp] at hx; apply hx.trans_eq; rw [norm_mul,mul_comm, Real.norm_of_nonneg (inv_nonneg.mpr hb.le)]
end YM.MSbar.Rolling
