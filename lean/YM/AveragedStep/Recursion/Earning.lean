import YM.AveragedStep.Recursion.Blue
/-!
 Uniform at sites: tools before accounting lists/orders. A glaze
 with positive exponent can price inherited wraps; must debit width
 against the pin-mass. Here NO expansion on pure coarse legs thrown out
 without price even though the test is ≤1. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.SD
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
open Matrix Push.Uniform
variable {c f:Side}{G:Gauge}{S:StepData c f}
def lens (S:StepData c f)(a:ℝ)(x:Site f)(w:Lips G c f):ℝ:=Real.exp (a*steps (S:=S) x w)
lemma lens_pos (S:StepData c f)(a:ℝ)(x:Site f)(w:Lips G c f):0<lens S a x w:=Real.exp_pos _
def coupon (S:StepData c f)(a:ℝ)(d:ℕ)(x:Site f)(i:Rim c f)(w:Lips G c f):ℝ := Real.exp (a*(steps (S:=S) x w+(d+1:ℝ)*((separation x (atRim S i):ℝ)+(2:ℝ)*aperture S.patch)))
lemma coupon_pos (S:StepData c f)(a:ℝ)(d:ℕ)(x:Site f)(i:Rim c f)(w:Lips G c f):0<coupon S a d x i w:=Real.exp_pos _
lemma coupon_border (S:StepData c f)(a:ℝ)(hA:0<a)(d:ℕ)(x:Site f){n:ℕ}(hn:n≤d+1)(i:Rim c f)(w:Lips G c f){v:Lips G c f}
    (hv:steps (S:=S) x v ≤ steps (S:=S) x w+n*((separation x (atRim S i):ℝ)+(2:ℝ)*aperture S.patch)): lens S a x v ≤ coupon S a d x i w := by
 apply Real.exp_monotone (mul_le_mul_of_nonneg_left (hv.trans ?_) hA.le)
 gcongr; exact_mod_cast hn

def stale (τ:ℝ)(d q:ℕ):ℝ:=τ⁻¹^(d+1)*lag τ^q
lemma stale_pos {τ:ℝ}(h:1≤τ)(d q:ℕ):0≤stale τ d q:=by unfold stale; have he:=lag_ge h; positivity
lemma stale_mono {τ:ℝ}(h:1≤τ)(d:ℕ){q m:ℕ}(hi:q≤m):stale τ d q ≤ stale τ d m:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (lag_ge h) hi) (by positivity)
lemma stale_shift {τ:ℝ}{d i:ℕ}(hK:i≤d)(q:ℕ) : τ⁻¹^i*stale τ (d-i) q=stale τ d q:=by rw [stale,← mul_assoc,← pow_add]; unfold stale; congr 2; omega

def Fund {τ a:ℝ}(x:Site f)(M:Lips G c f→ℝ)(d n k:ℕ)(B:ℝ)(q:ℕ):Prop:=∀ w:Lips G c f,w.length≤k → clips w ≤ n → |M w| ≤ B*stale τ d q*lens S a x w
lemma Fund.payable {τ a:ℝ}{x:Site f}{M:Lips G c f→ℝ}{d n k:ℕ}{B C:ℝ}{q r:ℕ}(H:Fund (S:=S) (τ:=τ) (a:=a) x M d n k B q)(h:1≤τ)(hb:0≤B)(hB:B≤C)(hQ:q≤r): Fund (S:=S) (τ:=τ) (a:=a) x M d n k C r:=by
 intro w hw ht
 exact (H _ hw ht).trans (mul_le_mul_of_nonneg_right (mul_le_mul hB (stale_mono h _ hQ) (stale_pos h ..) (hb.trans hB)) (lens_pos ..).le)
lemma shy_price {τ a:ℝ}{x:Site f}{M:Lips G c f→ℝ}{n k d:ℕ}{B:ℝ}{q:ℕ}(H:Fund (S:=S) (τ:=τ) (a:=a) x M d n k B q)(h:1≤τ)(ha:0<a)(hb:0≤B){j w}{v:Spray (Lips G c f)}{L:ℝ}(hq:Signed (Shy S j w) v L)(ht0:w.length+1≤k)(ht:clips w≤n):
    |offer M v| ≤ (L*B)*stale τ d q*coupon S a d x j.1 w:=by
 rw [mul_assoc L,mul_assoc L]
 have he:= stale_pos h d q; have hv:0≤B*stale τ d q:=mul_nonneg hb he
 apply hq.pay; · have :=coupon_pos S a d x j.1 w; positivity
 intro i hi
 exact (H i (hi.lo.trans ht0) (hi.fine.trans ht)).trans (mul_le_mul_of_nonneg_left (coupon_border S a ha _ x (n:=1) (by omega) j.1 w (by rw [Nat.cast_one,one_mul,← add_assoc]; exact hi.pays _)) hv)
lemma joy_price {τ a:ℝ}{x:Site f}{M:Lips G c f→ℝ}{k d i:ℕ}{B:ℝ}{q:ℕ}(H:Fund (S:=S) (τ:=τ) (a:=a) x M (d-i) (k+d+1) (k+d+1) B q)(h:1≤τ)(ha:0<a)(hb:0≤B)(hK:i≤d){j w}{v:Spray (Lips G c f)}{L:ℝ}(hq:Signed (Joy S j (i+1) w) v L)(ht0:w.length+1≤k):
    |τ⁻¹^i * offer M v| ≤ (L*B)*stale τ d q*coupon S a d x j.1 w:=by
 rw [abs_mul, abs_of_nonneg (show 0 ≤ τ⁻¹^i by positivity)]
 let R:=coupon S a d x j.1 w
 let T:=stale τ (d-i) q; have he:0≤T:=stale_pos h ..
 refine (mul_le_mul_of_nonneg_left (hq.pay (B*T*R) M (by have hr:0<R:=coupon_pos ..; positivity) ?_) (show 0≤τ⁻¹^i by positivity)).trans_eq ?_
 · intro a hV
   have hl:a.length ≤ k+d+1:=by have:=hV.lo; omega
   exact (H a hl ((full a).trans hl)).trans (mul_le_mul_of_nonneg_left (coupon_border S _ ha d x (n:=i+1) (by omega) j.1 w (hV.pays _)) (by change 0≤B*T; positivity))
 unfold T R; rw [← stale_shift (τ:=τ) hK q]; ring
/-- a to be selected small wrt b/ inverse η. -/
def reachBit (P:Patch)(d:ℕ)(a:ℝ):ℝ:=Real.exp (a*((d+1:ℝ)*(2*aperture P)))
lemma coupon_pass (S:StepData c f){a b η:ℝ}(ha:0<a){d:ℕ}(hB:a*(d+1:ℝ)≤b)(hZ:a*(d+1:ℝ)≤η/2)(x:Site f)(p i:Ink G c f)(w:Lips G c f):
    coupon S a d x i.1 w ≤ reachBit S.patch d a*lens S b x (p::w)*Real.exp ((η/2)*(separation (atRim S p.1) (atRim S i.1):ℝ)):=by
 unfold coupon lens reachBit
 let v :ℝ:= separation x (atRim S p.1)
 let l :ℝ:= separation (atRim S p.1) (atRim S i.1)
 let Q:ℝ:=separation x (atRim S i.1)
 let U:=steps (S:=S) x w
 rw [← Real.exp_add,←Real.exp_add,steps_cons]; apply Real.exp_monotone
 have hn:0 ≤ a*(d+1:ℝ):=by positivity
 have hx:a ≤ b:= (le_mul_of_one_le_right ha.le (by simp : 1≤(d:ℝ)+1)).trans hB
 have hs:Q ≤ v+l:= by unfold Q v l; exact_mod_cast separation_triangle ..
 have hv : 0≤v:=by positivity [v]
 have hl : 0≤l:=by positivity [l]
 have hU :0≤U:=step_pos ..
 change a*(U+(d+1:ℝ)*(Q+_)) ≤ a*(_*_)+ b*(v+U)+η/2*l
 nlinarith only [mul_le_mul_of_nonneg_left hs hn,mul_le_mul_of_nonneg_right hB hv,mul_le_mul_of_nonneg_right hZ hl,mul_le_mul_of_nonneg_right hx hU]
lemma back_shift (S:StepData c f)(F:Forest S.ratio){A:ChartRatio G}(E:Wage G S.patch S.kernel A)(hS: Bid.Larger (G:=G) S){d:ℕ}{a b:ℝ}(ha:0<a)(hB:a*(d+1:ℝ)≤b)(hZ:a*(d+1:ℝ)≤E.η/2)(x:Site f)(j:Key F G)(w:Lips G c f):
    ∑ i:Key F G,|(body A F)⁻¹ j i| * coupon S a d x (fkey F i).1 w ≤ (E.μ*((↑(keyMask G):ℝ)*countCost (E.η-E.η/2)))*reachBit S.patch d a*lens S b x (fkey F j::w):=by
 let L:=lens S b x (fkey F j::w)
 let R:=reachBit S.patch d a*L
 let C (i:Key F G):=coupon S a d x (fkey F i).1 w
 let B:=E.μ*((↑(keyMask G):ℝ)*countCost (E.η-E.η/2))
 have h (i):C i ≤ R*Real.exp (E.η/2*(separation (start F j) (start F i):ℝ)):=by
   change _ ≤ R*Real.exp (E.η/2*(separation (atRim S (fkey F j).1) (atRim S (fkey F i).1):ℝ))
   exact coupon_pass S ha hB hZ x (fkey F j) (fkey F i) w
 obtain ⟨_,he⟩:=E.lawful S F rfl rfl hS
 let T(i:Key F G):=Real.exp (E.η/2*(separation (start F j) (start F i):ℝ))
 let V(i:Key F G) := |(body A F)⁻¹ j i|
 have hv:∑ i,V i*T i ≤ B:=he.weighted E.active.le (start_card F) (by have :=E.available; linarith) j
 change (∑ i,V i*C i) ≤ B*reachBit S.patch d a*L
 calc
   _ ≤ ∑ i,(V i*T i)*R:= Finset.sum_le_sum fun i _=> (mul_le_mul_of_nonneg_left (h i) (show 0≤V i from abs_nonneg _)).trans_eq (by unfold V T; ring)
   _ ≤ B*R:=by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hv (mul_nonneg (Real.exp_pos _).le (lens_pos ..).le)
   _ = _:=by unfold R L; ring
end YM.AveragedStep.SD
