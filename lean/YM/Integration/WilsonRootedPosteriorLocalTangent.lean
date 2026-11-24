import YM.Integration.WilsonRootedPosteriorComparison

/-! The first change of every moment and both means in the mixed row.
The same original signed likelihood enters each covariance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPosteriorLocalTangent
open Filter Function MeasureTheory RG
open WilsonRootedPosteriorComparison (Pair value)
open scoped Classical Topology BigOperators
variable {X:Type*}[MeasurableSpace X]

def linear (E C:(X→ℂ)→ℂ)(w a b j:X→ℂ):ℂ:=
  C (fun x=>w x*j x)-(C w*E j+E w*C j)-
    (C (fun x=>w x*a x)*E b+E (fun x=>w x*a x)*C b)-
    (C (fun x=>w x*b x)*E a+E (fun x=>w x*b x)*C a)+
    2*((C w*E a+E w*C a)*E b+(E w*E a)*C b)

structure Changed (δ n c f:ℝ)(x y t:ℂ):Prop where
  base:Pair (n*δ) f x y
  remainder:‖y-x-t‖≤c*δ^2*f

theorem Changed.mul {δ n m c h f g:ℝ}{x y u v t s:ℂ}(a:Changed δ n c f x y t)(b:Changed δ m h g u v s):
    Changed δ (n+m) (c+h+n*m) (f*g) (x*u) (y*v) (t*u+x*s):=by
  refine ⟨by simpa only [add_mul] using a.base.mul b.base,?_⟩
  have ap:‖y-x‖≤n*δ*f:=by simpa only [norm_sub_rev y x] using a.base.price
  have bp:‖v-u‖ ≤ m*δ*g:=by simpa only [norm_sub_rev v u] using b.base.price
  calc
    _=‖(y-x-t)*u+x*(v-u-s)+(y-x)*(v-u)‖:=by congr 1;ring
    _≤‖(y-x-t)*u‖+‖x*(v-u-s)‖+‖(y-x)*(v-u)‖:=(norm_add_le ..).trans (add_le_add (norm_add_le ..) le_rfl)
    _≤(c*δ^2*f)*g+f*(h*δ^2*g)+(n*δ*f)*(m*δ*g):=by
      simp only [norm_mul]
      exact add_le_add (add_le_add (mul_le_mul a.remainder b.base.left (norm_nonneg _) ((norm_nonneg _).trans a.remainder))
        (mul_le_mul a.base.left b.remainder (norm_nonneg _) a.base.positive))
        (mul_le_mul ap bp (norm_nonneg _) ((norm_nonneg _).trans ap))
    _= _:=by ring

def Bought (E L C:(X→ℂ)→ℂ)(δ k:ℝ):Prop:=∀f,Measurable f→∀b:ℝ,0≤b→(∀x,‖f x‖≤b)→Changed δ 1 k b (E f) (L f) (C f)

private theorem five (p q r s t:ℂ):‖p-q-r-s+2*t‖≤‖p‖+‖q‖+‖r‖+‖s‖+2*‖t‖:=by
  have h1:=norm_sub_le p q
  have h2:‖p-q-r‖≤‖p‖+‖q‖+‖r‖:=(norm_sub_le ..).trans (add_le_add h1 le_rfl)
  have h3:‖p-q-r-s‖≤‖p‖+‖q‖+‖r‖+‖s‖:=(norm_sub_le ..).trans (add_le_add h2 le_rfl)
  have h4:=norm_add_le (p-q-r-s) (2*t)
  rw [norm_mul,show ‖(2:ℂ)‖=(2:ℝ) by norm_num] at h4
  exact h4.trans (add_le_add h3 le_rfl)

theorem original (E L C:(X→ℂ)→ℂ){δ k:ℝ}(paid:Bought E L C δ k)(w a b j:X→ℂ){t A B J:ℝ}
    (mw:Measurable w)(ma:Measurable a)(mb:Measurable b)(mj:Measurable j)
    (pt:0≤t)(pa:0≤A)(pb:0≤B)(pj:0≤J)
    (pw:∀x,‖w x‖≤t)(ha:∀x,‖a x‖≤A)(hb:∀x,‖b x‖≤B)(hj:∀x,‖j x‖≤J):
    ‖value L w a b j-value E w a b j-linear E C w a b j‖≤
      δ^2*t*((3*k+1)*J+(10*k+8)*A*B):=by
  have W:=paid w mw t pt pw
  have H:=paid j mj J pj hj
  have U:=paid a ma A pa ha
  have V:=paid b mb B pb hb
  have cost (f g:X→ℂ){s r:ℝ}(hf:∀x,‖f x‖ ≤ s)(pos:0 ≤ s)(hg:∀x,‖g x‖ ≤ r)(x:X):‖f x*g x‖ ≤ s*r:=by
    rw [norm_mul];exact mul_le_mul (hf _) (hg _) (norm_nonneg _) pos
  have M:=paid (fun x=>w x*j x) (mw.mul mj) (t*J) (mul_nonneg pt pj) (cost w j pw pt hj)
  have XA:=paid (fun x=>w x*a x) (mw.mul ma) (t*A) (mul_nonneg pt pa) (cost w a pw pt ha)
  have XB:=paid (fun x=>w x*b x) (mw.mul mb) (t*B) (mul_nonneg pt pb) (cost w b pw pt hb)
  let p:=L (fun x=>w x*j x)-E (fun x=>w x*j x)-C (fun x=>w x*j x)
  let q:=L w*L j-E w*E j-(C w*E j+E w*C j)
  let r:=L (fun x=>w x*a x)*L b-E (fun x=>w x*a x)*E b-(C (fun x=>w x*a x)*E b+E (fun x=>w x*a x)*C b)
  let s:=L (fun x=>w x*b x)*L a-E (fun x=>w x*b x)*E a-(C (fun x=>w x*b x)*E a+E (fun x=>w x*b x)*C a)
  let v:=L w*L a*L b-E w*E a*E b-((C w*E a+E w*C a)*E b+E w*E a*C b)
  have major:=add_le_add (add_le_add (add_le_add (add_le_add M.remainder (W.mul H).remainder)
    (XA.mul V).remainder) (XB.mul U).remainder) (mul_le_mul_of_nonneg_left ((W.mul U).mul V).remainder (show (0:ℝ)≤2 by norm_num))
  calc
    _=‖p-q-r-s+2*v‖:=by unfold value linear p q r s v;congr 1;ring
    _≤_:=((five p q r s v).trans major).trans (le_of_eq (by ring))
end YM.Integration.WilsonRootedPosteriorLocalTangent
