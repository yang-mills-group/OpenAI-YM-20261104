import YM.Integration.WilsonRootedPosteriorWallet

/-! Sensitivity of the whole signed mixed response. Both singleton means
are evaluated anew under each of the two probability distributions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPosteriorComparison
open MeasureTheory Filter Function RG
open scoped Topology BigOperators Classical
variable {X:Type*}[MeasurableSpace X]
def value (E:(X→ℂ)→ℂ)(w a b j:X→ℂ):ℂ:=
  E (fun x=>w x*j x)-E w*E j-E (fun x=>w x*a x)*E b-E (fun x=>w x*b x)*E a+
    2*(E w*E a*E b)

structure Pair (δ f:ℝ)(x y:ℂ):Prop where
  positive:0≤f
  left:‖x‖≤f
  right:‖y‖≤f
  price:‖x-y‖≤δ*f

theorem Pair.mul {d e f g:ℝ}{x y u v:ℂ}(a:Pair d f x y)(b:Pair e g u v):
    Pair (d+e) (f*g) (x*u) (y*v):=by
  refine ⟨mul_nonneg a.positive b.positive,?_,?_,?_⟩
  · rw [norm_mul];exact mul_le_mul a.left b.left (norm_nonneg _) a.positive
  · rw [norm_mul];exact mul_le_mul a.right b.right (norm_nonneg _) a.positive
  · calc
      _ = ‖(x-y)*u+y*(u-v)‖:=by congr 1;ring
      _ ≤ ‖(x-y)*u‖+‖y*(u-v)‖:=norm_add_le ..
      _ ≤ d*f*g+f*(e*g):=by
        simp only [norm_mul];exact add_le_add (mul_le_mul a.price b.left (norm_nonneg _) ((norm_nonneg _).trans a.price))
          (mul_le_mul a.right b.price (norm_nonneg _) a.positive)
      _ = _:=by ring

def Filed (E L:(X→ℂ)→ℂ)(δ:ℝ):Prop:=∀f,Measurable f→∀b:ℝ,0≤b→(∀x,‖f x‖≤b)→Pair δ b (E f) (L f)

private theorem sub {x y u v:ℂ}{a b:ℝ}(h:‖x-y‖≤a)(k:‖u-v‖≤b):
    ‖(x-u)-(y-v)‖≤a+b:=by
  rw [show x-u-(y-v)=(x-y)-(u-v) by ring];exact (norm_sub_le ..).trans (add_le_add h k)

private theorem add {x y u v:ℂ}{a b:ℝ}(h:‖x-y‖≤a)(k:‖u-v‖≤b):
    ‖(x+u)-(y+v)‖≤a+b:=by
  rw [show x+u-(y+v)=(x-y)+(u-v) by ring];exact (norm_add_le ..).trans (add_le_add h k)

theorem original (E L:(X→ℂ)→ℂ){δ:ℝ}(paid:Filed E L δ)(w a b j:X→ℂ){t A B J:ℝ}
    (mw:Measurable w)(ma:Measurable a)(mb:Measurable b)(mj:Measurable j)
    (pt:0≤t)(pa:0≤A)(pb:0≤B)(pj:0≤J)
    (pw:∀x,‖w x‖≤t)(ha:∀x,‖a x‖≤A)(hb:∀x,‖b x‖≤B)(hj:∀x,‖j x‖≤J):
    ‖value E w a b j-value L w a b j‖≤δ*t*(3*J+10*A*B):=by
  have W:=paid w mw t pt pw
  have H:=paid j mj J pj hj
  have U:=paid a ma A pa ha
  have V:=paid b mb B pb hb
  have cost (f g:X→ℂ){s r:ℝ}(hf:∀x,‖f x‖ ≤ s)(pos:0 ≤ s)(hg:∀x,‖g x‖ ≤ r)(x:X):‖f x*g x‖ ≤ s*r:=by
    rw [norm_mul];exact mul_le_mul (hf _) (hg _) (norm_nonneg _) pos
  have M:=paid (fun x=>w x*j x) (mw.mul mj) (t*J) (mul_nonneg pt pj) (cost w j pw pt hj)
  have Xₐ:=paid (fun x=>w x*a x) (mw.mul ma) (t*A) (mul_nonneg pt pa) (cost w a pw pt ha)
  have Xᵦ:=paid (fun x=>w x*b x) (mw.mul mb) (t*B) (mul_nonneg pt pb) (cost w b pw pt hb)
  have raw:=((W.mul U).mul V).price
  have twice:‖2*(E w*E a*E b)-2*(L w*L a*L b)‖≤2*((δ+δ+δ)*(t*A*B)):=by
    rw [←mul_sub,norm_mul,show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
    exact mul_le_mul_of_nonneg_left raw (show (0:ℝ)≤2 by norm_num)
  have purchased:=add (sub (sub (sub M.price (W.mul H).price) (Xₐ.mul V).price) (Xᵦ.mul U).price) twice
  apply purchased.trans
  exact le_of_eq (by ring)

theorem expectation (μ:Measure X)[IsProbabilityMeasure μ](w a b j:X→ℂ)
    (hw:Envelope w)(ha:Envelope a)(hb:Envelope b)(hj:Envelope j):
    value (fun f=>∫x,f x ∂μ) w a b j=∫x,w x*WilsonRootedPosteriorConnected.test μ a b j x ∂μ:=by
  rw [WilsonRootedPosteriorConnected.original μ w a b j hw ha hb hj]
  unfold value
  ring

end YM.Integration.WilsonRootedPosteriorComparison
