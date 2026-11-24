import YM.OPE.Compatible.Karls.Timber
/-! # homogeneous crowns, going backwards. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{m k i:ℕ}{q:ℝ}(p:E→L[ℝ] E)
local notation "X!"=> E→L[ℝ] E
open Filter Finset
open Quit.PriceZ
local notation "A!"=> Dice E
variable {G:Type}[NormedAddCommGroup G][NormedSpace ℝ G]
-- `thick` Pal stationary.H
variable (G:ℕ→ℕ→ Dice E) (L:ℕ→ E→L[ℝ] E)(Y:ℕ→Dice E) (T:E→L[ℝ] E) {b v u w:ℝ} {a d:ℕ}
lemma surge_h {r:ℝ} (x:ℝ)(f:ℝ→ℝ)(h:Continuous f)(hp:f x < r):∃ v:ℝ,x<v∧f v<r:=by
    obtain ⟨a,ha,hv⟩:= Metric.continuousAt_iff.1 (h.continuousAt (x:=x)) (r-f x) (sub_pos.mpr hp); refine ⟨x+a/2,lt_add_of_pos_right _ (by positivity),?_⟩; have hx: dist (x+a/2) x<a:=by rw [Real.dist_eq]; exact abs_lt.mpr ⟨by linarith,by linarith⟩
    have he:=hv hx; rw [Real.dist_eq,abs_lt] at he; linarith only [he.2]
variable {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]
lemma behind (ι:V→L[ℝ] E)(T X:V→L[ℝ] V)(f:ℕ→ Dice E)(h:X*T=1)(F:∀ n:ℕ,Summable (pl ι X f n))(x y:ℕ→V)(hp:∀ i,x (i+1)=T (x i))(hq:∀ i,y (i+1)=T (y i))(a n:ℕ):
     rear ι X f a (x n) (y n)=rear ι X f (a+n) (x 0) (y 0)+∑ i∈ range n,f (a+n-1-i) (ι (x i)) (ι (y i)):=by induction n generalizing a with
     | zero=>simp only [add_zero,sum_range_zero]
     | succ n ih=> rw [hp n,hq n,rest_step ι X f T h a (F a) (F (a+1)),ih (a+1), Finset.sum_range_succ]; rw [show a+(n+1)-1-n=a from by omega,show a+(n+1)=a+1+n from by omega]; abel
lemma fareStep {x y z t:ℕ→E} {q c r k:ℝ} (Z:ℕ→ℕ→ Dice E) (Q:ℕ→Dice E)(hx:0 < q)(hx':k < q*q)(ht:0 < k)(hp:0 ≤ r)(hP:r<1)(hz:0 ≤ c)(hC:c<q)(hB:∃ b:ℝ,∀ i j:ℕ,‖Z i j‖≤ b*k^j)
    (hR:∃ K:ℝ,∀ i j:ℕ, ‖Z i j-Q j‖≤ K*k^j*r^i) (h:∃ v,Hex c (x-z) v)(hh:∃ v,Hex c (y-t) v)(hk:∀ r:ℝ,q<r→∃ v,Hex r z v)(hm:∀ r:ℝ,q<r→∃ v,Hex r t v):
    Thick (q*q) (fun n=>∑ i∈range n, (Z i (n-1-i) (x i) (y i)-Q (n-1-i) (z i) (t i))):=by
       obtain ⟨b,B⟩:=hB; obtain ⟨K,R⟩:=hR; obtain ⟨v,hv⟩:=h; obtain ⟨s',Hs'⟩:= hh
       obtain ⟨a,ha,H⟩:= surge_h q (fun t=>max (r*t*t) (c*t)) (by fun_prop) (show max (r*q*q) (c*q)<q*q from max_lt (by nlinarith) (by nlinarith))
       obtain ⟨d,hD⟩:= hk a ha; obtain ⟨s,hS⟩:=hm a ha; have hy: Hex a y (s'+s):=sub_add_cancel y t ▸ Hex.add (Hs'.warm hz (hC.trans ha).le) hS
       let f:=fun i j=>Z i j (x i) (y i)- Q j (z i) (t i); have hk : max (r*a*a) (c*a) < q*q:= H; let p:= max k (max (r*a*a) (c*a)); have hq:p>0:=ht.trans_le (le_max_left ..); have h':p<q*q:= max_lt hx' hk; have ha' :0 < a:= hx.trans ha
       have h₁:0≤b:=by have ht:0 ≤ b*k^0:= (norm_nonneg (Z 0 0)).trans (B 0 0); rwa [pow_zero,mul_one] at ht
       have h₂:0 ≤ K:=by have ht:0 ≤ K*k^0*r^0:=(norm_nonneg (Z 0 0-Q 0)).trans (R 0 0); simpa using ht
       let t':=b*v*(s'+s)+b*d*s'+ K*d*s
       obtain ⟨V,hV,HV⟩:= exists_between h'; refine Thick.hex (f:=_) ⟨_,fogSum f (c:=t') hq.le hV fun i j=>?_⟩ (hq.trans hV).le HV
       let D:= Z i j; have he:f i j = D ((x-z) i) (y i)+ D (z i) ((y-t) i) + (D-Q j) (z i) (t i):=by unfold f; rw [Pi.sub_apply,Pi.sub_apply,map_sub,map_sub]; change D (x i) (y i)- Q j (z i) (t i)= D (x i) (y i)-D (z i) (y i)+( D (z i) (y i)-D (z i) (t i))+(D (z i) (t i)-Q j (z i) (t i)); ring
       have h₃:0 ≤ d:= hD.price; have h₄:0 ≤ v:= hv.price; have h₅:0 ≤ s':=Hs'.price; have h₆:0 ≤ s:=hS.price; let J:=p^j*p^i
       have hx(m:ℝ)(hh:0≤m)(hv:m≤p): k^j*m^i ≤ J:=mul_le_mul (pow_le_pow_left₀ ht.le (le_max_left ..) _) (pow_le_pow_left₀ hh hv _) (pow_nonneg hh _) (pow_nonneg hq.le _)
       have ha: c*a ≤ p:=le_trans (le_max_right ..) (le_max_right ..)
       have hv₁ : ‖D ((x-z) i) (y i)‖ ≤ b*v*(s'+s)*J:=by
           apply le_trans (InvokeB ..); apply le_trans (mul_le_mul (mul_le_mul (B i j) (hv i) (norm_nonneg _) (by positivity)) (hy i) (norm_nonneg _) (by positivity)); apply le_trans _ (mul_le_mul_of_nonneg_left (hx _ (by positivity) ha) (by positivity :0≤ b*v*(s'+s))); rw [mul_pow];exact le_of_eq (by ring)
       have hv₂: ‖D (z i) ((y-t) i)‖ ≤ b*d*s'*J:=by
           apply le_trans (InvokeB ..); apply le_trans (mul_le_mul (mul_le_mul (B i j) (hD i) (norm_nonneg _) (by positivity)) (Hs' i) (norm_nonneg _) (by positivity)); apply le_trans _ (mul_le_mul_of_nonneg_left (hx _ (by positivity) ha) (by positivity :0≤b*d*s')); rw [mul_pow]; exact le_of_eq (by ring)
       have hv₃: ‖(D-Q j) (z i) (t i)‖ ≤ K*d*s*J:=by
           apply le_trans (InvokeB ..); apply le_trans (mul_le_mul (mul_le_mul (R i j) (hD i) (norm_nonneg _) (by positivity)) (hS i) (norm_nonneg _) (by positivity)); apply le_trans _ (mul_le_mul_of_nonneg_left (hx _ (by positivity :0 ≤ r*a*a) (le_trans (le_max_left ..) (le_max_right ..))) (by positivity)); rw [mul_pow,mul_pow]; exact le_of_eq (by ring)
       rw [he]; apply ((norm_add_le ..).trans (add_le_add ((norm_add_le ..|>.trans (add_le_add hv₁ hv₂))) hv₃)).trans_eq; unfold t' J; ring
end YM.OPE.Hark
