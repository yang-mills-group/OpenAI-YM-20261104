import YM.OPE.Compatible.Karls.Top
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
-- backwards reservoir
local notation "H!"=> Dice E
variable {G:Type}[NormedAddCommGroup G][NormedSpace ℝ G]
-- reserves across l
variable (ι:G→L[ℝ] E)(X:G→L[ℝ] G)(f:ℕ→ Dice E) {a b r u:ℝ}
abbrev pl (n l:ℕ):= pullD (ι ∘L X^(l+1)) (f (l+n))
def rear (n:ℕ): Dice G:=∑' l, pl ι X f n l
lemma heft (h:∃ c,Hex a f c)(hp:∃ c, Hex b (fun i=> X^i) c)(hz:0 ≤ b)(ht:0 ≤ a):∃ c:ℝ,0 ≤ c∧∀ n:ℕ,Hex (a*b*b) (pl ι X f n) (c*a^n):=by
    obtain ⟨c,H⟩:=h; obtain ⟨d,D⟩:=hp; let r:=d*b; let s:=‖ι‖*r; have hr:0 ≤ r:=mul_nonneg D.price hz; have hx:0 ≤ s:=mul_nonneg (norm_nonneg _) hr; have hY:= H.price; refine ⟨c*s*s,(by positivity),fun n k=> ?_⟩
    let A:=ι ∘L X^(k+1); have he: ‖A‖≤ s*b^k:= (opNorm_comp_le ..|>.trans ((mul_le_mul_of_nonneg_left (D.forward k) (norm_nonneg _)).trans_eq (mul_assoc ..).symm)); apply (segment A A _).trans; apply le_trans (mul_le_mul (mul_le_mul (H (k+n)) he (norm_nonneg A) (by positivity)) he (norm_nonneg A) (by positivity)); rw [mul_pow,mul_pow,pow_add]; apply le_of_eq; ring
lemma A₁ {A:Type}[NormedAddCommGroup A][CompleteSpace A](f:ℕ→ A)(r b:ℝ)(h:0≤r)(hp:r<1)(he:Hex r f b):‖∑' i,f i‖ ≤ b*(∑' i:ℕ,r^i) ∧ Summable f:=by
    have hh:= (summable_geometric_of_lt_one h hp).mul_left b; have ht:Summable fun i:ℕ=> ‖f i‖:=Summable.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=>he i) hh; exact ⟨(norm_tsum_le_tsum_norm ht|>.trans ((ht.tsum_le_tsum he hh).trans_eq (tsum_mul_left))),ht.of_norm⟩
lemma rearF (hh:∃ c,Hex a f c)(hp:∃ c,Hex b (fun i=> X^i) c)(hz:0 ≤ b)(ht:0 ≤ a)(h:a*b*b<1): ∃ c,Hex a (rear ι X f) c∧∀ n:ℕ, Summable (pl ι X f n):=by
     obtain ⟨c,hc,H⟩:= heft ι X f hh hp hz ht; let g:=a*b*b; have hx:0 ≤ g:=(by unfold g; positivity); have he:= fun i=> A₁ (pl ι X f i) g _ hx h (H i)
     exact ⟨c*(∑' i:ℕ,g^i),fun n=>(he n).1.trans_eq (mul_right_comm ..),fun n=>(he n).2⟩
lemma pallD (p:ℕ→Dice G)(h:Summable p)(x y:G): (∑' i,p (i+1)) x y=∑' i,p (i+1) x y:=by
     let A:= (ContinuousLinearMap.apply ℝ ℝ y : (G→L[ℝ] ℝ)→L[ℝ] ℝ) ∘L (ContinuousLinearMap.apply ℝ (G→L[ℝ] ℝ) x); exact A.map_tsum ((summable_nat_add_iff 1).2 h)
lemma end₁ {A:Type}[NormedAddCommGroup A](f:ℕ→ A)(h:Summable f): (∑' i,f i)= f 0+∑' i,f (i+1):=by simpa only [sum_range_one] using (h.sum_add_tsum_nat_add 1).symm
lemma flopD (p:ℕ→Dice G)(h:Summable p)(x y:G): (∑' i,p i) x y=p 0 x y+∑' i,p (i+1) x y:= ((DFunLike.congr_fun (DFunLike.congr_fun (end₁ p h) x) y) |>.trans (congrArg (p 0 x y+·) (pallD p h x y)))
lemma rest_step (Y:G→L[ℝ] G)(hp:X*Y=1)(n:ℕ)(hq:Summable (pl ι X f n))(ht:Summable (pl ι X f (n+1))) (x y:G):
    rear ι X f n (Y x) (Y y)= f n (ι x) (ι y)+rear ι X f (n+1) x y:=by
       have he (k:ℕ): X^(k+1)*Y=X^k:=by rw [pow_succ,mul_assoc,hp,mul_one]
       let q:= pl ι X f n;
       have ha(z):q (z+1) (Y x) (Y y)= pl ι X f (n+1) z x y:=by
            have h(z':G): (X^(z+1+1)) (Y z')=(X^(z+1)) z':=by rw [← byway, he (z+1)]
            change (f ((z+1)+n)) (ι ((X^(z+1+1)) (Y x))) (ι ((X^(z+1+1)) (Y y)))= _; rw [h,h,show z+1+n=z+(n+1) from by omega]; rfl
       have hv:q 0 (Y x) (Y y) = f n (ι x) (ι y):=by change f (0+n) (ι ((X^1) (Y x))) (ι ((X^1) (Y y)))= _; rw [zero_add,pow_one, ←byway,hp,one_apply_eq_self]; rw [←byway,hp];rfl
       change (∑' i,q i) _ _= _; rw [flopD q hq,hv,add_right_inj]; simp_rw [ha]; -- combine via functional
       let A:Dice G→L[ℝ] ℝ:= ContinuousLinearMap.apply ℝ ℝ y ∘L ContinuousLinearMap.apply ℝ (G→L[ℝ] ℝ) x; exact (A.map_tsum ht).symm
end YM.OPE.Hark
