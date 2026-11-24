import YM.MSbar.Tramp.Pair
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tramp
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Wave MvPolynomial
open AnalyticBridge.VerifiedReset Native.Chart Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable (G:Gauge)(n: Side)
local notation "Π!"=>Positions (Primary n G)
local notation "A"=> Primary n G
local notation "Ω"=> Positions (Cards G n)
local notation "T"=> cards0 G n
local notation "H"=>cardsH G n
local notation "U"=> slide G n
local notation "L"=> Measuring.chart n G
local notation "p!"=>Cacao.Pot A
noncomputable def chant (G:Gauge)(n:Side)(r:ℕ)(p:Pot (Primary n G)) : Pot (Cards G n):= juncture (Ipen G n) (sieve G n p) (light G n r)
lemma garland (p:p!) (v:A)(x:Ω): clue (pderiv (.inl v) (sieve G n p)) x= clue (pderiv v p) (T x):=by
    rw [← tabs, ← tabs, show clue (sieve G n p)=clue p∘ cards0 G n from funext (href G n p)]
    let M:=cards0 G n; rw [fderiv_comp _ (helm p 1|>.contDiffAt.differentiableAt (by norm_num)) M.differentiableAt, M.fderiv]; change fderiv ℝ _ _ (T _)=_; rw [projection1]
lemma vitality (x:Ω)(p:p!)(r:ℕ): clue (chant G n r p) x= Lis.optics r (clue p) (H x) (T x):=by
   let D:= sieve G n p; let E:=light G n r
   have he:chant G n r p=∑ i:Primary n G,pderiv (.inl i) D*pderiv (hinge G n i) E:=by
        unfold chant juncture; rw [Fintype.sum_sum_type]; simp_rw [Ipen,ite_smul]; simp only [zero_smul,one_smul,Finset.sum_const_zero,add_zero, Finset.sum_ite_eq,Finset.mem_univ, ↓reduceIte]
        refine Finset.sum_congr rfl fun x _=>?_; rw [Finset.sum_eq_single_of_mem (.inr (.inr x)) (Finset.mem_univ _),if_pos rfl]; rfl; intro b h hb; rw [if_neg hb]
   rw [he]; let z(i:Primary n G):= choir r (H x) (T x) i; let F:=fderiv ℝ (clue p) (T x); change MvPolynomial.eval x _= F z; rw [spiral z]; -- z typed dependent
   rw [_root_.map_sum,_root_.map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [_root_.map_mul]; change clue _ x*clue _ x = _; rw [show clue _ x=_ from garland G n p i x, show clue _ x= _ from anchorD G n i x r,map_smul]; rw [← tabs]; exact mul_comm ..
lemma zeros (a:ℝ)(s m r:ℕ)(p:p!){C:ℝ}(ha:0≤a)(h:Tokew (Measuring.chart n G) a s (m+1) 0 p C): Tokew (slide G n) a s m 0 (chant G n r p) (2*2^m*(C*tub G a s r (m+1))) :=by simpa only [one_mul,chant] using union_bulk ha (inkSpot G n s a) (sipped G n p a (m+1) s h ha) (supported G n a s r (m+1) ha)
variable {G}{n} (F:Nesting G n)(R:PathData G)(l:Clip)(r p:ℕ){f:ℝ → Wilson.Config G n→ℝ}(he:Trend f F R l p)(hv:r ≤ p)
local notation "Z"=>tariff n p l R F
local notation "Δ"=>PowerSeries.coeff
noncomputable def devotion (F:Nesting G n)(R:PathData G)(l:Clip)(r p:ℕ): Pot (Cards G n) := -∑ i∈ Finset.range r, chant G n (r-i) (PowerSeries.coeff i (tariff n p l R F))
include he hv
lemma pursuit (x:Positions (Cards G n)) : clue (devotion F R l r p) x= fderiv ℝ (clue (PowerSeries.coeff r (tariff n p l R F))) (cards0 G n x) (grad (cardsH G n x)):=by
    let T':=tariff n p l R F; change _ = impulse n G _ _ _; unfold devotion clue; rw [_root_.map_neg,_root_.map_sum,driven R l F p he r hv]; congr 1; refine Finset.sum_congr rfl fun i _=>?_ ; exact vitality .. -- variable hp.
omit he hv
lemma pleasure (a:ℝ)(s m:ℕ)(Y:ℝ)(hb:0≤a)(h:∀ i<r, Tokew (Measuring.chart n G) a s (m+1) 0 (PowerSeries.coeff i (tariff n p l R F)) Y): Tokew (slide G n) a s m 0 (devotion F R l r p) ((∑ i∈Finset.range r, 2*2^m*tub G a s (r-i) (m+1))*Y):=by
    unfold devotion; rw [← neg_one_smul ℝ]; rw [Finset.sum_mul]; let t(i):=2*2^m*tub G a s (r-i) (m+1)*Y; let f(i:ℕ):= chant G n (r-i) (PowerSeries.coeff i (tariff n p l R F)); have hx:=Tokew.total f (Finset.range r) t (ξ:=0) (m:=m) (p:=s) (a:=a) (l:=slide G n) (fun i hi=>?_); exact hx.smoky (-1)|>.delta le_rfl (by simp [t]); refine (zeros _ _ a s m (r-i) _ hb (h i (Finset.mem_range.mp hi))).delta le_rfl ?_; exact le_of_eq (by unfold t; ring)
end YM.MSbar.Tramp
