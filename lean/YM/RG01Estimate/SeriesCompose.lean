import YM.RG01Estimate.SeriesPower
/-! # Local substitution; normed Taylor output in one represented normalization.
 Numeric Cost purchase only in stage pre-payment, finite order. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Series
open Function Filter Set Metric Finset MeasureTheory
open PhysicalNext.Repeat Lantern ConnectedActivityE6 Blaze Shield Brush RealTaylor
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {n k m l r : ℕ} {b u v t : ℝ} {z : X}
variable (F:ℝ→ℝ)
def extend (x : ℝ × ℝ):= F x.1
def coeff (i:ℕ):= piece (extend F) i 0
def remainder (i:ℕ)(x:ℝ):= pages (extend F) i (x,0)
lemma compose_budget (s:Set ℝ) (h:∀ x∈ball 0 u, Brush n t 1 F x) (x : ℝ×ℝ)(hp:x∈ corridor u s): Brush n t 1 (extend F) x:= by
   let L:=ContinuousLinearMap.fst ℝ ℝ ℝ
   have he:= Brush.reading L (h x.1 hp.1) (ContinuousLinearMap.norm_fst_le ..); rw [one_mul] at he; exact he
lemma expansion (h:∀ x∈ball 0 u, Brush (n+r) t 1 F x)(v:ℝ)(hp:v∈ball 0 u):
    F v=(∑ i∈ Finset.range r, v^i* coeff F i)+v^r * remainder F r v ∧ Brush n t 1 (remainder F r) v:= by
  have hv x (hh:x∈corridor u (Set.univ:Set ℝ)):=compose_budget F Set.univ h x hh
  let L:= ContinuousLinearMap.inl ℝ ℝ ℝ; have hx:(v,(0:ℝ))∈corridor u (Set.univ:Set ℝ):= ⟨hp,Set.mem_univ _⟩
  have hL:‖L‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=>by simp [L])
  have ht:= Brush.reading L (show Brush n t 1 _ (L v) from projected (extend F) Set.univ u isOpen_univ (v,(0:ℝ)) hx r hv) hL; rw [one_mul] at ht
  exact ⟨RealTaylor.priced (extend F) Set.univ u isOpen_univ (v,0) hx r hv,ht⟩

lemma negligible (f : X→ℝ)(p:Brush n (u* |b|) 1 f z)(k:ℕ): Brush n ((u*|b|)^k) (k:ℝ) (fun x=> f x^k) z:= by
   induction k with
   | zero=> simpa only [pow_zero,norm_one,Nat.cast_zero] using! Brush.certified (k:=n) (x:=z) (show (0:ℝ)≤0 from le_refl _) (1:ℝ)
   | succ i ih=> simp_rw [pow_succ,Nat.cast_add,Nat.cast_one]; exact ih.paints p
variable {f:X→ℝ} {P:Policy X ℝ} (A:Hon b r n P f t z) (hx: P 0 =ᶠ[𝓝 z] 0)
def lift (F : ℝ→ℝ)(r:ℕ)(M : Policy X ℝ)(j:ℕ) (x:X):= ∑ i∈ Finset.range r, coeff F i * mulPow M i j x

-- pays R⁻¹ and log uniformly with centered constant one in the denominator model.
-- Strip radius u is a FREE variable. Exposes comparison in normalized derivatives and keeps the scalar portraits.
-- telescope of higher powers only in finite polynomial, no Cauchy assumption on b.
def desk (F:ℝ→ℝ)(r n:ℕ)(t v:ℝ) :=
      (∑ i∈ Finset.range r, ‖coeff F i‖ * pricedPow i n r t)+ (r*t+t)^r* clump n (t+r*t) v*(1+((r:ℝ)+1))^n -- `(r+1)` casts edit
include A hx
lemma Hon.compose (he:∀ x∈ball 0 u, Brush (n+r) v 1 F x)(hr:0<r)(h:|b|≤1)(hm: (r*t+t)* |b| < u) :
      Hon b r n (lift F r P) (F ∘ f) (desk F r n t v) z := by
   let s i y:= f y^i; let q i:= mulPow P i
   let a x:= ∑ i∈ Finset.range r, coeff F i • s i x
   let t' i:= ‖coeff F i‖* pricedPow i n r t
   have hA : Hon b r n (lift F r P) a (∑ i∈range r,t' i) z:= by
      apply Hon.sum_pol (f:=fun i x=> coeff F i • s i x)
         (p:=fun i j x=> coeff F i • q i j x) (C:=t')
      exact fun i _=> (A.powers hr h i).scalar _
   have hx' := A.closed hr h hx; have hp : f z∈ball 0 u:= mem_ball_zero_iff.mpr (hx'.bound.trans_lt hm)
   have hv:=expansion F he _ hp
   have hα:= composite (A.bear h) hv.2
   let R:= (r*t+t:ℝ)^r* clump n (t+r*t) v*(1+((r:ℝ)+1))^n
   let g y:= (f y)^r* remainder F r (f y)
   have ht : 0 ≤ R := mul_nonneg (mul_nonneg (pow_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) A.positive) A.positive) r) hα.nonneg) (by positivity)
   have hz:= ((negligible f hx' r).paints hα).trim
   have hZ : Hon b r n (fun i _=>0) g R z:= by
      refine ⟨ht,fun i hi=> ((Brush.certified zero_le_one _).climb (by simpa) le_rfl),?_⟩
      unfold Series.trunc; simp only [smul_zero,sum_const_zero,sub_zero]; apply hz.climb (le_of_eq ?_) le_rfl; unfold R; rw [mul_pow]; ring
   have hz : (∑ i∈range r,t' i)+R=desk F r n t v:=rfl
   rw [← hz]
   refine (hA.more hZ).shift ?_ (fun i _=> Eventually.of_forall fun _=> (add_zero _).symm)
   filter_upwards [(A.bear h).smooth.continuousAt (isOpen_ball.mem_nhds hp)] with x hx
   change F (f x)= a x+g x; rw [(expansion F he (f x) hx).1]; unfold a g s; simp only [smul_eq_mul]; congr 1; apply Finset.sum_congr rfl; intro i _; exact mul_comm ..

open Laplace Lattice
omit A hx
lemma pay_desk {G:Gauge}{L:Side}{f:ℝ→ℝ}(n r:ℕ)(h:Cookie G L f)(c:ℝ): Cookie G L (fun x=> desk F r n (f x) c):= by
    have hs(s:Finset ℕ):Cookie G L (fun x=> ∑ i∈s, ‖coeff F i‖ * pricedPow i n r (f x)):= by
        induction s using Finset.induction_on with
        | empty=> simp_rw [sum_empty]; exact Cookie.const _
        | insert i s hi H=> simp_rw [sum_insert hi]; exact ((Cookie.const _).pays (paid_pow h ..)).joins H
    let ht:= (Cookie.const (r:ℝ)).pays h
    exact (hs (range r)).joins ((((ht.joins h).pow r).pays ((h.joins ht).lump (Cookie.const c) n)).pays (Cookie.const _))
end YM.RG01Estimate.Series
