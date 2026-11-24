import YM.RG01Estimate.Gallery
/-!
# Local truncated algebra, quantitative prices at evaluation point

Not a formal coefficient prescription. These are costs for any rendered model with those
coefficients; at finite order can feed to polynomial inverse, log, matched marks etc. Costs
polynomial at finite degrees; for later leaves with polydisplacements pay any + powers at those
post-block gates. No dimension equivalent constants. No new witness.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Series
open Function Filter Set Metric Finset MeasureTheory
open PhysicalNext.Repeat Lantern ConnectedActivityE6 Blaze Shield Brush
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {X E Y H : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
abbrev Policy (X E:Type) := ℕ → X → E
variable {f g : X→E} {h:X→ Y}{m n r : ℕ}{b C V D u : ℝ}{M N : Policy X E}{P : Policy X Y}{x:X}

def trunc (M : Policy X E) (t:ℝ) (r:ℕ)(x:X):= ∑ i∈Finset.range r, t^i • M i x
structure Hon (b:ℝ)(r n:ℕ) (M : Policy X E)(f:X→E) (C:ℝ)(x:X):Prop where
   positive : 0≤ C
   present (i:ℕ) (hi:i<r) : Brush n C 1 (M i) x
   priced : Brush n (|b|^r*C) 1 (fun x=> f x-trunc M b r x) x

-- Product coefficients specified LOW

def convolve (L:E→L[ℝ] Y→L[ℝ] H) (M : Policy X E)(P : Policy X Y) : Policy X H:= fun r x=>
    ∑ i∈ Finset.range (r+1), L (M i x) (P (r-i) x)

def carry (L:E→L[ℝ] Y→L[ℝ] H)(b:ℝ)(r:ℕ) (M : Policy X E)(P : Policy X Y) (x:X):=
    ∑ i∈ Finset.range r, ∑ j∈ Finset.range r,
       if r ≤ i+j then b^(i+j) • L (M i x) (P j x) else 0

omit [NormedSpace ℝ X] [NormedAddCommGroup X] in
lemma multiplies (L:E→L[ℝ] Y→L[ℝ] H) (r:ℕ)(M : Policy X E) (P : Policy X Y) (b:ℝ) :
    L (trunc M b r x) (trunc P b r x)= trunc (convolve L M P) b r x+ carry L b r M P x:= by
   let F(i j:ℕ):= b^(i+j) • L (M i x) (P j x)
   have hp : L (trunc M b r x) (trunc P b r x)= ∑ i∈ range r,∑ j∈range r,F i j:= by
     unfold trunc; rw [map_sum L,_root_.sum_apply]; refine Finset.sum_congr rfl fun i _=> ?_
     rw [_root_.map_sum]; unfold F; simp_rw [map_smul, smul_apply,smul_smul,pow_add]; apply Finset.sum_congr rfl
     intro j _; rw [mul_comm]
   let G n i j:= if i+j=n then F i j else 0
   suffices hs: trunc (convolve L M P) b r x = ∑ i∈range r,∑ j∈range r,∑ n∈range r,G n i j by
      rw [hp,hs]; unfold carry; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i _=>?_); rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; by_cases h:i+j< r
      · unfold G; simp only [sum_ite_eq, Finset.mem_range,h, if_true,h.not_ge,if_false]; rw [add_zero]
      unfold G; simp only [sum_ite_eq, Finset.mem_range,h, if_false,not_lt.mp h, if_true]; rw [zero_add]
   symm
   calc
    _ = ∑ n∈ range r, ∑ i∈ range r, ∑ j∈range r, G n i j := by
        conv_lhs=> arg 2; ext i; rw [Finset.sum_comm]; -- formatting
        rw [Finset.sum_comm]
    _ = _ := by
        unfold trunc convolve; refine Finset.sum_congr rfl fun n hn=> ?_
        rw [Finset.smul_sum]
        rw [← Finset.sum_subset (s₁:=Finset.range (n+1)) (by refine range_mono ?_; exact Nat.succ_le_of_lt (mem_range.mp hn))]
        · refine Finset.sum_congr rfl fun i hi=> ?_
          have he : i ≤ n:= Nat.lt_add_one_iff.mp (mem_range.mp hi); have hx:n-i ∈range r:=Finset.mem_range.mpr ((Nat.sub_le ..).trans_lt (mem_range.mp hn))
          unfold G; rw [Finset.sum_eq_single (n-i), if_pos (show i+(n-i)=n by omega)]; unfold F; rw [show i+(n-i)=n by omega]
          · intro j hj hv; rw [if_neg (by omega)]
          intro h'; exact False.elim (h' hx)
        intro i hi hV; have he' : ¬ i≤ n:= by simp only [Finset.mem_range] at hV; omega
        apply sum_eq_zero; intro j hj; unfold G; rw [if_neg (by omega)]

variable (p:Hon b r n M f C x)
include p
lemma Hon.raise (h:C≤D): Hon b r n M f D x:= ⟨p.positive.trans h,fun i hi=>(p.present i hi).climb h le_rfl,p.priced.climb (mul_le_mul_of_nonneg_left h (pow_nonneg (abs_nonneg _) _)) le_rfl⟩
lemma Hon.more (h:Hon b r n N g D x): Hon b r n (fun i x=> M i x+N i x) (fun x=> f x+g x) (C+D) x:= by
    refine ⟨add_nonneg p.positive h.positive,fun i hi=>(p.present i hi).gathering (h.present i hi),?_⟩
    rw [mul_add]; refine (p.priced.gathering h.priced).shimmy ?_; filter_upwards with y
    unfold trunc; dsimp only; simp only [smul_add,Finset.sum_add_distrib]; abel
lemma Hon.scalar (c:ℝ): Hon b r n (fun i x=>c • M i x) (fun x=> c • f x) (‖c‖*C) x:= by
    refine ⟨mul_nonneg (norm_nonneg _) p.positive,fun i hi=>(p.present i hi).smul c,?_⟩
    rw [mul_left_comm]; refine (p.priced.smul c).shimmy ?_; filter_upwards with y
    unfold trunc; dsimp only; rw [smul_sub,Finset.smul_sum]; simp_rw [smul_smul, mul_comm _ c]
lemma Hon.bar (hx : |b|≤1): Brush n (r*C) 1 (trunc M b r) x:= by
   unfold trunc; rw [show (r:ℝ)*C=∑ _i∈ Finset.range r,C by simp]
   apply Brush.spree _ _ _ zero_le_one; intro i hi
   apply ((p.present i (Finset.mem_range.mp hi)).smul _).climb _ le_rfl
   rw [Real.norm_eq_abs, abs_pow]; exact mul_le_of_le_one_left p.positive (pow_le_one₀ (abs_nonneg _) hx)
lemma Hon.bear (hx : |b|≤1): Brush n (C+r*C) 1 f x:= by
   have he':= (p.priced.climb (mul_le_of_le_one_left p.positive (pow_le_one₀ (abs_nonneg _) hx)) le_rfl).gathering (p.bar hx)
   exact he'.shimmy (Eventually.of_forall fun y=> (sub_add_cancel _ _).symm)

def cost (n:ℕ)(u C D:ℝ):= (u*(C*D))*(3:ℝ)^n
omit p
lemma tint_cost (L:E→L[ℝ] Y→L[ℝ] H)(p:Brush n C 1 f x)(q:Brush n D 1 h x)(hu:‖L‖≤u):
   Brush n ((u*(C*D))*3^n) 1 (fun x=> L (f x) (h x)) x:= by
    have he:= ((p.twins q L).climb (mul_le_mul_of_nonneg_right hu (mul_nonneg p.nonneg q.nonneg)) le_rfl).trim; rw [show (1:ℝ)+(1+1)=3 by norm_num] at he; exact he

include p
variable (q:Hon b r n P h D x)(L:E→L[ℝ] Y→L[ℝ] H) (hx:|b|≤1)(hu:‖L‖≤ u)
def addition (n r : ℕ)(u C D:ℝ) := r*cost n u C D + (cost n u C (D+r*D)+cost n u (r*C) D+r*(r*cost n u C D))
include q hx hu
lemma Hon.twins : Hon b r n (convolve L M P) (fun x=>L (f x) (h x)) (addition n r u C D) x:= by
   let T:= trunc M b r; let W:= trunc P b r; let G x:= L (f x-T x) (h x); let A x':= L (T x') (h x'-W x'); let c:= cost n u C D
   have hC:= p.positive; have hD:= q.positive; have hU : 0 ≤ u:= (norm_nonneg L).trans hu; have h1 : 0 ≤ c := by unfold c cost; positivity
   refine ⟨by unfold addition cost; positivity,fun i hi=> ?_,?_⟩
   · unfold convolve; refine (Brush.spree _ _ (fun _=> c) zero_le_one (fun j hj=>?_)).climb ?_ le_rfl
     · have he : j≤ i:= Nat.le_of_lt_succ (Finset.mem_range.mp hj)
       exact tint_cost L (p.present _ (by omega)) (q.present _ (by omega)) hu
     simp only [sum_const,card_range,nsmul_eq_mul]
     unfold addition; refine (mul_le_mul_of_nonneg_right (show ((i+1:ℕ):ℝ)≤ r by exact_mod_cast (Nat.succ_le_of_lt hi)) h1).trans ?_
     apply le_add_of_nonneg_right; unfold cost; positivity
   have hg := tint_cost L p.priced (q.bear hx) hu; have hp:= tint_cost L (p.bar hx) q.priced hu
   let U (i j : ℕ) y:=if r ≤ i+j then b^(i+j) • L (M i y) (P j y) else 0
   have hκ : Brush n (r*(r*(|b|^r*c))) 1 (carry L b r M P) x:= by
      unfold carry; rw [show (r:ℝ)*(r*(|b|^r*c))= ∑ i∈ range r,∑ j∈ range r,(fun _ _=> |b|^r*c) i j by simp]
      refine Brush.spree _ _ _ zero_le_one (fun i hi=> Brush.spree _ _ _ zero_le_one (fun j hj=> ?_))
      change Brush n _ 1 (U i j) x; unfold U; split_ifs with H
      · apply ((tint_cost L (p.present i (mem_range.mp hi)) (q.present j (mem_range.mp hj)) hu).smul _).climb _ le_rfl
        rw [Real.norm_eq_abs, abs_pow]; exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg _) hx H) h1
      apply (Brush.certified zero_le_one _).climb _ le_rfl; rw [norm_zero]; exact mul_nonneg (pow_nonneg (abs_nonneg _) _) h1
   refine (((hg.gathering hp).gathering hκ).climb ?_ le_rfl).shimmy ?_
   · unfold addition; rw [mul_add (|b|^r)]; -- fragile adjust
     apply le_trans ?_ (le_add_of_nonneg_left (show 0 ≤ |b|^r * ((r:ℝ)*cost n u C D) from mul_nonneg (pow_nonneg (abs_nonneg _) _) (mul_nonneg (Nat.cast_nonneg _) h1)))
     unfold c cost; apply le_of_eq; ring
   filter_upwards with y
   have hs := multiplies (x:=y) L r M P b
   rw [map_sub,_root_.map_sub]; simp only [sub_apply]; rw [hs]; abel
end YM.RG01Estimate.Series
