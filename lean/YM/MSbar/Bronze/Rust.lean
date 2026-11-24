import YM.MSbar.Bronze.Canyon
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bronze
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c: Side}(F:Nesting G c)(R : PathData G)(J:Bed)(p:Clip)
local notation "Y"=>Primary c G
local notation "T"=> Measuring.chart c G
local notation "X"=> Positions (Primary c G)
local notation "Q"=> rim (collectT c R p)
open MvPolynomial AnalyticBridge.VerifiedReset Work.F03 Work.F08 Next.Free
variable (s:G.ColorIndex) {θ η C' κ Λ ε b D t V A w:ℝ}{n₀ m q a':ℕ}
variable (h:R.Bounds p θ C' Λ)(ht:Attached J R)(hs:Bid.Sworn J c G)(he:Floor J p c ε D)
open UVNext.PricedKernels
noncomputable def oer (a:ℝ):= (Next.Free.delta_budget 1 a).choose
noncomputable def apron (a v:ℝ):= Fintype.card (TypeFace 2) * oer a * (Fintype.card (TypeFace 2)*v) * dC 1 a
lemma rust (H:J.metric.strip η C')(hv:0≤η)(h0:0≤ C')(x:Body 1 c): (∑ y:Body 1 c, gained η x.1 y.1 * |Precision.K (J.metric.acts c) x y|) ≤ apron η C':=by
    have he:= (delta_budget 1 η).choose_spec; have hk₁ : Annuity (site c _) (site c _) (Exterior.d 1 c).transpose η (Fintype.card (TypeFace 2)*oer η):=by
        have hp:=Annuity.paid_site (strip_trans he.2) hv c; rw [acts_trans] at hp; exact hp
    have hp:= (Annuity.paid_site H hv c); have ht:= delta_paid c 1 η hv; exact (((hk₁.times hp hv (by positivity)).times ht hv (dC_nonneg ..)) x)
include h ht hs he
lemma ravel (hp:Premier (main c p R))(i j:Y): buoy (clue (ink c p R)) 0 [i,j]= if i.2=j.2 then (Precision.K (J.metric.acts c)) i.1 j.1 else 0:=by
    rw [← finches R J p h ht hs he]; let F:=clue (ink c p R); rw [← ion R p hp,stream F i j (helm _ 2|>.contDiffAt)]; unfold Midpoint.cell sun; simp only [brand,curr]; rfl
lemma comb (hp:Premier (main c p R))(H:J.metric.strip η V)(hη:0≤η)(hb:0≤b)(ht':t+b≤η)(hx:0≤t)(hA:0≤ A)(hV:0≤V)(hq:∀ m:ℕ,(1+(m:ℝ))^n₀ ≤ A*Real.exp (t*m))(i:Y): cog T b n₀ (ink c p R) 1 i ≤ A*apron η V:=by
    have he (j:Primary c G): swipe T b n₀ [i,j]≤ A*gained η i.1.1 j.1.1:=by
        let k:=separation i.1.1 j.1.1; have hp:extent (Whisk.zone T ∅ [i,j])≤k:=by apply Whisk.yard; intro x hx y hy; simp [Whisk.zone] at hx hy; rcases hx with hx|hx <;> rcases hy with hy|hy <;> subst_vars <;> first | (rw [separation_self]; omega) | exact separation_comm _ _|>.le | rfl -- dangerous subst
        apply (w_more hp hb n₀).trans; unfold liftW gained; refine (mul_le_mul_of_nonneg_right (hq k) (Real.exp_pos _).le).trans ?_; rw [mul_assoc,← Real.exp_add]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) hA; rw [← add_mul]; exact mul_le_mul_of_nonneg_right ht' (by positivity)
    rw [← scored]; change (∑ j:Y, |buoy _ _ _| * swipe _ _ _ _) ≤ _
    have hx : (∑ j:Primary c G,|buoy (clue (ink c p R)) 0 [i,j]| *gained η (T i) (T j))≤ apron η V:=by
         rw [Fintype.sum_prod_type]; simp_rw [ravel R J p h ht hs ‹_› hp]; apply le_trans (le_of_eq ?_) (rust J H hη hV i.1); apply Finset.sum_congr rfl; intro j _; rw [Finset.sum_eq_single i.2]; simp [ Measuring.chart, mul_comm]; intro b _ hb; simp only [if_neg (Ne.symm hb),abs_zero,zero_mul]; simp
    refine le_trans (Finset.sum_le_sum (g:=fun j:Primary c G=> A*(|buoy (clue (ink c p R)) 0 [i,j]| *gained η (T i) (T j))) ?_) ?_; swap;· rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hx hA
    intro j hj; exact (mul_le_mul_of_nonneg_left (he j) (abs_nonneg _)).trans_eq (by rw [mul_left_comm]; rfl)
lemma chronos (hp: Premier (main c p R))(H:J.metric.strip η V)(hη:0≤η)(hb:0≤b)(ht':t+b≤η)(hx:0≤t)(hA:0≤ A)(hV:0≤V)(hq:∀ n:ℕ,(1+(n:ℝ))^n₀ ≤ A*Real.exp (t*n))(m:ℕ)(hw:0<w) : Tin T b n₀ m w (ink c p R) (w^2*(A*apron η V)):=by
    have hi:0 ≤ apron η V:=by
       have hu:0≤oer η:=(delta_budget 1 η).choose_spec.1.le; unfold apron; have ht:=dC_nonneg 1 η; positivity
    refine ⟨by positivity,fun j hj i=>?_⟩; by_cases hh:j=1
    · subst j; apply (comb R J p h ht hs he hp H hη hb ht' hx hA hV hq i).trans; apply le_of_eq; field_simp
    refine le_trans (le_of_eq ?_) (div_nonneg (show 0≤w^2*(A*apron η V) by positivity) (pow_nonneg hw.le _)); -- wait le_of_eq goal cog=0 direction
    rw [←scored]; unfold ink; refine (Whisk.stitch j ?_).trans (spool j)
    intro l hl; have hv0: (i::l).length≠2:=by simp [hl]; omega
    rw [CrossH.ports (collectT c R p) _ (show ContDiffAt ℝ (↑(2:ℕ)) _ 0 from ((hp.line (tint G _).toContinuousLinearMap).1.of_le le_top)) (by decide) _ (by simp),if_neg hv0,abs_zero,zero_mul]
end YM.MSbar.Bronze
