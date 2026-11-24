import YM.OPE.Mountains.Assembly
import YM.OPE.Log.Uniform
/-!
# Radius denominators at actual power (not log rates)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset Real OPE.Log
open scoped Classical Topology BigOperators ContDiff
set_option quotPrecheck false
variable {G: Gauge}{C:Register G}
variable {I:Type}[Fintype I] {s:Arboreal I} {r:I→ℝ}(D:I→ℕ)(n:ℕ)(p:I→ C.Token)
    {i:I} {a:Finset I}
-- convenient product log independent of lives (root & every internal)
def prestige (s:Arboreal I) (r:I→ℝ) : ℝ:= ∏ i∈s.zones, (1+run (r i))
def listPrice (s:Arboreal I)(p:I→ C.Token)(r:I→ℝ)(n k:ℕ):ℝ:= s.tariff p (n:ℝ) 0 r * s.prestige r^k
variable (he:s.Graduated r)
namespace Graduated
include he
lemma qFine (hi:i∈s.zones):0 < s.ratioAt r i:=div_pos (he.allowed _ hi) (he.allowed _ (s.inward i))
lemma worth (h:s.root∈s.zones):0< s.tariff p (n:ℝ) 0 r:= mul_pos (rpow_pos_of_pos (he.allowed s.root h) _) (prod_pos (fun i hi=> Real.rpow_pos_of_pos (he.qFine (mem_erase.mp hi).2) _))
lemma awards (hp:(s.middle s.zones).Nonempty):0< s.grace r D:=sum_pos (fun i hi=> pow_pos (he.qFine (mem_erase.mp hi).2) _) hp -- orientation
lemma grip (i:I)(hi:i∈s.zones) : log (s.ratioAt r i)=s.stepAt (log ∘ r) i:= Real.log_div (he.allowed _ hi|>.ne') (he.allowed _ (s.inward i)|>.ne')
lemma reward_eq : s.tariff p (n:ℝ) 0 r * s.fee p r s.leaves s.root n=1:=by
    let d:= OPE.sigma (crop p s.leaves); let h:(I→ℝ):= fun i=> -(OPE.sigma (crop p (s.inputs s.zones i)):ℝ) - 0; let T (t:I):=s.ratioAt r t ^ h t; let W:= log ∘ r; let K:=s.tariff p (n:ℝ) 0 r; let H:=s.fee p r s.leaves s.root n; have hz:= he.allowed _ s.initial; have he':0<H:= he.fee_pos p n s.initial; have hK:0<K:= he.worth n p s.initial; have hT(i)(hi:i∈s.middle s.zones):0 < T i:= rpow_pos_of_pos (he.qFine (mem_erase.mp hi).2) _; have ht: s.onset W p s.leaves= Real.log (s.rent p r s.leaves):=by
       unfold rent onset; rw [log_prod]; exact sum_congr rfl fun i _=> (log_pow ..).symm; exact fun i hi=> pow_ne_zero _ (he.allowed _ (s.inward i)|>.ne') -- parse separator
    have hF : ∑ i∈ s.middle s.zones, Real.log (T i)= ∑ i∈ s.middle s.zones,h i * s.stepAt W i:= sum_congr rfl (fun i hi=> by rw [show Real.log (T i)= _ from log_rpow (he.qFine (mem_erase.mp hi).2) (h i), he.grip i (mem_erase.mp hi).2])
    have hG : Real.log (r s.root)^2≥0:=sq_nonneg _ -- unused
    have hx: Real.log K= ((n:ℝ)-d-0)* W s.root+ ∑ i∈ s.middle s.zones,h i*s.stepAt W i:= by
       unfold K tariff; rw [log_mul (rpow_pos_of_pos hz _|>.ne') (prod_pos hT|>.ne'),log_rpow hz]; change _ + log (∏ i∈ s.middle s.zones,T i)= _; rw [log_prod (fun i hi=> hT i hi|>.ne'),hF]; rfl
    have hu:Real.log (K*H)=0:=by
       rw [log_mul hK.ne' he'.ne',hx, show Real.log H= Real.log (s.rent p r s.leaves) - (n:ℝ)*W s.root from (by unfold H fee; rw [log_div (he.rent_pos p|>.ne') (pow_pos hz n|>.ne'),log_pow]; rfl),← ht]; let f(i:I):ℝ:= (OPE.sigma (crop p (s.inputs s.zones i)):ℝ); have hh:s.onset W p s.leaves=d*W s.root+∑ i∈ s.middle s.zones,f i*s.stepAt W i:= s.appearances W p (Action s); rw [hh]; unfold h; simp only [sub_zero,neg_mul, Finset.sum_neg_distrib]; unfold f; ring
    change K*H = 1; exact (Real.exp_log (mul_pos hK he')).symm.trans (by rw [hu,Real.exp_zero])
omit he
private lemma compSum {V:Type*}{a:Finset V}{g:V→ℝ}(hg:∀ i∈a,0≤g i): 1+∑ i∈a,g i ≤ ∏ i∈a,(1+g i):= by -- precedence! this statement parsing requires parentheses?
    induction a using Finset.induction with
    | empty=> simp
    | insert u s he ih=>
       have hh:= hg u (mem_insert_self ..); have hv:=fun i hi=> hg i (mem_insert_of_mem (b:=u) hi); rw [Finset.prod_insert he, Finset.sum_insert he]; specialize ih hv; nlinarith only [mul_nonneg hh (sum_nonneg hv), mul_le_mul_of_nonneg_left ih (show 0 ≤ 1+g u from add_nonneg zero_le_one hh)]
include he
lemma reputation (h:1 ≤ run (r s.root)): 1 ≤ s.fullLife r ∧ s.fullLife r ≤ s.prestige r:=by
    have hp(i)(hi:i∈ s.zones): 0≤run (r i):= (zero_le_one.trans h).trans (he.rising hi)
    refine ⟨h.trans (he.limit s.initial),?_⟩
    have hk: s.fullLife r ≤ ∑ i∈s.zones, run (r i) :=by
       unfold fullLife; let g i:= run (r i); rw [add_comm]; apply le_trans (b:=g s.root +∑ i∈ s.zones.erase s.root,g i) ?_ ((add_sum_erase s.zones g s.initial).le); exact add_le_add (le_refl _) (sum_le_sum (fun i hi=> sub_le_self _ (hp _ (s.inward i))))
    exact hk.trans ((le_add_of_nonneg_left zero_le_one).trans (compSum hp))
lemma max_cost {k m:ℕ}{a:ℝ}(ht:1 ≤ run (r s.root))(hh:k ≤ m)(h: s.fee p r s.leaves s.root n*a ≤ s.fullLife r^k) : a ≤ listPrice s p r n m :=by
    have hp:= he.worth n p s.initial; have hx:= he.reward_eq n p; have hh':= he.reputation ht
    calc a = s.tariff p n 0 r * (s.fee p r s.leaves s.root n*a) :=by rw [← mul_assoc,hx,one_mul]
         _ ≤ s.tariff p n 0 r * s.prestige r^m:= mul_le_mul_of_nonneg_left (h.trans ((pow_le_pow_right₀ hh'.1 hh).trans (pow_le_pow_left₀ (zero_le_one.trans hh'.1) hh'.2 _))) hp.le
-- simplify if apply congr F
end Graduated
end YM.OPE.Arboreal
