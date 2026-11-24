import YM.SchemeRG11.Air.Touch
/-! Taylor limits coefficient families. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Wolt
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North
open scoped Classical Pointwise
variable {G:Gauge}{m n:ℕ}{T: Align.Itinerary}{c:ℕ→Sky G n→ℝ}
abbrev Tone(c:ℕ→Sky G n→ℝ):Prop:=∀a,Finishes fun i=>c i a
def rooms (T:Itinerary)(c:ℕ→ Sky G n→ℝ)(i:ℕ)(p:Sky G n):= T.gap i^(inkAge p:ℤ)*c i p
def spry(T: Itinerary)(c:ℕ→Sky G n→ℝ)(m:ℕ)(p:vellum G)(k:ℕ):= aeval (rooms T c k) (cliff inkAge m (inlay G n p))
def stairs (c:ℕ→ Sky G n→ℝ)(m:Size G n)(k:ℕ):=∏ i∈m.support, c k i ^ (m i)
lemma toneS(a:Size G n)(h:Tone c):Finishes (stairs c a):=by unfold stairs; exact Finishes.prod _ _ (fun i hi=>⟨_, (h i).choose_spec.pow _⟩)
lemma stairs_scale (T:Itinerary)(c:ℕ→Sky G n→ℝ)(m:Size G n) (k:ℕ):stairs (rooms T c) m k= T.gap k ^ (bill m) * stairs c m k:=by
 unfold stairs rooms; simp only [mul_pow,Finset.prod_mul_distrib]; congr 1
 unfold bill rankW; rw [zpow_natCast]; simp_rw [zpow_natCast]; rw [Finsupp.weight_apply]; unfold Finsupp.sum; rw [← Finset.prod_pow_eq_pow_sum]; apply Finset.prod_congr rfl; intro i _; rw [←pow_mul]; simp [mul_comm]
lemma tablature (p:Sketch G n)(c:ℕ→ Sky G n→ℝ)(k:ℕ)(s:Finset (Size G n))(h:p.support ⊆ s) : aeval (c k) p=∑ a∈s,p.coeff a* stairs c a k:=by
 trans ∑ a∈p.support,p.coeff a*stairs c a k
 · conv_lhs=>rw [← p.support_sum_monomial_coeff]
   rw [map_sum]; exact Finset.sum_congr rfl fun i _=>by rw [monomial_eq,map_mul]; unfold stairs; simp only [aeval_C,Algebra.algebraMap_self_apply,map_prod,map_pow,aeval_X,Finsupp.prod]
 exact Finset.sum_subset h fun i hi e=>by rw [show p.coeff i=0 from not_ne_iff.mp fun g=>e (mem_support_iff.mpr g),zero_mul]
lemma topp {p:Sketch G n}: ((cliff inkAge m) p).support⊆p.support:=by intro s h; rw [mem_support_iff,keeps_i] at h; split at h <;> first |exact mem_support_iff.mpr h| simp_all
lemma loPrice (p:Sketch G n)(s:Finset (Size G n))(h:p.support⊆s) (m:ℕ)(k:ℕ):
 (aeval (rooms T c k) (cliff inkAge m p))= ∑ i∈s,(if rankW inkAge i ≤ m then p.coeff i else 0)* (T.gap k^(bill i)* stairs c i k):=by rw [tablature _ _ _ s (topp.trans h)]; simp only [keeps_i,stairs_scale]
lemma cost_z (p:vellum G)(c:ℕ→ Sky G n→ℝ)(T: Itinerary)(i:ℕ): aeval (shapeV T c i) p= aeval (rooms T c i) (inlay G n p):=(rise_cast n (rooms T c i) p).symm
lemma hiPrice (p: Sketch G n)(s:Finset (Size G n))(h:p.support⊆s)(m i:ℕ) :
 aeval (rooms T c i) p-aeval (rooms T c i) (cliff inkAge m p)= ∑ a∈s,(if rankW inkAge a≤ m then 0 else p.coeff a)*(T.gap i^(bill a)*stairs c a i):=by
 rw [loPrice _ _ h,tablature (c:=rooms T c) _ _ _ h,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro a _; rw [stairs_scale]; split<;>simp

lemma bond {f:ℕ→ℝ}(h:Finishes f): Wall T (fun _ _=>True) 0 0 (fun i _=> f i):=by
 have hv : ∀ᶠ i in atTop, ‖f i‖ ≤ |h.choose| +1:= h.choose_spec.norm.eventually (ge_mem_nhds (by rw [Real.norm_eq_abs]; linarith))
 refine ⟨_, add_pos_of_nonneg_of_pos (abs_nonneg h.choose) zero_lt_one,hv.mono fun i hi p _=>?_⟩; simp only [zpow_zero,mul_one]; exact hi
lemma hind {f:Ban G}{u:ℤ}{R:ℝ}(h:Sigil T n u f)(hc:Tone c)(m:ℕ): Local T R ((m:ℤ)+1) ((m:ℤ)+1-u) (fun i z=> aeval (shapeV T c i) (f i z)-spry T c m (f i z) i) :=by
 obtain ⟨s,H⟩:=h.safe; unfold spry; simp_rw [cost_z,hiPrice _ s (H _ _)]
 apply Wall.sums _ _
 intro a ha; split
 · next w=>simp only [zero_mul]; exact Wall.zero
 next w=>
 let x:=bill a
 have he:= (h.key a).wall.mul ((Wall.scale x).mul (bond (toneS a hc) : Wall T (fun _ _=>True) 0 0 _))
 have hh:x-m-1≥0:=by have ht:m<rankW inkAge a:=lt_of_not_ge w; unfold x bill; omega
 convert Long.fold (he.inherit (W:=Near T R) (Eventually.of_forall (fun _ _ _=> trivial))) (x-m-1) hh using 1
 · omega
 · dsimp only [x]; abel
 rfl
lemma uplink {f:Ban G}{u:ℤ}{S}(h:Sigil T n u f)(hc:Tone c)(m:ℕ): Streams T S (-u) (fun i z=>spry T c m (f i z) i):=by
 intro y e hp z hz; obtain ⟨s,H⟩:=h.safe; unfold spry; simp_rw [loPrice _ s (H _ _),Finset.mul_sum]
 apply Finishes.sum s; intro a _; by_cases hZ: rankW inkAge a≤ m
 · simp only [hZ,↓reduceIte]; refine (((h.key a).watch y e trivial z hz).mul (toneS a hc)).same (Eventually.of_forall ?_); intro i
   change T.gap i^(bill a - u)*coeff _ _ * _= _; rw [sub_eq_add_neg,zpow_add₀ (T.positive i).ne']; ring
 simp only [hZ,↓reduceIte,zero_mul,mul_zero]; exact Finishes.const _
end YM.SchemeRG11.Wolt
