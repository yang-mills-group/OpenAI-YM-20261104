import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Overtime
/-!
# T-powers Scale budget: overflow and argument replacement at a composition

Estimates every coefficient-weight with the same log-poly tariff. Needs the
actual formal power series composition (literal finite omissions) and paid step clock
error; don't identify two physical comparisons by sameness of leading order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.ScaleCost
open Function Filter Set PowerSeries Asymptotics XSpace
open MS.Book.Program Comparing
open scoped Topology ContDiff BigOperators Classical

lemma blend (q p : Cn) (h : Rooted p) (n : ℕ) (t : ℝ) :
    crop n t (q.subst p) = ∑ k ∈ Finset.range (n+1), crop n t (p^k)*coeff k q := by
  have e (k : ℕ) (hk : k ∈ Finset.range (n+1)) : coeff k (q.subst p)=
      ∑ j∈Finset.range (n+1), coeff k (p^j) * coeff j q := by
    rw [ ← Dframe.Constants.actual_subst q p h, coeff_mk, larger h (show k≤n from Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), ← Nat.range_succ_eq_Iic]
    rfl
  simp_rw [crop_apply,Finset.sum_mul]; rw [Finset.sum_comm (t:= Finset.range (n+1)) (f:=fun k j=> _*coeff k q)]
  exact Finset.sum_congr rfl fun k hk=>by rw [e k hk, Finset.mul_sum]; simp_rw [mul_assoc]

variable {I : Type*} {f q : I→Cn} {T t w g u : I→ℝ} {X : Filter I}
    (ht : ∀ᶠ i in X,1≤T i) (h : ∀ᶠ i in X, |t i| ≤ 1) (paid : t=O[X] g)
    (H : Tunes T X (fun _=>1) q)
private lemma collapse (t : ℝ) (n : ℕ) : crop n t 1=1 := by
  rw [crop_apply,Finset.sum_eq_single 0]
  · simp
  · intro i _ hi; rw [coeff_one,if_neg hi,mul_zero]
  simp
include ht H
lemma powered (n : ℕ) : Tunes T X (fun _=>1) (fun i=>q i ^ n) := by
  induction n with
  | zero=> simp_rw [pow_zero]; exact fun i=>Fare.constant _
  | succ n ih=>
    simp_rw [pow_succ]; simpa only [one_mul] using Tunes.mix ht ih H
lemma submitted (hf : Tunes T X w f) (ha : ∀ i, Rooted (q i)) : Tunes T X w (fun i=> (f i).subst (q i)) := by
  intro n; simp_rw [ ← Dframe.Constants.actual_subst _ (q _) (ha _), coeff_mk, rules,cut,smul_eq_mul ]
  exact Fare.sum ht fun k _=>Fare.cover (powered ht H k n) (hf _)
include paid h
lemma repeated (n p : ℕ) : Fare T X (fun i=> g i ^ (p+1)) (fun i=> crop p (t i) (q i) ^ n - crop p (t i) (q i^n)) := by
  induction n with
  | zero => simp_rw [pow_zero,collapse, sub_self]; exact Fare.nil _
  | succ n ih=>
    have e := Tunes.cuts ht h p H; have hc := Tunes.overflow ht h paid p (powered ht H n) H
    refine (Fare.add ht ((ih.mul e).extend ?_) (hc.extend ?_)).congr ?_
    · exact Eventually.of_forall fun _=> mul_one _
    · exact Eventually.of_forall fun _=>by ring
    exact Eventually.of_forall fun i=>by rw [pow_succ,pow_succ,sub_mul]; abel
omit h paid ht H in
private lemma trading (ht : ∀ᶠ i in X,1≤T i) {z z' : I→ℂ} {u : I→ℝ}
    (h : Fare T X u (fun i=> z i - z' i)) (fz : Fare T X (fun _=>1) z) (fz' : Fare T X (fun _=>1) z') (p : ℕ) :
    Fare T X u (fun i=> z i ^p-z' i^p) := by
  induction p with
  | zero=> simp_rw [pow_zero,sub_self]; exact Fare.nil _
  | succ n ih =>
    refine (Fare.add ht ((ih.mul fz').extend ?_) ((fz.zero_pow n |>.mul h).extend ?_)).congr ?_
    · exact Eventually.of_forall fun _=>mul_one _
    · exact Eventually.of_forall fun _=>one_mul _
    exact Eventually.of_forall fun i=>by rw [pow_succ,pow_succ]; ring

-- price includes coefficient weight `w` (e.g., T^k at grade k of the head)
lemma clock_inserting (hf : Tunes T X w f) (ha : ∀ i,Rooted (q i)) (p : ℕ) (hc : ∀ᶠ i in X, |u i| ≤ 1)
    (fee : Fare T X (fun i=> g i ^ (p+1)) (fun i=> (↑(u i):ℂ)-crop p (t i) (q i))) :
    Fare T X (fun i=> g i^(p+1)*w i) (fun i=> crop p (u i) (f i)-crop p (t i) ((f i).subst (q i))) := by
  -- before rewriting crop in inner
  have e (i : I) : crop p (u i) (f i)-crop p (t i) ((f i).subst (q i)) =
      ∑ k∈Finset.range (p+1), ((u i : ℂ)^k - crop p (t i) (q i^k))*coeff k (f i) := by
    rw [blend (f i) (q i) (ha i), crop_apply]; simp_rw [sub_mul]; rw [Finset.sum_sub_distrib]
  simp_rw [e]
  have hz : Fare T X (fun _=>1) (fun i=> (↑(u i):ℂ)) := by simpa only [pow_one] using (Tunes.budget_b (T:=T) hc 1)
  exact Fare.sum ht fun k hk=> Fare.mul
    ((Fare.add ht (trading ht fee hz (Tunes.cuts ht h p H) k) (repeated ht h paid H k p)).congr
      (Eventually.of_forall fun i=> sub_add_sub_cancel ..)) (hf k)
end YM.FVA2.GradedFar259.ScaleCost
