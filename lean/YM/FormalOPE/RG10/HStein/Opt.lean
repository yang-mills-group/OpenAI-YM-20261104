import YM.FormalOPE.RG10.HStein.Direct

/-! # Recurrences on transferred packet grades
 For use with positive-order relative bulk log coefficients, written in
 the SAME coupling variable. Operator linear tail `opt` still in regulators;
 no analytic-growth or basis claim. Only inputs defined by `Routes.Episode`
 carry an actual formal A WilsonX interpretation WITH the Episode hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.HStein
open Route Route.Bulk PowerSeries Function MeasureTheory Metric Filter Topology Finset
open Multi.Vacuum.Gauss (Row)
open scoped Topology BigOperators Classical
variable {I B J:Type} [Fintype J]
local notation "Y₀" => Packet (I⊕B)
local notation "Y"=> Channel (I⊕B)
variable (q : I→Row J) (V : Channel (I⊕B)) (P : Channel (I⊕B)) (k : ℕ)

lemma hand_sum (p r:Y₀): hand q (p+r)=hand q p+hand q r:= by
 apply all_conf; intro x; simp_rw [_root_.map_add, hand_eq, _root_.map_add]
lemma hand_times (p:Y₀)(c:ℂ): hand q (c • p)= c • hand q p:= by
 apply all_conf; intro x; simp_rw [_root_.map_smul, hand_eq, _root_.map_smul] -- may fail
lemma hand_empty : hand (B:=B) q 0=0:= by unfold hand; simp

def stepwise : Y→ₗ[ℂ] Channel B where
 toFun p:=transfer q p V
 map_add' p r:= by
   unfold transfer; rw [mul_add]; have he (p r:Y):move q (p+r) = move q p+move q r := by apply PowerSeries.ext; intro k; unfold move; simp [_root_.map_add,hand_sum];
   rw [he,add_mul]
 map_smul' c p:= by
   change transfer q (c • p) V=c • transfer q p V; unfold transfer
   rw [mul_smul_comm]; have he (p:Y) : move q (c • p) = c • move q p := by apply PowerSeries.ext; intro k; unfold move; simp [hand_times]
   rw [he,smul_mul_assoc]
lemma send : stepwise q V P=transfer q P V:= rfl
lemma paid : transfer q (PowerSeries.X^k * P) V=(PowerSeries.X^k) * transfer q P V:= by
 unfold transfer; rw [mul_left_comm]; have he(p:Y):move q (PowerSeries.X^k * p) = PowerSeries.X^k * move q p := by apply PowerSeries.ext; intro i; unfold move; simp +contextual [coeff_X_pow_mul']; split <;> simp_all [hand_empty] -- simp may finish
 rw [he,mul_assoc]
protected lemma through_transfer {F Q:Y}(h:Through k F Q): Through k (transfer q F V) (transfer q Q V) := by
 refine Through.mul ?_ (Through.refl _)
 intro i hi; unfold move; rw [coeff_mk,coeff_mk,(Through.mul (Through.refl _) h) i hi]

/-- grade-k transition on a single input coefficient. -/
def opt : Y₀→ₗ[ℂ] Packet B where
 toFun p:= coeff k (transfer q (C p) V)
 map_add' p r:= by rw [_root_.map_add]; simp only [← send, _root_.map_add];
 map_smul' c p:= by
   change coeff k (transfer q (C (c • p)) V)=c • (coeff k (transfer q (C p) V));
   have he : C (c • p) = c • C p:= by apply PowerSeries.ext;intro n; cases n <;> simp
   rw [he]; simp only [← send, _root_.map_smul, coeff_smul];
lemma optical (P:Y₀): opt q V k P=coeff k (transfer q (C P) V):= rfl
lemma rational : coeff k (transfer q P V)=∑ i∈antidiagonal k,opt q V i.2 (coeff i.1 P):= by
 rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=>opt q V j (coeff i P))] -- inspect
 let R := ∑ i∈ range (k+1), PowerSeries.monomial i (coeff i P);
 have h : Through k R P := by
   intro i hi; unfold R; rw [_root_.map_sum]; simp [coeff_monomial,mem_range,hi]
 rw [← HStein.through_transfer q V k h k le_rfl, ← send]; unfold R
 rw [_root_.map_sum,_root_.map_sum]; apply sum_congr rfl; intro j hj
 rw [send, monomial_eq_C_mul_X_pow, mul_comm, paid, coeff_X_pow_mul', if_pos (Nat.le_of_lt_succ (mem_range.mp hj)), optical]
lemma upgrade (X:Y₀)(a:I) [Fintype I] (h:coeff 0 V=0) : opt q V k (MvPolynomial.X (.inl a)*X)= opt q V k (uptick q a X)+∑ i∈antidiagonal k,opt q V i.2 ((uptick q a (coeff i.1 V))*X):= by
 rw [optical,_root_.map_mul,bill q a _ V h]
 have he : journeyD (uptick q a) (C X)=C (uptick q a X):= by apply PowerSeries.ext; intro i; rw [shelves]; cases i <;> simp
 rw [he,← send, _root_.map_add,_root_.map_add]; simp_rw [send]; rw [optical]; -- chooses left wrong
 apply congr_arg (_ + ·)
 rw [rational]; apply sum_congr rfl; intro i _; rw [coeff_mul_C, shelves]

lemma upstairs (X:Y₀)(b:B): opt q V k (MvPolynomial.X (.inr b)*X)=MvPolynomial.X b * opt q V k X:= by rw [optical,_root_.map_mul, coarse q b _ V,sprout,coeff_C_mul]; rfl

@[simp] lemma opt_zero_pay : opt q V 0 1=1:= by
 unfold opt; change coeff 0 (transfer q (C 1) V)=1; have he : transfer q (C 1) V=1:= by unfold transfer income; rw [map_one,mul_one,mul_invOfUnit]; exact (coeff_zero_eq_constantCoeff_apply _).symm.trans (accounting ..)
 rw [he,coeff_zero_one]
lemma opt_one_pay (h : k≠0):opt q V k 1=0:= by
 unfold opt; change coeff k (transfer q (C 1) V)=0; have he : transfer q (C 1) V=1:= by unfold transfer income; rw [map_one,mul_one,mul_invOfUnit]; exact (coeff_zero_eq_constantCoeff_apply _).symm.trans (accounting ..)
 rw [he]; simp [h]
end YM.FormalOPE.RG10.HStein
