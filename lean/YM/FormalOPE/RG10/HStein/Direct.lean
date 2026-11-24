import YM.FormalOPE.RG10.HStein.Zap
/-! # Power-series Stein formula of ONE formal normalized step

SI units reserved.Chosen pre-dictionary R gear. All orders Ok.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.HStein
open PowerSeries Function MeasureTheory Metric Filter Topology Finset
open Route Route.Bulk Multi.Vacuum.Gauss Primitives.GCC
open scoped Topology BigOperators ContDiff Classical
variable {I B J K:Type} [Fintype J]

local notation "A"=> Packet K
local notation "W"=> Channel K
section exp
variable {k n:ℕ} {V:Channel K} (L:Derivation ℂ (Packet K) (Packet K))
def journeyD : Derivation ℂ (Channel K) (Channel K) where
 toFun p:= PowerSeries.mk fun i=> L (coeff i p)
 map_add' a b:= by ext; simp
 map_smul' c a:= by ext; simp
 map_one_eq_zero':= by ext i:1; cases i <;> simp
 leibniz' a b:= by
    apply PowerSeries.ext; intro i; change coeff i (PowerSeries.mk (fun i=> L (PowerSeries.coeff i (a*b))))=coeff i (a*(mk (fun i=> L (coeff i b)))+b*(mk (fun i=> L (coeff i a))))
    simp only [coeff_mk, _root_.map_add,smul_eq_mul,coeff_mul,_root_.map_sum,Derivation.leibniz, sum_add_distrib]; congr 1; -- times swapped sum
    exact Finset.Nat.sum_antidiagonal_swap (f:=fun u:ℕ×ℕ=> coeff u.1 b * L (coeff u.2 a)) -- guess
lemma shelves (V:Channel K): coeff k (journeyD L V)=L (coeff k V):= by simp [journeyD]
lemma respects {U:Channel K}(h: Through k U V): Through k (journeyD L U) (journeyD L V):= fun i hi=> by rw [shelves,shelves,h i hi]
private def finite (V:Channel K)(n:ℕ):= ∑ i∈ Finset.range (n+1), (i.factorial:ℂ)⁻¹ • (V^i)
lemma freely (h:coeff 0 V=0) (hk:k≤n): Through k (advance V) (finite V n):= by
 intro i hi; have he : constantCoeff V = 0:=(coeff_zero_eq_constantCoeff_apply _).symm.trans h
 obtain ⟨P,hP⟩:=X_dvd_iff.mpr he
 rw [advance,coeff_mk,finite,_root_.map_sum]; simp_rw [coeff_smul]; apply Finset.sum_subset (Finset.range_mono (by omega)); intro j _ hu;
 rw [hP,mul_pow,coeff_X_pow_mul', if_neg (show ¬j ≤ i by contrapose! hu; simpa using hu),smul_zero]

lemma sail (V:Channel K) (n:ℕ) : journeyD L (finite V (n+1))=finite V n * journeyD L V:= by
 let D:= journeyD L; unfold finite;
 rw [_root_.map_sum, Finset.sum_range_succ', Finset.sum_mul]; rw [pow_zero, Nat.factorial_zero, Nat.cast_one,inv_one,one_smul,Derivation.map_one_eq_zero, add_zero];
 apply sum_congr rfl; intro i _; rw [show (journeyD L) (_ • _)= _ from (show journeyD L ((↑(i+1).factorial:ℂ)⁻¹ • V^(i+1)) = ((↑(i+1).factorial:ℂ)⁻¹) • D (V^(i+1)) from _root_.map_smul D.toLinearMap _ _), Derivation.leibniz_pow, show i+1-1=i from Nat.add_sub_cancel ..];
 -- scalar factorial handling
 let p:=V^i * journeyD L V; change ((↑(i+1).factorial:ℂ)⁻¹) • ((i+1) • p)=_; rw [smul_mul_assoc];
 rw [show (i+1) • p = (↑(i+1:ℕ):ℂ) • p from ?_, smul_smul];
 · push_cast [Nat.factorial_succ]; field_simp [show (↑i+1:ℂ)≠0 from by exact_mod_cast Nat.succ_ne_zero i]; rfl
 exact (Nat.cast_smul_eq_nsmul ℂ (i+1) p).symm

lemma shift (h: coeff 0 V=0) : journeyD L (advance V)= advance V * journeyD L V:= by
 apply PowerSeries.ext; intro i
 rw [respects L (freely h (Nat.le_succ i)) i le_rfl,sail]; exact (Through.mul (freely h (le_refl i)) (Through.refl _)).symm i le_rfl
end exp

variable [Fintype I]
local notation "A₀"=> Packet (I⊕B)
local notation "T"=> Channel (I⊕B)
local notation "D"=> journeyD
variable (q: I→Row J)
open MvPolynomial (aeval)
variable (a:I)(x: B)
abbrev sprout (a:K) : Channel K:= PowerSeries.C (MvPolynomial.X a)
omit [Fintype I] in
lemma paid_coarse (p:A₀): hand q (MvPolynomial.X (Sum.inr x)*p)=MvPolynomial.X x *hand q p:= by
 apply Route.all_conf; intro y; rw [Bulk.hand_eq, _root_.map_mul (MvPolynomial.aeval (R:=ℂ) y), Bulk.hand_eq,lobby,lobby]; simp_rw [map_mul,HStein.average,MvPolynomial.aeval_X]; exact integral_const_mul ..
variable (p v:Channel (I⊕B))
lemma single : move q (sprout (.inl a)*p)=move q (journeyD (uptick q a) p):= by apply PowerSeries.ext; intro i; unfold move; rw [coeff_mk,coeff_mk,sprout,coeff_C_mul,steam,shelves] -- order
omit [Fintype I] in
lemma coarse : transfer q (sprout (.inr x)*p) v=sprout x * transfer q p v:= by
 let f:= advance v*p
 have he : move q (sprout (.inr x)*f)=sprout x*move q f:= by apply PowerSeries.ext;intro i; unfold move sprout; rw [coeff_mk,coeff_C_mul,coeff_C_mul,coeff_mk,paid_coarse]
 unfold transfer; rw [mul_left_comm (advance v),he,mul_assoc]
/-- Full Markov denominator. Stein commutator after $V` positive weight. No room shortcuts on
 higher tangled. Predictor must interpret `V` as in `Episode.Supply` including Jacob-log. -/
theorem bill (h:coeff 0 v=0) : transfer q (sprout (.inl a)*p) v =
    transfer q (D (uptick q a) p+D (uptick q a) v * p) v:= by
 unfold transfer; rw [mul_left_comm (advance v),single,Derivation.leibniz, shift _ h];
 simp_rw [smul_eq_mul]; congr 2; ring
end YM.FormalOPE.RG10.HStein
