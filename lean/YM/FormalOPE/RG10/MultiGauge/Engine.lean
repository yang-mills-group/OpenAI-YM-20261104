import YM.FormalOPE.RG10.MultiGauge.Rental
/-!
 # loan transfer and truncation inside coherent weight series
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MultiGauge
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
namespace Stack
open PowerSeries Papers Splice StationaryMarks
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E]
 def roll (p:ℝ): Ticket E:= C (algebraMap ℝ (Permit E) p)
@[simp] lemma load (x:E)(r:PowerSeries ℝ): read x (carry r)=r:= by apply PowerSeries.ext; intro n; unfold read carry; simp_rw [coeff_map]; rfl
@[simp] lemma rollThrough (x:E)(v:ℝ): read x (roll v) = C v:= by rw [roll,read, map_C]; rfl
-- positive-order weight lift, log arguments degree at least one; need not use PS formal convergence
 def exponential (A:Ticket E): Ticket E:= mk fun n=> coeff n (∑ i ∈ Finset.range (n+1), roll ((i.factorial:ℝ)⁻¹)*(A^i))
private lemma powerSupp {A:Ticket E}(hz:constantCoeff A=0)(k:ℕ): ∀ i<k,coeff i (A^k)=0:= by
 induction k with
 | zero=> omega
 | succ k ih=>
   intro i hi; rw [pow_succ,coeff_mul]; apply Finset.sum_eq_zero; intro p hp
   have he:= Finset.mem_antidiagonal.mp hp; rcases eq_zero_or_pos p.2 with h|h
   · simp [h,hz]
   rw [ih _ (by omega),zero_mul]
theorem acting {A:Ticket E}(h:constantCoeff A=0)(n:ℕ): Through n (exponential A) (∑ i ∈ Finset.range (n+1), roll ((i.factorial:ℝ)⁻¹)* (A^i)) := by
 intro i hi; rw [exponential, coeff_mk, map_sum,map_sum]; apply Finset.sum_subset (Finset.range_mono (by omega)); intro j hj hk; simp only [Finset.mem_range, not_lt] at hk; rw [roll,coeff_C_mul,powerSupp h j i (by omega),mul_zero]
@[simp] theorem initial (A:Ticket E): constantCoeff (exponential A)=1:= by simp [exponential,roll]

variable [FiniteDimensional ℝ E]
-- lift actual negative pricing jets after Gaussian quadratic extracted
 def advancing (A:E→ℝ): Ticket E:= drop 2 (-(rise A))+ C (coeff 2 (rise A))
lemma levels (A:E→ℝ)(x:E)(j:ℕ): coeff j (read x (advancing A))= layers A j x:= by
 rw [reading_term,advancing,map_add,coeff_C, drop,coeff_mk,map_neg]; unfold layers; split
 · rename_i h; change j=0 at h; subst j; simp; -- simp subalg
 rename_i h
 change (-(coeff (2+j) (rise A))+0: Permit E).val x=_
 rw [add_zero]; simp [←reading_term,read_rise,Nat.add_comm 2 j]
lemma advancing_zero (A:E→ℝ): constantCoeff (advancing A) = 0:= by simp [advancing,drop]
lemma book (A:E→ℝ)(x:E)(j k:ℕ): coeff j (read x ((advancing A)^k))= Zone.TaylorPow (layers A) k j x:= by
 induction k generalizing j with
 | zero => simp [Zone.TaylorPow]
 | succ k ih=> simp [pow_succ, -map_pow,map_mul, coeff_mul, Zone.TaylorPow, Zone.mul, levels, ih]
lemma business (A:E→ℝ)(x:E)(j:ℕ): coeff j (read x (exponential (advancing A))) = expsum (layers A) j j x:= by
 rw [reading_term,exponential,coeff_mk,←reading_term]; simp_rw [map_sum,map_mul]; unfold expsum; apply Finset.sum_congr rfl; intro i hi; rw [rollThrough,coeff_C_mul,book]
end Stack
end YM.FormalOPE.RG10.MultiGauge
