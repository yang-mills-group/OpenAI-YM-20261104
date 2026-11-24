import YM.Qlocal.Flute
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Bind
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j i q r:ℕ} {n c f :Side}{S:StepData c f} {b α t:ℝ}
open PertExtension PertExtension.Series Sienna Lantern Catch Catch.Clock tether
variable {n m j k r:ℕ}
namespace StampCo
open Laplace.SigmaP PertExtension.Series
variable {v w f g : Word ℝ}
def roll (v:Word ℝ)(n:ℕ)(i:ℕ):= if n ≤ i then v (i-n) else 0
def fold (v:Word ℝ)(n:ℕ) (i:ℕ):= v (i+n)
lemma recovers (h:∀ i<n,v i=0) : roll (fold v n) n=v:= by
 funext i; unfold roll fold; split; rename_i hi; · rw [Nat.sub_add_cancel hi]
 exact (h i (by omega)).symm
lemma back : fold (roll v n) n=v:= by funext i; rw [fold,roll,if_pos (by omega),Nat.add_sub_cancel]
noncomputable abbrev dialect (v : Word ℝ):= PowerSeries.mk v
lemma reversible (h:dialect v=dialect w): v=w:= funext fun i=>by simpa only [dialect, PowerSeries.coeff_mk] using (congr_arg (PowerSeries.coeff (R:=ℝ) i) h)
lemma rolling : dialect (roll v n)= dialect v * PowerSeries.X^n:= by
 ext i; unfold dialect; rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]; rfl
lemma folds : plus f (roll v n)= roll (plus f v) n:= by
 have hs(a b:Word ℝ): dialect (plus a b)=dialect a*dialect b:= by ext i; unfold dialect; rw [PowerSeries.coeff_mk]; rfl
 apply reversible; rw [hs,rolling,rolling,hs,mul_assoc]
lemma suppress (h:∀ i<n, plus f v i=0) (hh:f 0≠0) {i:ℕ}(hp:i<n) : v i=0:= by
 induction i using Nat.strong_induction_on with
 | h i ih=>
    have he := h i hp; rw [plus_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ', Finset.sum_eq_zero, Nat.sub_zero,zero_add] at he; swap; · intro j hj; rw [ih _ (by have := mem_range.mp hj; omega) (by have := mem_range.mp hj; omega),mul_zero]
    exact (mul_eq_zero.mp he).resolve_left hh
lemma lscale (a:ℝ) : plus v (a • f) = a • plus v f:= by ext i; rw [plus_sum,Pi.smul_apply, plus_sum, smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun i hi=>by simp only [Pi.smul_apply, smul_eq_mul]; ring
lemma sunk : plus v (f-g)= plus v f-plus v g:= by funext i; rw [plus_sum,Pi.sub_apply,plus_sum,plus_sum]; simp only [Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
lemma stern : roll (roll v n) m= roll v (n+m):= by apply reversible; rw [rolling,rolling,rolling,pow_add,mul_assoc]
lemma lore (A:ℝ) : roll (A • f) i= A • roll f i:= by ext j; simp only [roll,Pi.smul_apply]; split_ifs <;> simp
lemma urban (h:v=roll w n)(i:ℕ): v (i+n)=w i:=congr_fun ((congr_arg (fun t=>fold t n) h).trans back) i
end StampCo
end YM.Qlocal.Bind
