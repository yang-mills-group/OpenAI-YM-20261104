import YM.FormalOPE.RG10.MultiGauge.Membership
/-!
 # Agreement of fully-integrated pipeline with genuine `scene` Marked operator
 using all-cost insertion lemma. Common mass and jacobian units multiplied before expectation.
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
variable {G:Gauge}{I J:Type}[Fintype I][Fintype J]
variable {U:Survey G I J}(H: U.Ready){P:ChartRatio G}(L:LocalRatio P)
variable {O:Spending G I}(h:Curtain O)
local notation "Λ"=> evidence _ H.entire
local notation "ν"=> tangent G I
local notation "Δ"=> Direction G I

include L h in
lemma roster_sum (n:ℕ):
 C (budget H) * input Λ ν ((∑ i∈Finset.range (n+1), roll ((i.factorial:ℝ)⁻¹) * (dressing U)^i)*(planting U P * imbed O)) = U.truncation P O n := by
 rw [Finset.sum_mul,map_sum,Finset.mul_sum]; unfold Survey.truncation; apply Finset.sum_congr rfl; intro i hi
 rw [threshold, Finset.mul_sum, Finset.sum_mul, map_sum,Finset.mul_sum]; refine Finset.sum_congr rfl fun p hp=>?_
 let A:= carry (E:=Δ) (∏ i, Tracks.shadow (U.w (p i)))
 let k:ℝ:=(i.factorial:ℝ)⁻¹
 rw [show roll k*(A * tagMass U p)*(planting U P * imbed O) = roll k* (A*(tagMass U p*(planting U P * imbed O))) by ring, rolls]; unfold A; rw [alongside, Survey.print, ← coupon H L h p]; ring
 def weight (P:ChartRatio G) (U:Survey G I J): Ticket Δ := roll ((jacobian P (0:Δ))⁻¹) * (planting U P * exponential (dressing U)) -- roll inverse placement deliberate input parentheses
 def overhead (P:ChartRatio G) (I:Type)[Fintype I]:= jacobian P (0:Direction G I)

include L in
lemma official  : 0<overhead P I:= Finset.prod_pos fun _ _ =>
     (show 0<fee P 0 from lt_max_of_lt_left (by rw [L.anchored,mul_one];exact L.scale))
include L in
lemma checked_up : incline (weight P U):= by
 unfold incline weight roll planting; rw [map_mul, constantCoeff_C, map_mul,initial,mul_one];
 have he:= (official (I:=I) L).ne'
 rw [map_mul,initial,mul_one]; apply Subtype.ext; ext1 x; change (overhead P I)⁻¹ * ((constantCoeff (rise (jacobian P (U:=I)))).val x) = (1:ℝ); rw [←coeff_zero_eq_constantCoeff_apply, rise, coeff_mk]; change _* jet _ 0 _=_; rw [jet_zero]; exact inv_mul_cancel₀ he -- handle jet

include L h in
lemma overalls : C (budget H*overhead P I) * input Λ ν (weight P U * imbed O)=U.imprint P O:= by
 have ha:C (budget H*overhead P I) * input Λ ν (weight P U * imbed O)= C (budget H) * input Λ ν (exponential (dressing U)*(planting U P * imbed O)):= by
    let d:= overhead P I
    rw [weight,mul_assoc, mul_comm (planting U P),mul_assoc,rolls,map_mul]
    rw [mul_assoc,← mul_assoc (C (overhead P I)), ← map_mul C (overhead P I)]; change _= _; rw [show (jacobian P (0:Δ))⁻¹ = (overhead P I)⁻¹ from rfl,mul_inv_cancel₀ (official (I:=I) L).ne', map_one, one_mul]
 rw [ha]; apply PowerSeries.ext; intro n; rw [Survey.imprint,coeff_mk,← roster_sum H L h]
 apply Through.mul (Through.refl _) (keepsThrough _ ((acting (dressing_zero U H) n).mul (Through.refl _))) n le_rfl -- expected R congr type
include L h in
lemma plan : U.ratecard P O=enjoy Λ ν (imbed O) (weight P U):= by
 unfold Survey.ratecard enjoy
 -- avoid asserting invert using constant factor.Law. Unitization.
 let A:=U.imprint P 1; let W:=input Λ ν (weight P U)
 let V:= input Λ ν (weight P U*imbed O); let K:= C (budget H*overhead P I)
 have ht: K*W=A:= by simpa only [label_one,mul_one] using overalls H L (unit (G:=G) (E:=I))
 change U.imprint P O * A⁻¹= V*W⁻¹
 have h₁: constantCoeff (W)≠0:=by rw [show constantCoeff W=1 from underBudget Λ ν (checked_up (U:=U) L)]; exact one_ne_zero
 have ht': A ≠ 0:= fun e=> H.mark L (show constantCoeff A =0 from by rw [e,map_zero])
 apply mul_right_cancel₀ ht'
 conv_rhs=> rw [← ht]
 rw [mul_assoc, PowerSeries.inv_mul_cancel _ (H.mark L),mul_one,← overalls H L h];
 calc
 _ = V * K:=mul_comm _ _
 _ = V*W⁻¹*(K*W):= by
   nth_rw 1 [show V= V*(W⁻¹*W) from by rw [PowerSeries.inv_mul_cancel _ h₁,mul_one]]
   ring
end Stack
end YM.FormalOPE.RG10.MultiGauge
