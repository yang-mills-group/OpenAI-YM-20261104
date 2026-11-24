import YM.FormalOPE.RG10.MultiGauge.Variate
/-!
 # base coefficient calculation prior to exponential of coupling-clock weights
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
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
 [MeasurableSpace E][BorelSpace E] (Λ: Law E)(μ:Measure E)[Measure.IsAddHaarMeasure μ]
lemma alongside (c:PowerSeries ℝ)(A:Ticket E): input Λ μ (carry c * A)= c * input Λ μ A:= by
 apply PowerSeries.ext; intro i; unfold input throughPrice carry; simp_rw [AddMonoidHom.coe_mk,ZeroHom.coe_mk, coeff_mk,LinearMap.toAddMonoidHom_coe, coeff_mul, map_sum, coeff_map]
 apply Finset.sum_congr rfl; intro j _; rw [← Algebra.smul_def, map_smul]; rw [coeff_mk]; rfl
lemma rolls (c:ℝ) (A:Ticket E): input Λ μ (roll c * A)= C c * input Λ μ A:= by
 conv_lhs=> rw [show roll (E:=E) c=carry (C c) from (PowerSeries.map_C ..).symm]
 exact alongside Λ μ .. -- split
lemma taking (n:ℕ)(A:Ticket E): input Λ μ (X^n*A)= X^n * input Λ μ A:= by rw [show (X^(n):Ticket E)= carry (X^n) from by rw [map_pow]; simp [carry], alongside]
variable {G:Gauge}{I J:Type}[Fintype I][Fintype J]
variable {U:Survey G I J} (H:U.Ready){P:ChartRatio G}(L:LocalRatio P)
local notation "U0"=> U.target
local notation "W"=> Direction G I
local notation "Z"=> evidence _ H.entire
local notation "ν"=> tangent G I
 def budget {U:Survey G I J}(H:U.Ready) := (∫ x,(evidence _ H.entire).kern x ∂ν)
lemma budget_pos : 0<budget H:= positive (evidence _ (H.entire)) _
variable {O:Spending G I}(h:Curtain O)
include L h in
lemma identify (j:ℕ)(x:W):
 (coeff j (planting U P * imbed O)).val x = integrandSeries (U0 ∘ expLinks G I) (offer P O) j x:= by
 let V:=exponential (advancing (U0 ∘ expLinks G I))
 rw [show planting U P * imbed O = rise (offer P O) * V from ?_,←reading_term,map_mul,coeff_mul,integrandSeries,Zone.mul]
 · apply Finset.sum_congr rfl; intro i _; rw [read_rise,business]
 rw [planting,mul_right_comm,imbed,offer,rise_mul ((Ratio.jacobian_smooth L).of_le le_top) h.germ] -- implicit J

include L h in
lemma registered : C (budget H) * input (evidence _ H.entire) ν (planting U P*imbed O) = PowerSeries.mk (summing P U.target O):= by
 apply PowerSeries.ext; intro i
 rw [coeff_mk, coeff_C_mul]; unfold summing Radial.moment; change budget H * opening ν _ _= _
 have he:= (budget_pos H).ne'
 -- rewrite integrand_eq
 simp_rw [normTerm,← identify (U:=U) L h,← evidence_law (H:=H.entire)]
 simp only [Finsupp.single_eq_same]
 change budget H *((∫ x, (coeff i (planting U P * imbed O)).val x * (evidence U.target H.entire).kern x ∂ν)/ budget H)=_
 field_simp

-- power shift back
include L h in
lemma coupon {k:ℕ}(v:Fin k→J): C (budget H) * input (evidence _ H.entire) ν
 (tagMass U v*(planting U P * imbed O)) = U.basePrint P O v:= by
 have ha:= registered H L (H.readings k h v)
 unfold Survey.basePrint
 rw [← ha, Survey.readMarks, label_mul h (Curtain.gather _ _ (fun i _=> H.localAll (v i))), ← spikeProduct U H]
 rw [show planting U P*( imbed O*(X^k * _))=X^k * (tagMass U v*(planting U P * imbed O)) by ring,taking]
 rw [mul_left_comm (C (budget H))]
 exact (drop_mul (R:=ℝ) k _).symm
end Stack
end YM.FormalOPE.RG10.MultiGauge
