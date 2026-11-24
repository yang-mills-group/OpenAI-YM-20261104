import YM.FormalOPE.RG10.MarkovChain.Router
/-!
 # Strip a fully future-dependent factor before conditionally normalising
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open Inherit Push.Loops Chart Lattice RG GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open Papers Warp Line Roof
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side}
variable {S:StepData c f} {H:S.patch.Branches S.kernel G}{t:S.Choices}{hf:_root_.Even f.val}{L:Fabric G c} {C:Cloth L}{P:Inside S.ratio}
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "d"=> Pathway (S:=S) (H:=H) (t:=t) (hf:=hf) (C:=C) (P:=P)
namespace Router
local notation "Ω"=> Field (Cloth.choose T0)
local notation "V"=> Field C.choose
local notation "F"=> Cross (G:=G) S P
-- with genuine variable set $F = currently fine indices$
lemma displayed (Λ: Law Ω) (μ:Measure (Cross (G:=G) S P)) [Measure.IsAddHaarMeasure μ] (a:Permit Ω)(y:V): (partialMean Λ d μ a).val y= (fast Λ d).average μ (fun x=> a.val (d (x+pin Λ d y,y))):= Papers.Penn (fast Λ d) μ (translation (fusion Λ d).toLinearMap a) y
lemma presentScale (Λ: Law Ω) (μ:Measure (Cross (G:=G) S P)) [Measure.IsAddHaarMeasure μ] (a:Permit Ω)(b:Permit V): partialMean Λ d μ (a * (translation ( (LinearMap.snd ..) ∘ₗ (d).symm.toLinearMap) b))= partialMean Λ d μ a * b:= by
 apply Subtype.ext; ext1 y
 change (partialMean Λ d μ _).val y= (partialMean Λ d μ _).val y*b.val y; rw [displayed,displayed]
 have he x: (d).symm (d (x+ pin Λ d y,y))= (x+pin Λ d y,y):=(d).symm_apply_apply _
 change (fast Λ d).average μ (fun x=> a.val _ * b.val (_))=_;
 unfold Law.average;
 change (∫ x:F,(a.val _ * b.val (((d).symm (d (x+pin Λ d y,y))).2)) * (fast Λ d).kern x ∂μ)/ _ =_
 simp_rw [he,mul_right_comm _ (b.val y), integral_mul_const, Pi.mul_apply]
 ring
lemma pullOut (Λ: Law Ω) (μ:Measure (Cross (G:=G) S P)) [Measure.IsAddHaarMeasure μ] (a:Ticket Ω)(b:Ticket V): reclose Λ d μ (a * Ancestor b)= (reclose Λ d μ a)*b:= by
 apply PowerSeries.ext; intro n; unfold reclose throughPrice; simp_rw [AddMonoidHom.coe_mk,ZeroHom.coe_mk, coeff_mul, coeff_mk, LinearMap.toAddMonoidHom_coe, map_sum]; apply Finset.sum_congr rfl; intro i _; unfold Ancestor boost; rw [coeff_map]; exact presentScale Λ μ _ _
local notation "B"=> boost (coarse d)
lemma rLine (Λ: Law Ω) (μ:Measure (Cross (G:=G) S P)) [Measure.IsAddHaarMeasure μ] (u A:Ticket Ω)(hv: incline u): reclose Λ d μ (u*A)= reclose Λ d μ (handle u*A)*(boost (coarse d) u):= by
 rw [←pullOut]; congr 1; rw [mul_right_comm, whole hv]
lemma rWeight (Λ: Law Ω) (μ:Measure (Cross (G:=G) S P)) [Measure.IsAddHaarMeasure μ] (u:Ticket Ω)(hv: incline u): reclose Λ d μ u= reclose Λ d μ (handle u) * (boost (coarse d) u):= by simpa only [mul_one] using rLine Λ μ u 1 hv
lemma surround (Λ: Law Ω) (μ:Measure (Cross (G:=G) S P)) [Measure.IsAddHaarMeasure μ] (u A:Ticket Ω)(hv: incline u): delivered Λ d μ A u= delivered Λ d μ A (handle u):= by
 apply (worth (born_transfer Λ d μ hv)).mul_left_cancel
 rw [junior Λ d μ _ hv,rWeight Λ μ _ hv, rLine Λ μ _ _ hv, mul_right_comm, junior Λ d μ _ (seat hv)]
end Router
end YM.FormalOPE.RG10.MarkovChain
