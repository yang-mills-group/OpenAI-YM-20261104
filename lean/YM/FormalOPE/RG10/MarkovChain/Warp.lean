import YM.FormalOPE.RG10.MarkovChain.Schur
import YM.FormalOPE.RG10.MarkovChain.Factor
/-!
 # Realm of time roofs. Multiplicative detection with transported formal weight (not a Laurent limit).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open PowerSeries Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side}
namespace Warp
open Papers
-- moving polynomial tickets as ring & hom 
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
 def boost (d:E→ₗ[ℝ] F): Ticket F→+* Ticket E:= PowerSeries.map (translation d).toRingHom
lemma caught (d:E→ₗ[ℝ] F)(A:Ticket F)(x:E): Stack.read x (boost d A)=Stack.read (d x) A:= by apply PowerSeries.ext; intro i; rw [reading_term,boost, coeff_map,reading_term]; rfl
lemma exponent (x:E)(A:Ticket E): Stack.read x (Stack.exponential A)=Formal.expander (RingHom.id _) (Stack.read x A):= by
 apply PowerSeries.ext; intro i; rw [reading_term, Stack.exponential, Formal.expander,coeff_mk,coeff_mk,←reading_term]; simp only [map_sum,_root_.map_mul,_root_.map_pow,rollThrough, Formal.press,RingHom.id_apply]
lemma shape {A:Ticket E}(h:incline A)(x:E): constantCoeff (Stack.read x A)=1:= by rw [← coeff_zero_eq_constantCoeff_apply,reading_term,coeff_zero_eq_constantCoeff_apply,h]; rfl
lemma upright {A:Ticket E}(h:∀ i:E,constantCoeff (Stack.read i A)=1): incline A:= by
 apply Subtype.ext; funext i; rw [← coeff_zero_eq_constantCoeff_apply, ← reading_term,coeff_zero_eq_constantCoeff_apply,h]; rfl
lemma preserve_boost (d:E→ₗ[ℝ] F){A:Ticket F}(h:incline A): incline (boost d A):= upright (fun x=> by rw [caught]; exact shape h _)
lemma wrap {A:Ticket E}(h:constantCoeff A=0)(x:E): constantCoeff (Stack.read x A)=0:= by rw [← coeff_zero_eq_constantCoeff_apply,reading_term,coeff_zero_eq_constantCoeff_apply,h]; rfl
lemma boost_exp (d:E→ₗ[ℝ] F)(A:Ticket F): boost d (Stack.exponential A)= Stack.exponential (boost d A):= by apply into; intro i; rw [caught, exponent, exponent,caught]
lemma vacant (d:E→ₗ[ℝ] F){A:Ticket F}(h:constantCoeff A=0): constantCoeff (boost d A)=0:= by
 apply Subtype.ext; funext i; rw [←coeff_zero_eq_constantCoeff_apply,←reading_term,caught,coeff_zero_eq_constantCoeff_apply, wrap h]; rfl
section
variable (S:StepData c f)(H:S.patch.Branches S.kernel G)(t:S.Choices)(hf:_root_.Even f.val){L: Fabric G c} {T:L.loom.Truss}(P:Inside S.ratio)
local notation "T1" => P.join T H t hf
local notation "d" => Blocking.sector S H t hf L P T
 def rightward : Ticket (Field T1) →+* Ticket (Field T):= boost (coarse d)
 def earlier : Ticket (Field T)→+* Ticket (Field T1):= boost ((LinearMap.snd ..) ∘ₗ (d).symm.toLinearMap) -- notation symm trouble
lemma rightward_eq (y)(A:Ticket (Field T1)): Stack.read y (rightward S H t hf P (T:=T) A)=Stack.read (d (0,y)) A:= caught _ _ _
lemma earlier_eq (x:Cross (G:=G) S P)(y)(A:Ticket (Field T)): Stack.read (d (x,y)) (earlier S H t hf P A) = Stack.read y A:= by unfold earlier; rw [caught]; simp
end
end Warp
end YM.FormalOPE.RG10.MarkovChain
