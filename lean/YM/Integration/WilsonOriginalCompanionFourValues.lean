import YM.Integration.WilsonOriginalCompanionBeforeRoster
import YM.Integration.WilsonOriginalCompanionSignedTwin
import YM.Integration.WilsonThermometerOccupiedGallery
import YM.Integration.WilsonThermometerOccupiedLinear

/-! The true signed canonical hard difference is a divided linear sum of four entire original inventories. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionFourValues
open Function Finset Filter MeasureTheory Lattice Wilson RG Source QuadraticLocal QuadraticLocal.Earn Marker
open Extra.Histories Extra.Trajectories PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonThermometerOccupiedGallery WilsonThermometerOccupiedInterpolation
open WilsonThermometerUnitFilingCoarse
open private sub from YM.Integration.WilsonOriginalCompanionSignedTwin
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N per f u:ℕ}{X I:Type}{o:Fin 3→Site (R.family.side f per)}
local notation "P"=>R.family.path.rep N per f
local notation "J"=>Stock.census (Fin 3)
theorem original (D:Gallery X I o (P) (J))(x:X)(w:Fin 3→ℝ)(wp:∀v,0<w v)(uF:u≤f)
    (s:(J).Mode)(T cap:ℝ)(large:1≤T)(live:Integrable (D.density x) (prior G _))
    (fund:∀z:ℂ,‖z‖≤3*T → (gallery z D).K.Paid w (P).p.B (P).p.supportExponent 1)
    (nodes:∀z:ℂ,‖z‖≤3*T → Integrable ((gallery z D).density x) (prior G _) ∧
      Poly.toll w s*‖reading R (N:=N) (fun U=>((gallery z D).density x U).part s) u uF‖≤cap):
    let Y:=fun U=>(D.density x U).part s-(P).eval U*(Poly.pass (D.E.log x U)).part s
    Integrable Y (prior G _) ∧ Poly.toll w s*‖reading R (N:=N) Y u uF‖≤10*cap/T:=by
  intro Y
  let real:=fun U=>(D.density x U).part s
  let regular:=fun U=>((P).eval U:ℂ)*(Poly.pass (D.E.log x U)).part s
  have tp:0<T:=zero_lt_one.trans_le large
  let z(v:Fin 4):ℂ:=if v=0 then 0 else if v=1 then T else if v=2 then 2*(T:ℂ) else 3*(T:ℂ)
  have within(v:Fin 4):‖z v‖≤3*T:=by
    fin_cases v <;> simp [z,abs_of_nonneg tp.le] <;> linarith
  let F(v:Fin 4):Config G (R.family.side f per)→ℂ:=fun U=>((gallery (z v) D).density x U).part s
  have inc(v:Fin 4):Integrable (F v) (prior G _):=(Poly.get s).integrable_comp (nodes (z v) (within v)).1
  have used(v:Fin 4):Poly.toll w s*‖reading R (N:=N) (F v) u uF‖≤cap:=(nodes (z v) (within v)).2
  have funded (t:ℂ)(hit:t∈({0,(T:ℂ),2*(T:ℂ),3*(T:ℂ)}:Finset ℂ)):
      (gallery t D).K.Paid w (P).p.B (P).p.supportExponent 1:=by
    apply fund
    simp only [mem_insert,mem_singleton] at hit
    rcases hit with rfl|rfl|rfl|rfl <;> simp [abs_of_nonneg tp.le] <;> linarith
  have point(U):real U=fitted T⁻¹ (F 0 U) (F 1 U) (F 2 U) (F 3 U):=by
    have same:=congrArg (fun a:Poly (J)=>a.part s)
      (WilsonThermometerOccupiedGallery.field D x U w wp T⁻¹ T 1 (inv_mul_cancel₀ tp.ne') funded)
    exact same
  have zero:F 0=regular:=by
    funext U
    exact congrArg (fun a:Poly (J)=>a.part s) (WilsonThermometerOccupiedGallery.origin D x U w wp (funded 0 (by simp)))
  have ir:Integrable real (prior G _):=(Poly.get s).integrable_comp live
  have isoft:Integrable regular (prior G _):=zero ▸ inc 0
  refine ⟨ir.sub isoft,?_⟩
  let val(v:Fin 4):ℂ:=reading R (N:=N) (F v) u uF
  have plus:=WilsonThermometerOccupiedLinear.earlier R (N:=N) T⁻¹ real F inc point uF
  have price(v:Fin 4):‖val v‖≤cap/Poly.toll w s:=(le_div_iff₀ (Poly.worth wp s)).2 (by simpa [val,mul_comm] using used v)
  have bill:=WilsonThermometerOccupiedInterpolation.bill T⁻¹ (inv_nonneg.mpr tp.le) (inv_le_one_of_one_le₀ large)
    (val 0) (val 1) (val 2) (val 3) _ (price 0) (price 1) (price 2) (price 3)
  rw [sub R real regular ir isoft uF,plus,←zero]
  apply (mul_le_mul_of_nonneg_left bill (Poly.worth wp s).le).trans_eq
  field_simp [(Poly.worth wp s).ne',tp.ne']

end YM.Integration.WilsonOriginalCompanionFourValues
end
