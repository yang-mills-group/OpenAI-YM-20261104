import YM.Integration.WilsonPositionScaleLawThermometerChart

/-! All coefficients of the independently prepared signed triple, including its
zero-field value, on the original Schwartz thermometer test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawThermometerGround
open Function Filter Set Finset PowerSeries Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival XSpace.Cirrus
open WilsonPositionScaleLawThermometerChart (response)
open WilsonPositionScaleLawIndependent (ψ)
open scoped Topology BigOperators Classical
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

include H in
theorem zero (s:ℝ){x:Points 3}(hx:x∈conf 3):coeff 0 (Select.Single (response Z M ν s) x)=0:=by
  let data:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  let P:=Jury.fxt (response Z M ν s) x
  have fixed:P 0=scene x 6:=by
    change Jury.fxt (response Z M ν s) (⟨x,hx⟩:Stage 3).val 0=_
    rw [Jury.exactC]
    exact (Equator.step_dawn (Measure.start Z.scheme Z.criterion 6) (ψ Z M ν s) (Measure.dawn Z.scheme Z.criterion ν M σ hG data.Taylor data.still data.base)) 3 ⟨x,hx⟩
  have no (a:Badge)(ha:a.Nonempty):constantCoeff (batchT P a)=0:=by
    rw [←coeff_zero_eq_constantCoeff_apply,batchT,coeff_mk,fixed]
    exact silent Z.scheme hG hx a ha
  change coeff 0 (b3 (batchT P))=0
  rw [coeff_zero_eq_constantCoeff_apply]
  unfold b3
  simp only [two_smul,map_add,map_sub,map_mul]
  rw [no univ (by decide),no {0,1} (by decide),no {0,2} (by decide),no {1,2} (by decide),
    no {0} (by decide),no {1} (by decide),no {2} (by decide)]
  ring

include H in
theorem printed (s:ℝ)(k:ℕ):
    (Rose.test Z.criterion).applyTo (fun x=>coeff k (Select.Single (response Z M ν s) x))=
      (Rose.cT Z.criterion.cut G Z.criterion.image:ℂ)*coeff k (ψ Z M ν s):=by
  cases k with
  | succ k=>exact WilsonPositionScaleLawThermometerChart.coefficient Z M H ν s k
  | zero=>
    have change:EqOn (fun x=>coeff 0 (Select.Single (response Z M ν s) x)) (fun _=>0) (conf 3):=fun _ h=>zero Z M H ν s h
    rw [Test.apply_eq _ change, ((H.details.normative ν).first.led s).start,mul_zero]
    simp [Test.applyTo]

end YM.Integration.WilsonPositionScaleLawThermometerGround
end
