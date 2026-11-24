import YM.Integration.WilsonPositionScaleLawThermometerGround

/-! The Taylor polynomial of the genuine signed test is obtained by testing
the independent point-function Taylor polynomial against the original profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawThermometerSmeared
open Function Filter Set Finset PowerSeries MeasureTheory Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawThermometerChart (response)
open WilsonPositionScaleLawIndependent (ψ)
open scoped Topology BigOperators Classical Polynomial
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

theorem paper(q:ℕ)(p:PowerSeries ℂ)(u:ℂ):(trunc (q+1) p).eval u=∑k∈range (q+1),coeff k p*u^k:=by
  exact eval₂_trunc_eq_sum_range u (RingHom.id ℂ) (q+1) p

include H in
theorem smooth (s:ℝ)(j:ℕ):ContinuousOn (fun x=>coeff j (Select.Single (response Z M ν s) x)) (conf 3):=by
  let data:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have base:=(Jury.enrolled ν M Z.scheme Z.criterion σ hG data.Taylor data.still data.base (d:=6))
  exact Select.steady _ ((base.glance (ψ Z M ν s)).light)

include H in
theorem original (s:ℝ)(q:ℕ)(u:ℂ):
    (Rose.test Z.criterion).applyTo (fun x=>(trunc (q+1) (Select.Single (response Z M ν s) x)).eval u)=
      (Rose.cT Z.criterion.cut G Z.criterion.image:ℂ)*(trunc (q+1) (ψ Z M ν s)).eval u:=by
  let φ:=Rose.test Z.criterion
  let f(k:ℕ)(x:Points 3):=coeff k (Select.Single (response Z M ν s) x)
  let c:ℂ:=Rose.cT Z.criterion.cut G Z.criterion.image
  have term(k:ℕ):Integrable (fun x=>φ x*f k x*u^k):=(φ.smearing (smooth Z M H ν s k)).mul_const _
  simp_rw [paper]
  change (∫x,φ x*(∑k∈range (q+1),f k x*u^k))=c*_
  simp_rw [Finset.mul_sum,←mul_assoc]
  rw [integral_finsetSum _ (fun k _=>term k)]
  apply Finset.sum_congr rfl;intro k _
  rw [integral_mul_const]
  change φ.applyTo (f k)*u^k=_
  rw [WilsonPositionScaleLawThermometerGround.printed Z M H ν s k]

end YM.Integration.WilsonPositionScaleLawThermometerSmeared
end
