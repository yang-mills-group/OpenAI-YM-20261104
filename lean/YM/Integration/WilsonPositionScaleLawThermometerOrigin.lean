import YM.Integration.WilsonPositionScaleLawThermometerSmeared

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawThermometerOrigin
open Function Filter Set Finset PowerSeries MeasureTheory Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Rose PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawThermometerChart (response)
open WilsonPositionScaleLawIndependent (ψ)
open scoped Topology BigOperators Classical Polynomial
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)


include H in
theorem clock : ψ Z M ν 0 = PowerSeries.X := by
  let data := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  change (Reg.Choice.choice (ν-0) Z.criterion M).subst (Reg.Token.conversion ν Z.criterion M) = _
  rw [sub_zero]
  exact (Reg.Faith.hearty ν Z.scheme Z.criterion σ M hG data.Taylor data.still data.base).cost.right

theorem initial (q : ℕ) (u : ℂ) : (trunc (q+2) (PowerSeries.X:PowerSeries ℂ)).eval u = u := by
  rw [show q+2=(q+1)+1 from rfl,WilsonPositionScaleLawThermometerSmeared.paper,Finset.sum_eq_single 1]
  · simp
  · intro i _ other
    simp [PowerSeries.coeff_X,other]
  · simp

include H in
theorem original (q:ℕ)(u:ℂ):
    (Rose.test Z.criterion).applyTo (fun x=>(trunc (q+2) (Select.Single (response Z M ν 0) x)).eval u)=
      (Rose.cT Z.criterion.cut G Z.criterion.image:ℂ)*u := by
  rw [show q+2=(q+1)+1 from rfl,WilsonPositionScaleLawThermometerSmeared.original Z M H ν,clock Z M H ν,initial]

end YM.Integration.WilsonPositionScaleLawThermometerOrigin
end
