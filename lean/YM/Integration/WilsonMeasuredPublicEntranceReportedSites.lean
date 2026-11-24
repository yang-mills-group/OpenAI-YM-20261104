import YM.Integration.WilsonMeasuredPublicEntrancePooledEar

/-! Transporting the elected lamps along the equality of their received roots. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceReportedSites
open Function Finset Lattice Wilson RG Marker QuadraticLocal
variable {G:Gauge}{n:Side}{T V I:Type}[DecidableEq V]{J:Census V}{p:BudgetPoint}
  {o c:V→Site n}(eqn:o=c)(E:Lamps T I G p o J)

def placed : Lamps T I G p c J:=eqn ▸ E

theorem log (t:T)(U:Config G n):(placed eqn E).log t U=E.log t U:=by
  cases eqn
  rfl

theorem wage (w:V→ℝ)(B:ℕ)(α fee:ℝ)(h:E.Paid w B α fee):
    (placed eqn E).Paid w B α fee:=by
  cases eqn
  exact h

end YM.Integration.WilsonMeasuredPublicEntranceReportedSites
end
