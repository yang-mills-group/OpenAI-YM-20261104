import YM.Integration.WilsonPhysicalNodalCollar

/-! An independently issued dated sheet at the younger flat terminal
retains all its occupied coefficients on the original prior. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalNodalTerminal
open Function Filter Finset Lattice Wilson RG Marker PhysicalNext.Repeat.Legato
open WilsonMovingForkPrintedFile (Program row parent allSlots)
open WilsonMovingForkDepositedPrint (polynomial board)
open WilsonMovingForkTerminalFile (programme Source)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open Pert.Asymptotics
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N per v K n:ℕ}{d:Fin n → ℕ}

theorem original (issued:Source R d v K)(vk:v < K)(kn:K ≤ N)
    (w:∀a,R.family.label (d a))(pins:Fin n → Site (R.family.side K per)):
    let H:=issued N per kn w pins v le_rfl vk
    let M:=row (programme issued) N per w pins
    reading R (N:=N) (numerator R N per v (M v)) v le_rfl=
      (polynomial H (regulatorRun R.family N per v)).part (allSlots n):=by
  intro H M
  have life:=WilsonThermometerUnitFilingFlatRead.original R (vk.le.trans kn)
    (R.family.path.rep N per v) rfl (M v)
  refine life.trans ?_
  have named:programme issued N per w pins v vk=board H:=dif_pos ⟨kn,le_rfl⟩
  simp only [M,row,dif_pos vk]
  rw [named,WilsonMovingForkDepositedPrint.flat]

end YM.Integration.WilsonPhysicalNodalTerminal
end
