import YM.Integration.WilsonGraphGraphPaperCorrelations
import YM.Integration.WilsonGraphPaperCorrelations

/-! The issued graph correlation on the previously chosen publication. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGraphIncumbentGraphPublication
open WilsonGraphPaperPublication
universe u

theorem atPeriods (g : _root_.YangMills.GaugeGroup) (hg : g.IsSimple) :
    WilsonGraphGraphPaperCorrelations.AtPeriods hg (construction.{u} g hg)
      (publicPick.{u} g hg) (perspective.{u} g hg) := by
  have selected := ((rowBefore.{u} g hg).choose_spec.2.2
    (fun _ => True) (fun _ _ _ => True.intro)).choose_spec
  have receipts : YM.Answer.ContinuumLimit.PreElectedPublication.Receipts hg
      (construction.{u} g hg) (publicPick.{u} g hg) := selected.2.2.2.1
  exact WilsonGraphGraphPaperCorrelations.atPeriods hg
    (construction.{u} g hg) (publicPick.{u} g hg) (perspective.{u} g hg)
    (WilsonGraphDirectPaperCorrelation.atPeriods hg (construction.{u} g hg)
      (publicPick.{u} g hg) (perspective.{u} g hg) (nominated.{u} g hg) receipts)

end YM.Integration.WilsonGraphIncumbentGraphPublication
end

