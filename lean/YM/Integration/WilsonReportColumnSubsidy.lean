import YM.Integration.WilsonFundedWindowMenu
import YM.OPE.Loom.ExtraDelays

/-! Buy the column improvement on the same delay on which the original
physical school and its reporting cutoff are chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportColumnSubsidy

open RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonLimitConstruction.FundedCompanySelection

variable {G : Gauge}

def Eligible : Prediction G := fun {_} {_} {A} _ => Subsidize A.B.a

theorem prepaid (s : Sheet G) (price : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@Eligible G) s price := by
  intro C E flags programs wages baton
  refine ⟨0, ?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu V quarter
  obtain ⟨W, hVW, grant⟩ := subsidize_feasible (G := G) V
  refine ⟨W, hVW, ?_⟩
  intro Y hY bar wait priced B archive origins rank
  dsimp only
  intro η q exchange aux rider booth sheltered works divides
  exact grant Y hY wait B.a B.valid

theorem allPrices : WilsonFundedWindowMenu.AllPrices (@Eligible G) :=
  fun s T => prepaid s (ThroughLaunch.raging s T)

end YM.Integration.WilsonReportColumnSubsidy
end

