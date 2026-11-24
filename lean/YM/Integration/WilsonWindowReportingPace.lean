import YM.Integration.WilsonFundedWindowMenu
import YM.RG16.Provider.Slower

/-! The slow-block inequality used by the signed OPE receipt at the nearby
cut. It is bought after the actual block side is chosen and before the wait,
on the same directed levels as the funded continuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWindowReportingPace

open RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonLimitConstruction.FundedCompanySelection

variable {G : Gauge}

def Slow : Prediction G := fun {_} {_} {A} _ =>
  RG16.PlentyGate A.B.a ∧ ∀ m, ((A.B.a.S.block m).val : ℝ) ≤ Real.log (RG16.Lambda A.B.a m)

theorem prepaid (hG : G.Simple) (s : Sheet G) (price : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@Slow G) s price := by
  intro C E flags programs wages baton
  refine ⟨0,?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu V quarter
  obtain ⟨W,hVW,grant⟩ := RG16.later D hG V (fun _ => 0)
  refine ⟨W,hVW,?_⟩
  intro Y hY bar wait priced B archive origins rank
  dsimp only
  intro η q exchange aux rider booth sheltered works divides
  obtain ⟨plenty,pace⟩ := grant Y hY wait B.a B.valid
  exact ⟨plenty,fun m => (le_max_left _ _).trans (pace m)⟩

end YM.Integration.WilsonWindowReportingPace
end

