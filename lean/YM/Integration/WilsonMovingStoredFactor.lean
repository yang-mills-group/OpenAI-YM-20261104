import YM.Integration.WilsonMovingCommonPrices
import YM.Integration.WilsonOriginalLightSelection

/-! The higher singleton quotation and the old prediction on the same actual factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingStoredFactor
open RG Push Push.PriceCompiler Pressure Precision PhysicalNext Repeat Legato
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonLimitConstruction.FundedPredictionSupply
open WilsonMovingShadowPrices (Ask)

def AtMenu {G : Gauge} : Prediction G := fun {_} {_} {_} F =>
  ∀ j i, (F.menu j i).q = Push.SectorMeasure.Chi.canonical

def OnMenu {G : Gauge} (P : Prediction G) : Prediction G := fun {_} {_} {_} F => AtMenu F → P F

theorem ordinary {G : Gauge} (ask : Ask) (slow : ℝ → ℝ) {other : Prediction G}
    (paid : FundedPredictionSupply.AllPrices (@other)) :
    WilsonMovingCommonPrices.AllPrices ask slow
      (@Both G (@WilsonMovingCommonPrices.Stored G ask)
        (@Both G (@WilsonOriginalLightSelection.Lit G slow) (@other))) := by
  intro s price targets E charts C v baton wanting wages
  obtain ⟨u,next⟩ := paid s price targets E charts C v baton wanting
  refine ⟨u,?_⟩
  intro l hl upper D w U Z φ S θ p P V pocket quarter
  obtain ⟨W,hw,book⟩ := next l hl D w U Z φ S θ p P V quarter
  refine ⟨W,hw,?_⟩
  intro W' h' b I hp B light A η q E' X J K' f shelter works divides
  exact ⟨⟨fun _ _ => rfl,wages,upper⟩,light,
    book W' h' b I hp B η q E' X J K' f shelter works divides⟩

end YM.Integration.WilsonMovingStoredFactor
end
