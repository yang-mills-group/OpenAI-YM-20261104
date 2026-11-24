import YM.Integration.WilsonMovingCommonForecasts

/-! Two specifications submitted for the same original root enter the common
block-length and delay register before the physical factor is issued. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorStagePair
open Precision RG RG.Supply Push Push.PriceCompiler Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonLimitConstruction.FundedPredictionSupply

theorem paid {G : Gauge} {ask : WilsonMovingShadowPrices.Ask} {slow : ℝ → ℝ}
    {s : Sheet G} {price : MapPrices} {P Q : Prediction G}
    (left : WilsonMovingCommonPrices.Prepaid ask slow (@P) s price)
    (right : WilsonMovingCommonPrices.Prepaid ask slow (@Q) s price) :
    WilsonMovingCommonPrices.Prepaid ask slow (@Both G (@P) (@Q)) s price := by
  intro targets E charts C v baton wanting earn
  obtain ⟨l,h⟩ := left targets E charts C v baton wanting earn
  obtain ⟨u,k⟩ := right targets E charts C v baton wanting earn
  refine ⟨l ⊔ u,?_⟩
  intro t ht earlier D w U Z φ S θ p P V pocket cap
  obtain ⟨first,second⟩ := sup_le_iff.mp ht
  obtain ⟨W,hw,receipt⟩ := h t first earlier D w U Z φ S θ p P V pocket cap
  obtain ⟨Y,hy,bill⟩ := k t second earlier D w U Z φ S θ p P W pocket cap
  refine ⟨Y,hw.trans hy,?_⟩
  intro W' hv K I stock B light A η z E' X J K' b shelter works divides
  exact ⟨receipt W' (hy.trans hv) K I stock B light η z E' X J K' b shelter works divides,
    bill W' hv K I stock B light η z E' X J K' b shelter works divides⟩

end YM.Integration.WilsonMovingMentorStagePair
end
