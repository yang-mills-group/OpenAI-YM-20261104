import YM.Integration.WilsonMovingStoredFactor

/-! The same original register pays any pre-filed prospect together with the canonical-menu wage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingCommonForecasts
open RG Push Push.PriceCompiler Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonLimitConstruction.FundedPredictionSupply
open WilsonMovingShadowPrices (Ask)
open WilsonMovingStoredFactor (OnMenu)

theorem together {G : Gauge} (ask : Ask) (slow : ℝ → ℝ) {P Q : Prediction G}
    (first : WilsonMovingCommonPrices.AllPrices ask slow (@P))
    (second : WilsonMovingCommonPrices.AllPrices ask slow (@OnMenu G (@Q))) :
    WilsonMovingCommonPrices.AllPrices ask slow (@OnMenu G (@Both G (@P) (@Q))) := by
  intro s cost targets E charts C v baton wanting earn
  obtain ⟨L, p⟩ := first s cost targets E charts C v baton wanting earn
  obtain ⟨L', q⟩ := second s cost targets E charts C v baton wanting earn
  refine ⟨L ⊔ L',?_⟩
  intro l hl earlier D w u Z post S θ record fee V pocket cap
  obtain ⟨U, hU, hp⟩ := p l (le_sup_left.trans hl) earlier D w u Z post S θ record fee V pocket cap
  obtain ⟨W, hW, hq⟩ := q l (le_sup_right.trans hl) earlier D w u Z post S θ record fee U pocket cap
  refine ⟨W,hU.trans hW,?_⟩
  intro W' hv bar wait priced B light A η reset exchange menu aux rider booth shelter works divides common
  exact ⟨hp W' (hW.trans hv) bar wait priced B light η reset exchange menu aux rider booth shelter works divides,
    hq W' hv bar wait priced B light η reset exchange menu aux rider booth shelter works divides common⟩

theorem plain {G : Gauge} (ask : Ask) (slow : ℝ → ℝ) :
    WilsonMovingCommonPrices.AllPrices ask slow (@OnMenu G (@Always G)) := by
  intro s price targets E charts C v baton wanting earn
  refine ⟨fun _ => 0,?_⟩
  intro l _ earlier D w u Z post S θ record fee V pocket cap
  exact ⟨V,DelayLe.refl _,by intros; exact fun _ => True.intro⟩

end YM.Integration.WilsonMovingCommonForecasts
end
