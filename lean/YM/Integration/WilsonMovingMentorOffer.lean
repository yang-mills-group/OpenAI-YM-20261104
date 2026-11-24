import YM.Integration.WilsonMovingMentorOwnership
import YM.Integration.WilsonMovingStoredFactor

/-! The same original register pays any pre-filed prospect together with the canonical-menu wage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorOffer
open RG Push Push.PriceCompiler Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonLimitConstruction.FundedPredictionSupply
open WilsonMovingShadowPrices (Ask)
open WilsonMovingStoredFactor (OnMenu)

theorem together {G : Gauge} (ask : Ask) (slow : ℝ → ℝ) {P Q : Prediction G}
    (first : WilsonMovingCommonPrices.AllPrices ask slow (@P))
    (second : WilsonMovingMentorOwnership.AllPrices ask slow (@OnMenu G (@Q))) :
    WilsonMovingMentorOwnership.AllPrices ask slow (@OnMenu G (@Both G (@P) (@Q))) := by
  intro s cost targets E charts C v baton wanting earn
  obtain ⟨L, p⟩ := first s cost targets E charts C v baton wanting earn
  obtain ⟨L', q⟩ := second s cost targets E charts C v baton wanting earn
  refine ⟨L ⊔ L',?_⟩
  intro l hl earlier D w u Z post S θ record fee V pocket cap
  obtain ⟨U, hU, hp⟩ := p l (le_sup_left.trans hl) earlier D w u Z post S θ record fee V pocket cap
  obtain ⟨W, hW, hq⟩ := q l (le_sup_right.trans hl) earlier D w u Z post S θ record fee U pocket cap
  refine ⟨W,hU.trans hW,?_⟩
  intro W' hv bar wait priced B light A η reset exchange menu aux rider booth shelter works divides owner common
  exact ⟨hp W' (hW.trans hv) bar wait priced B light η reset exchange menu aux rider booth shelter works divides,
    hq W' hv bar wait priced B light η reset exchange menu aux rider booth shelter works divides owner common⟩


/-- Put the two contracts released by the original directed construction beside an
earlier certified menu. There is only one physical Factor in this issue. -/
theorem retain {G : Gauge} (ask : Ask) (slow : ℝ → ℝ) {P : Prediction G}
    (posted : WilsonMovingCommonPrices.AllPrices ask slow (@OnMenu G (@P))) :
    WilsonMovingMentorOwnership.AllPrices ask slow
      (@OnMenu G (@Both G (@WilsonMovingMentorOwnership.Owned G) (@P))) := by
  intro s cost target E charts C v baton wanting earn
  obtain ⟨k, paid⟩ := posted s cost target E charts C v baton wanting earn
  refine ⟨k,?_⟩
  intro l hl earlier D w u Z φ S θ P' P₀ U pocket cap
  obtain ⟨V, hV, grant⟩ := paid l hl earlier D w u Z φ S θ P' P₀ U pocket cap
  refine ⟨V,hV,?_⟩
  intro V' hv b I hp B light _A η q E' X J M d hZ hY hm owned menu
  exact ⟨owned,grant V' hv b I hp B light η q E' X J M d hZ hY hm menu⟩

end YM.Integration.WilsonMovingMentorOffer
end
