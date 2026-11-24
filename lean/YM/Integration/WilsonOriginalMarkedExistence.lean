import YM.Integration.WilsonLimitConstruction.FundedOriginalRun
import YM.Integration.WilsonOldActionForecast
import YM.Integration.OriginalMarkedGibbsRate

/-! Purchase the original marked grants on the run that realizes the funded
campaign and its moving correlations. All charged estimates use that run's clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMarkedExistence

open Filter RG RG.Supply Precision Org Push.PriceCompiler Lattice
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12 GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection

universe u
variable {G : Gauge}

/-- The original expense identity pays the joint marker and checkout forecast. -/
theorem prepaid (s : Sheet G) (price : MapPrices) :
    Prepaid (@WilsonOldActionForecast.Eligible G) s price := by
  intro targets expenses _ _ _ _ wanting
  let Δ := (markerBudget G).paired (checkout G)
  obtain ⟨n, paid⟩ := Mallow.RG12.lint Δ targets expenses
  refine ⟨n, ?_⟩
  intro l hl D w u Z post scouts θ stages P V quarter
  have first : Mallow.RG12.First Δ (ThroughLaunch.raise s l) _ _ _ n := paid
  obtain ⟨W, hVW, grant⟩ := Mallow.RG12.board Δ Z first
    (fun j => (hl j).trans (D.large j).need) (fun j i _ => (wanting j i).le) V
  refine ⟨W, hVW, ?_⟩
  intro Y late K wait priced directed
  dsimp only
  intros
  exact grant Y late

/-- The full-support fee bound with an arbitrary prefactor on the original clock. -/
def Charged (R : Run G) : Prop :=
  ∀ (q : ℕ) (v : ℝ), 0 < v →
    ∀ᶠ m : ℕ in atTop, ∀ N p, m < N → ∀ S : Support (R.family.side m p),
      let g := Pert.Asymptotics.regulatorRun R.family N p (m+1)
      2 * Real.exp 2 * OriginalMarkedLocalPurchase.fee R.alloy.B.a m S ((Real.sqrt 2*g)^(q+2)) ≤
        v * S.card * g^(q+1)

/-- Co-purchase any original input prediction before selecting the physical factor. -/
theorem selectedWith (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (prediction : Prediction G) (price : FundedPredictionSupply.AllPrices (@prediction)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      prediction R.kit ∧
      Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay ∧
      Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧ Charged R := by
  obtain ⟨R, T, W, predicted, correlations, original⟩ :=
    fundedOriginalRun_with_prediction.{u} hG hε
      (@FundedPredictionSupply.Both G (@prediction) (@WilsonOldActionForecast.Eligible G))
      (fun s t => FundedPredictionSupply.both (price s t) (prepaid s (ThroughLaunch.raging s t)))
  obtain ⟨marker, checkout⟩ := WilsonOldActionForecast.issued R predicted.2
  exact ⟨R, T, W, predicted.1, marker, checkout, correlations, original,
    OriginalMarkedGibbsRate.charged R hG⟩

/-- The original funded campaign, moving correlations and both marked grants on one run. -/
theorem original (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay ∧
      Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧ Charged R := by
  obtain ⟨R, T, W, _, marker, checkout, correlations, funded, charged⟩ :=
    selectedWith.{u} hG hε (@FundedPredictionSupply.Always G)
      (fun s t => FundedPredictionSupply.always s (ThroughLaunch.raging s t))
  exact ⟨R, T, W, marker, checkout, correlations, funded, charged⟩

end YM.Integration.WilsonOriginalMarkedExistence
end
