import YM.Integration.WilsonFundedWindowMenu
import YM.Gaps1020.Local.Invoice
import YM.Gaps1020.Local.MarkedRevenue
import YM.RG12.Burst.Cotton

/-! The two original marked-action grants are purchased prior to the
single physical selection and retain its actual register and beta delay. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOldActionForecast
open RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12 GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLimitConstruction.FundedCompanySelection
variable {G : Gauge}

def Eligible : Prediction G := fun {_} {_} {A} F =>
  Mallow.RG12.Earned ((markerBudget G).paired (checkout G)) F.shape A.delay

theorem prepaid (s : Sheet G) (price : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@Eligible G) s price := by
  intro targets e flags programs wages baton
  let Δ := (markerBudget G).paired (checkout G)
  obtain ⟨n,paid⟩ := Mallow.RG12.lint Δ targets e
  refine ⟨n,?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu V quarter
  have first : Mallow.RG12.First Δ (ThroughLaunch.raise s l) _ _ _ n := paid
  obtain ⟨W,hVW,grant⟩ := Mallow.RG12.board Δ Z first
    (fun j=>(hl j).trans (D.large j).need) (fun i j _=>(flags i j).2.2.2.1.le) V
  refine ⟨W,hVW,?_⟩
  intro Y late K wait priced B archive origins rank
  dsimp only
  intro η q exchange aux rider booth sheltered works divides
  exact grant Y late

theorem allPrices : WilsonFundedWindowMenu.AllPrices (@Eligible G) :=
  fun s price=>prepaid s (ThroughLaunch.raging s price)

theorem issued (R : Run G) (paid : Eligible R.kit) :
    Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay ∧
      Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay :=
  ⟨fun j x hx i hi=>(paid j x hx i hi).1, fun j x hx i hi=>(paid j x hx i hi).2⟩

end YM.Integration.WilsonOldActionForecast
end
