import YM.Integration.WilsonMovingMentorHeader
import YM.QuadraticLocal.Startup.Warm

/-! The original starting hard budget on the same physical salary and delay. -/
noncomputable section
namespace YM.Integration.WilsonMovingMentorWarm
open RG Push PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.Foundations Org RG.Supply Push.PriceCompiler ThroughLaunch
open WilsonLimitConstruction.FundedCompanySelection WilsonMovingStoredFactor

open AllOrder.Transit.WheelP
def Held {G : Gauge} : Prediction G := fun {M} {_} {A} _ => QuadraticLocal.Spes.Market.Warm (s:=M.p) A.delay

theorem paid {G : Gauge} (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ) :
    WilsonMovingMentorOwnership.AllPrices ask slow (@OnMenu G (@Held G)) := by
  intro s T rows E charts C v baton wanting wage
  refine ⟨0,?_⟩
  intro l hl earlier D w fees Z φ S θ p P V pocket cap
  let M : Metals G := ⟨raise s l,raging s T,chart G,chart_ok G⟩
  obtain ⟨W,hw,available⟩ := QuadraticLocal.Spes.Market.accrue (s:=M.p) V
  refine ⟨W,hw,?_⟩
  intro W' hW b I hp B light A η z E' X J K' f shelter works divides owner menu
  exact available _ hW

/-- Both starting hard appointments apply to this single physical delay. -/
def Conditions {G : Gauge} : Prediction G :=
  @WilsonLimitConstruction.FundedPredictionSupply.Both G (@WilsonMovingMentorHeader.Conditions G) (@Held G)

theorem issued {G : Gauge} (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ) :
    WilsonMovingMentorOwnership.AllPrices ask slow (@OnMenu G (@Conditions G)) :=
  WilsonMovingMentorUnion.together ask slow (WilsonMovingMentorHeader.issued ask slow) (paid ask slow)

end YM.Integration.WilsonMovingMentorWarm
end
