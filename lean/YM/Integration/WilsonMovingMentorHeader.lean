import YM.AllOrder.Transit.Crown
import YM.Integration.WilsonMovingMentorUnion
import YM.Integration.WilsonMovingMentorFrost

/-! The physical course entry and its analytic estimates are purchased at the
actual original delay, before any period or cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorHeader
open RG Push PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.Foundations Org RG.Supply Push.PriceCompiler ThroughLaunch
open WilsonLimitConstruction.FundedCompanySelection WilsonMovingStoredFactor

open AllOrder.Transit.WheelP
def Held {G : Gauge} : Prediction G := fun {M} {_} {A} _ => Header (X:=M) A.delay

theorem paid {G : Gauge} (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ) :
    WilsonMovingMentorOwnership.AllPrices ask slow (@OnMenu G (@Held G)) := by
  intro s T rows E charts C v baton wanting wage
  refine ⟨0,?_⟩
  intro l hl earlier D w fees Z φ S θ p P V pocket cap
  let M : Metals G := ⟨raise s l,raging s T,chart G,chart_ok G⟩
  obtain ⟨W,hw,available⟩ := demands (X:=M) V
  refine ⟨W,hw,?_⟩
  intro W' hW b I hp B light A η z E' X J K' f shelter works divides owner menu
  exact available _ hW

def Conditions {G : Gauge} : Prediction G :=
  @WilsonLimitConstruction.FundedPredictionSupply.Both G (@Held G) (@WilsonMovingMentorFrost.Held G)

theorem issued {G : Gauge} (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ) :
    WilsonMovingMentorOwnership.AllPrices ask slow (@OnMenu G (@Conditions G)) :=
  WilsonMovingMentorUnion.together ask slow (paid (G:=G) ask slow) (WilsonMovingMentorFrost.paid ask slow)

theorem at_date {G : Gauge} (R : Run G) (bought : Conditions R.kit) (m k : ℕ)
    (admitted : k ≤ R.alloy.B.a.clock.J m) :
    AllOrder.Quay.BandTar G (R.metals.p.profile (R.alloy.B.a.clock.J m)) k
      (R.alloy.B.a.clock.hatBeta m) ∧
    QuadraticLocal.Beaming.Celebrates R.kit.shape R.kit.book R.kit.scout
      (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m) (R.alloy.B.a.clock.hatBeta m) :=
  ⟨bought.1 _ _ k admitted (step_paid R.alloy.B.a m) _ (R.alloy.B.valid.pays m),
   WilsonMovingMentorFrost.actual R bought.2 m⟩

end YM.Integration.WilsonMovingMentorHeader
end
