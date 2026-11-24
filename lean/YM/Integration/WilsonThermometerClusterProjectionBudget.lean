import YM.Integration.WilsonThermometerClusterProjectionFee
import YM.Integration.WilsonReportLampForecast
import YM.Integration.WilsonWindowJointPurchase
import YM.Push.PRICE_COMPILER.Scene

/-! The finite scalar-section factors in the original Wilson grouping tariff, purchased at the actual stage before choosing its cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerClusterProjectionBudget
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Tree Pressure
open Extra.Iteration PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ThroughLaunch Next.Foundations Push.PriceCompiler RG.Supply Input Next.Scheduling
open WilsonLimitConstruction.FundedCompanySelection WilsonReportRetainedAnchor
open Push.AbsoluteSums
open scoped Classical BigOperators Topology
variable {G:Gauge}

def charge (v:Stage):ℝ:=
  2*|Graces.host G v 0| * 4^(v.power*v.order)*|Reserves.polyPrice (1/2:ℝ) (v.power*v.order)|

def Ready (a:Levels G):Prop:=∀ᶠ k:ℕ in atTop,charge (G:=G) (a.params k)≤a.clock.hatBeta k

def Eligible : Prediction G:=fun {_} {_} {A} _=>Ready A.B.a

theorem prepaid (s:Sheet G) (price:MapPrices):WilsonFundedWindowMenu.Prepared (@Eligible G) s price:=by
  intro C E flags programs wages baton
  refine ⟨0,?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu V quarter
  let F (n:ℕ) (x:ℝ):Prop:=∀ i:Fin (n+1),charge (G:=G) (s.profile i)≤x
  have enough (n:ℕ):∀ᶠ x:ℝ in atTop,F n x:=eventually_all.mpr fun i=>eventually_ge_atTop _
  obtain ⟨W,hVW,_,grant⟩:=delay_extra V F (fun _ _ _=>True) enough (fun _ _=>by simp)
  refine ⟨W,hVW,?_⟩
  intro U hWU table wait priced B archive origins rank
  dsimp only
  intro η q exchange aux rider booth sheltered works divides
  apply Eventually.of_forall
  intro k
  rw [params_eq B.valid k]
  exact (grant U hWU).1 (B.a.clock.J (k+1)) (B.a.clock.hatBeta k) (B.valid.pays k)
    ⟨B.a.clock.J k,Nat.lt_succ_of_le (B.a.fits.mono (Nat.le_succ k))⟩

theorem allPrices : WilsonFundedWindowMenu.AllPrices (@Eligible G):=
  fun s price=>prepaid s (ThroughLaunch.raging s price)

end YM.Integration.WilsonThermometerClusterProjectionBudget
end
