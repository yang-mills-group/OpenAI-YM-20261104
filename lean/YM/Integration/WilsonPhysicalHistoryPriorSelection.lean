import YM.Integration.WilsonPhysicalMarkedDefectWalletSelection
import YM.Integration.WilsonPhysicalHistoryPriorAperture

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryPriorSelection
open Function Filter Finset Lattice Wilson RG RG.Shoot RG.Supply Pressure Input Org Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Push.PriceCompiler
open PhysicalNext.Repeat.Daisy.Charity.RG12
open ThroughLaunch AllOrder AllOrder.Transit AllOrder.Transit.WheelP
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open MSbar MSbar.Heath FVA1Physical.Wilson FVA1Physical.Round2.Curvature
open WilsonConditionalTaylorLabels WilsonWindowRootPurchase WilsonWindowJointPurchase
open WilsonWindowBookPurchase WilsonWindowUniversalSchool
open scoped Classical

universe u
variable {G:Gauge} {φ:ℕ→ℕ} {ε:ℝ}

theorem permitted (φ:ℕ→ℕ) (s : Sheet G) (price : MapPrices) :
    WilsonWindowBookPurchase.Permitted (WilsonPhysicalHistoryPriorAperture.law G φ) s price := by
  intro Q C E he
  refine ⟨fun _=>0,?_⟩
  intro ℓ _ D w u Z post scouts h P θ tab B hB W
  exact WilsonPhysicalHistoryPriorAperture.priced (M:=WilsonWindowBookPurchase.raised s price ℓ) D Q φ W

theorem selected (simple:G.Simple) (hε:0<ε) (u:G.ColorIndex) (U:ℕ→ℕ)
    (C:VowsR.LawScroll G φ) (split:MintClock.splits≤φ)
    (external:∀ (s:Sheet G) (M:MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (extra:∀ V:Voice G,Clear G V→Prediction G)
    (credit:∀ V clear, WilsonFundedWindowMenu.AllPrices (@extra V clear)) :
    ∃ (V:Voice G) (clear:Clear G V) (R:Run G) (T:Campaign R) (W:Campaign.Pillars R T),
      WilsonPhysicalMarkedDefect.SingletonRent.Selection.{u} simple u U C (@extra V clear) V clear R T W ε ∧
      WilsonPhysicalHistoryWalletPurchase.dues V clear simple R.kit ∧
      WilsonPhysicalHistoryUpperAngular.angular G R.kit ∧
      WilsonPhysicalHistoryPriorAperture.Paid R.rolls (roots simple R.metals.p R.metals.K) φ R.alloy.delay := by
  let combined:=MintClock.both G φ C (WilsonPhysicalHistoryPriorAperture.law G φ)
  have both (s:Sheet G) (M:MapPrices) : Permitted combined s (ThroughLaunch.raging s M):=
    WilsonWindowVacuumLaws.both (external s M) (permitted φ s _)
  obtain ⟨V,clear,R,T,W,H,wallet,angle⟩:=WilsonPhysicalMarkedDefect.SingletonRent.with_wallet.{u}
    simple hε u U combined split both extra credit
  obtain ⟨B,F,school⟩:=H.housed
  have elected:WilsonPhysicalHistoryPriorAperture.Paid R.rolls (roots simple R.metals.p R.metals.K) φ R.alloy.delay:=
    school.licence.employed.obligation.2
  have held:VowsR.Chamber C R.kit (roots simple R.metals.p R.metals.K) (rollTab simple R.metals R.rolls) B:=
    {school.licence.employed with obligation:=school.licence.employed.obligation.1}
  have house:Treehouse.VariableHouse R (roots simple R.metals.p R.metals.K) (rollTab simple R.metals R.rolls)
      C B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p):=
    {school with licence:={school.licence with employed:=held}}
  exact ⟨V,clear,R,T,W,{H with housed:=⟨B,F,house⟩},wallet,angle,elected⟩

end YM.Integration.WilsonPhysicalHistoryPriorSelection
