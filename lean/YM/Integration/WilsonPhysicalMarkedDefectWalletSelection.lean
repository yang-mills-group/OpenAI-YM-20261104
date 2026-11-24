import YM.Integration.WilsonPhysicalMarkedDefectSelectedHistory
import YM.Integration.WilsonPhysicalHistoryWalletPurchase
import YM.Integration.WilsonPhysicalHistoryUpperAngular

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.SingletonRent
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

theorem on_voice (simple:G.Simple) (hε:0<ε) (u:G.ColorIndex) (U:ℕ→ℕ) (V:Voice G) (clear:Clear G V)
    (C:VowsR.LawScroll G φ) (split:MintClock.splits≤φ)
    (external:∀ (s:Sheet G) (M:MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (extra:Prediction G) (credit:WilsonFundedWindowMenu.AllPrices (@extra)) :
    ∃ (R:Run G) (T:Campaign R) (W:Campaign.Pillars R T),
      Selection.{u} simple u U C (@extra) V clear R T W ε := by
  let combined := MintClock.both G φ C (law G φ)
  have both (s:Sheet G) (M:MapPrices) : Permitted combined s (ThroughLaunch.raging s M) :=
    WilsonWindowVacuumLaws.both (external s M) (permitted φ s _)
  obtain ⟨R,T,W,⟨request,subsidy⟩,inv,tails,⟨B,F,school⟩,pace,archive,canonical,
    posterior,masks,rooted,prescribed,corr,books,original,citizen,logs⟩ :=
    WilsonSelectedMarkedHistory.select.{u} simple hε u V clear combined split both U
      (Together (@extra) (@WilsonReportColumnSubsidy.Eligible G))
      (fun s M => WilsonWindowJointPurchase.joint (credit s M) (WilsonReportColumnSubsidy.allPrices s M))
  have elected : Paid R.rolls (roots simple R.metals.p R.metals.K) φ R.alloy.delay :=
    school.licence.employed.obligation.2
  have held : VowsR.Chamber C R.kit (roots simple R.metals.p R.metals.K) (rollTab simple R.metals R.rolls) B :=
    { school.licence.employed with obligation := school.licence.employed.obligation.1 }
  have house : Treehouse.VariableHouse R (roots simple R.metals.p R.metals.K) (rollTab simple R.metals R.rolls)
      C B R.family.path.levels.clock.kernel.penalty F (stages R.metals.p) :=
    { school with licence := { school.licence with employed := held } }
  exact ⟨R,T,W,request,subsidy,inv,tails,⟨B,F,house⟩,elected,
    subpower φ R simple _ elected,pace,archive,canonical,posterior,masks,rooted,prescribed,corr,books,
    original,citizen,logs⟩

/-- The voice and its clearance are fixed before the physical run. The same
selection satisfies the true wallet axial gates, original angular threshold
and all obligations already paid by Selection. -/
theorem with_wallet (simple:G.Simple) (hε:0<ε) (u:G.ColorIndex) (U:ℕ→ℕ)
    (C:VowsR.LawScroll G φ) (split:MintClock.splits≤φ)
    (external:∀ (s:Sheet G) (M:MapPrices), Permitted C s (ThroughLaunch.raging s M))
    (extra:∀ V:Voice G,Clear G V→Prediction G)
    (credit:∀ V clear, WilsonFundedWindowMenu.AllPrices (@extra V clear)) :
    ∃ (V:Voice G) (clear:Clear G V) (R:Run G) (T:Campaign R) (W:Campaign.Pillars R T),
      Selection.{u} simple u U C (@extra V clear) V clear R T W ε ∧
      WilsonPhysicalHistoryWalletPurchase.dues V clear simple R.kit ∧
      WilsonPhysicalHistoryUpperAngular.angular G R.kit := by
  obtain ⟨V,clear⟩ := MSbar.Heath.vocals G
  let ask : Prediction G := Together (@extra V clear) (Together (@WilsonPhysicalHistoryWalletPurchase.dues G V clear simple)
    (@WilsonPhysicalHistoryUpperAngular.angular G))
  have finance : WilsonFundedWindowMenu.AllPrices (@ask) := fun s M=>
    WilsonWindowJointPurchase.joint (credit V clear s M) (WilsonWindowJointPurchase.joint
      (WilsonPhysicalHistoryWalletPurchase.prepaid V clear simple s (ThroughLaunch.raging s M))
      (WilsonPhysicalHistoryUpperAngular.prepaid G s M))
  obtain ⟨R,T,W,h⟩ := on_voice.{u} simple hε u U V clear C split external (@ask) finance
  exact ⟨V,clear,R,T,W,{h with requested:=h.requested.1},h.requested.2.1,h.requested.2.2⟩

/-- Concrete complete single run, including the actual retained course, all
positive physical fields and wallet gates, with no prior selected R. -/
theorem physical_wallet (simple:G.Simple) (hε:0<ε) (u:G.ColorIndex) (U:ℕ→ℕ) :
    ∃ (V:Voice G) (clear:Clear G V) (R:Run G) (T:Campaign R) (W:Campaign.Pillars R T),
      Selection.{u} simple u U (VowsR.probe G MintClock.splits) (@WilsonReportColumnSubsidy.Eligible G)
        V clear R T W ε ∧ WilsonPhysicalHistoryWalletPurchase.dues V clear simple R.kit ∧
      WilsonPhysicalHistoryUpperAngular.angular G R.kit := by
  apply with_wallet.{u} simple hε u U _ le_rfl _ (fun _ _=>@WilsonReportColumnSubsidy.Eligible G)
    (fun _ _=>WilsonReportColumnSubsidy.allPrices)
  intro s price R C E flags
  exact ⟨0,fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ V=>⟨V,Push.PriceCompiler.DelayLe.refl _,fun _ _=>trivial⟩⟩

end YM.Integration.WilsonPhysicalMarkedDefect.SingletonRent
