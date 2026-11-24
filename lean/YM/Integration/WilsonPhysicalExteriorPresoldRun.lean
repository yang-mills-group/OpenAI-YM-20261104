import YM.Integration.WilsonPhysicalExteriorIssuedWord
import YM.Integration.WilsonWindowReportingRun
import YM.Integration.WilsonWindowFormalAnnouncement

/-! One physical run for the preannounced formal graph order, returned
field detector windows, original physical reports and the independent
historical Wilson--MS prescription. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorPresoldRun
open RG RG.Supply Lattice Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonWindowJointPurchase
open MS MS.Land FVA2 Register FVAAlt2 Lobby RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open FormalBulk08
universe u

def Books {G:Gauge} (hG:G.Simple) (R:Run G) : Prop :=
  ∀(N:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(dial:Bool),
  ∃ S:Prescription (Press.portDeck G),Main.Match N hG M S dial ∧
    ∃(Z:∀ b:Patch,b.Branches R.family.path.levels.clock.kernel G)
      (ledger:Lodge.Contract R (Oracle.books R.family.path.levels.clock.kernel) Z) (Q:Prescription (Press.portDeck G)),
      Q.team=S.team ∧ TaylorOKPl M (Lobby.Table (basisR R) (Press.portDeck G)) Q ∧
      WilsonPhysicalExteriorFundedPeriod.Periods R Z ledger Q ∧
      WilsonPhysicalExteriorFirstCutPrice.Rows R M Q ∧ WilsonPhysicalExteriorIssuedWord.Windows R M Q

theorem original {G:Gauge} (hG:G.Simple) {ε:ℝ} (hε:0<ε) (U:ℕ→ℕ)
    (p:Prediction G) (paid:WilsonFundedWindowMenu.AllPrices (@p)) :
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T), p R.kit ∧
      WilsonWindowTicketPurchase.Issued hG R.kit ∧ WilsonWindowReportingPace.Slow R.kit ∧
      WilsonWindowOriginalRun.ArchivedInputs R.kit ∧ NativeFVAPlateau.Correlations R ∧
      FundedOriginalProperties.{u} hG ε W ∧
      WilsonWindowFormalPurchase.Canonical U R.kit ∧ Primer.Announced R.family U ∧ Books hG R := by
  obtain ⟨R,T,W,⟨hp,hf⟩,ticket,pace,archive,corr,original⟩:=
    WilsonWindowReportingRun.select.{u} hG hε (Together (@p) (@WilsonWindowFormalPurchase.Canonical G U))
      (fun s price=>joint (paid s price) (WilsonWindowFormalPurchase.prepaid U s _))
  exact ⟨R,T,W,hp,ticket,pace,archive,corr,original,hf,WilsonWindowFormalAnnouncement.on_run R hf,
    fun N M dial=>WilsonPhysicalExteriorIssuedWord.funded R hG N M dial corr⟩

end YM.Integration.WilsonPhysicalExteriorPresoldRun
end
