import YM.Integration.WilsonWindowRootPurchase
import YM.Integration.WilsonFundedWindowMenu
import YM.Integration.WilsonMovingMentorRootRadius
import YM.QuadraticLocal.Cycle.Funding

/-! Fund the root radius and the hiring threshold on the very same roots and rolls as the existence proof. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseOriginalTuition

open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonWindowRootPurchase QuadraticLocal QuadraticLocal.Mentor
open ThroughLaunch Next.Foundations Push.PriceCompiler
open WilsonLimitConstruction.FundedCompanySelection

variable {G : Gauge}


/-- Both inverse-source charges refer to the roots already used by the original marked school. -/
def Funds (hG:G.Simple) (φ:ℕ→ℕ) : Prediction G := fun {M} {D} {A} _ =>
  WilsonMovingMentorRootRadius.Income (M:=M) (roots hG M.p M.K) φ A.delay ∧
    ∀ j,MintClock.Employment (roots hG M.p M.K) φ j (D.L j)

theorem prepaid (hG:G.Simple) (φ:ℕ→ℕ) (shorter:MintClock.splits≤φ) :
    WilsonFundedWindowMenu.AllPrices (@Funds G hG φ) := by
  intro s T C E flags programs wages baton
  let price:=ThroughLaunch.raging s T
  obtain ⟨floor,staff⟩:=MintClock.opens (roots hG s price) φ shorter
  refine ⟨floor,?_⟩
  intro l growth D w U Z post scouts pocket θ stages cost menu V quarter
  let M:Metals G:=⟨ThroughLaunch.raise s l,price,chart G,chart_ok G⟩
  obtain ⟨W,next,paid⟩:=WilsonMovingMentorRootRadius.accrued (M:=M) (roots hG M.p M.K) φ V
  refine ⟨W,next,?_⟩
  intro Y later bar wait priced B archive origins rank
  dsimp only
  intro η q exchange aux rider booth sheltered works divides
  exact ⟨paid Y later,fun j=>staff j (D.L j) ((growth j).trans (D.large j).need)⟩

end YM.Integration.WilsonReceivedCloseOriginalTuition
