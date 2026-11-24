import YM.Integration.WilsonWindowBookPurchase
import YM.QuadraticLocal.Cycle.Bank
import YM.QuadraticLocal.Fk.Volume
import YM.QuadraticLocal.Rebirth.Loan
import YM.QuadraticLocal.Rebirth.Price
import YM.QuadraticLocal.Rebirth.CostB

/-! Pay the manuscript's vacuum and volume laws on the rods and books of the actual
price schedule. The estimates called here were proved for arbitrary physical metals. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWindowVacuumLaws

open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open ThroughLaunch Pressure QuadraticLocal QuadraticLocal.Mentor
open WilsonWindowBookPurchase
open scoped Classical

variable {G : Gauge} {ψ : ℕ → ℕ} {s : Sheet G} {price : MapPrices}

/-- Both laws use one roll, tab, sales receipt and final delay. -/
theorem both {b c : VowsR.LawScroll G ψ} (hb : Permitted b s price) (hc : Permitted c s price) :
    Permitted (MintClock.both G ψ b c) s price := by
  intro R C E flags
  obtain ⟨m,hm⟩ := hb R C E flags
  obtain ⟨n,hn⟩ := hc R C E flags
  refine ⟨m ⊔ n,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  obtain ⟨V₁,h₁,p₁⟩ := hm l (le_sup_left.trans hl) D w q Z post scouts pocket P θ tab book sold V
  obtain ⟨V₂,h₂,p₂⟩ := hn l (le_sup_right.trans hl) D w q Z post scouts pocket P θ tab book sold V₁
  exact ⟨V₂,h₁.trans h₂,fun W hW => ⟨p₁ W (h₂.trans hW),p₂ W hW⟩⟩

theorem volume : Permitted (Volume.wind G ψ) s price := by
  intro R C E flags
  refine ⟨0,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  exact Volume.bankroll (X := raised s price l) R D tab ψ book V

theorem genesis : Permitted (Rebirth.Scholar.genesis G ψ) s price := by
  intro R C E flags
  refine ⟨0,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  exact Rebirth.Scholar.season (X := raised s price l) D R tab V

theorem readyYear : Permitted (Rebirth.Scholar.Vacuum.readyYear G ψ) s price := by
  intro R C E flags
  refine ⟨0,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  exact Rebirth.Scholar.Vacuum.seasons (X := raised s price l) D R tab V

theorem training : Permitted (Rebirth.Scholar.Vacuum.training G ψ) s price := by
  intro R C E flags
  refine ⟨0,?_⟩
  intro l hl D w q Z post scouts pocket P θ tab book sold V
  exact Rebirth.Scholar.Vacuum.smaller (X := raised s price l) D R V

end YM.Integration.WilsonWindowVacuumLaws
end

