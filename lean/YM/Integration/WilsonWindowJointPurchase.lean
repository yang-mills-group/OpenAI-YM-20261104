import YM.Integration.WilsonFundedWindowMenu

/-! Two original marked invoices can be paid on one literal selected factor.
Choose the larger block lengths. Offer the first delay as the starting delay
for the second contract; both suppliers accept the eventual physical report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWindowJointPurchase

open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open ThroughLaunch WilsonLimitConstruction.FundedCompanySelection WilsonFundedWindowMenu
open scoped Classical

variable {G : Gauge}

def Together (p q : Prediction G) : Prediction G := fun {_} {_} {_} F => p F ∧ q F

theorem joint {p q : Prediction G} {s : Sheet G} {price : MapPrices}
    (first : Prepared (@p) s price) (second : Prepared (@q) s price) :
    Prepared (Together (@p) (@q)) s price := by
  intro R E flags C z bt
  obtain ⟨n₁,L⟩ := first R E flags C z bt
  obtain ⟨n₂,K⟩ := second R E flags C z bt
  refine ⟨n₁ ⊔ n₂,?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu V quarter
  obtain ⟨V₁,h₁,p₁⟩ := L l (le_sup_left.trans hl) D w u Z post scouts pocket θ stages P menu V quarter
  obtain ⟨V₂,h₂,p₂⟩ := K l (le_sup_right.trans hl) D w u Z post scouts pocket θ stages P menu V₁ quarter
  refine ⟨V₂,h₁.trans h₂,?_⟩
  intro W hW bar wait hp B archive origins rank
  dsimp only
  intro η rate exchange aux r booth sheltered works divides
  exact ⟨p₁ W (h₂.trans hW) bar wait hp B archive origins rank η rate exchange aux r booth sheltered works divides,
    p₂ W hW bar wait hp B archive origins rank η rate exchange aux r booth sheltered works divides⟩

end YM.Integration.WilsonWindowJointPurchase
end

