import YM.Integration.WilsonMovingMentorOffer

/-! The original Tour reads only the reported phase of the Clockwork menu.
This phase is determined on the physical campaign before raising its delay. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorPhase
open RG Push PhysicalNext Repeat Roof
open WilsonLimitConstruction.FundedCompanySelection WilsonMovingStoredFactor

def Canonical {G : Gauge} : Prediction G := fun {_} {_} {_} F =>
  wind F.menu = fun _ _ => SectorMeasure.Chi.canonical

theorem actual {G : Gauge} {M : Org.Metals G} {D : RG.Supply.Rolls M.p} {A : Org.Alloy M D}
    (F : Roost.Factor A) (menu : AtMenu F) : Canonical F := by
  funext j i
  exact menu j i

/-- Its posted input is the original phase of all menus that qualify for the physical course. -/
theorem earned {G : Gauge} (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ) :
    WilsonMovingMentorOwnership.AllPrices ask slow (@OnMenu G (@Canonical G)) := by
  intro s fees R E charts C v baton want wage
  refine ⟨fun _ => 0,?_⟩
  intro l hl early D w u Z φ S θ p P V pocket cap
  refine ⟨V,⟨le_rfl,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro V' hv b I hp B light A η q E' X J K' f shelter works divides owner menu
  exact actual _ menu

end YM.Integration.WilsonMovingMentorPhase
end
