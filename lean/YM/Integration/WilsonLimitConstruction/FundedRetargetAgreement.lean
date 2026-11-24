import YM.FullVolume.Roll.Fiscal
import YM.UVExtension.Case.Wing

/-! The UV funding and native funded-Run constructors select their retargeted
map prices from equivalent predicates. This identifies the prices and their
whole provider for a fixed original sheet, preliminary quote and length floor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedRetargetAgreement

open RG RG.Supply Precision PhysicalNext

private theorem choose_eq {α : Type*} {p q : α → Prop}
    (hp : ∃ x, p x) (hq : ∃ x, q x) (h : ∀ x, p x ↔ q x) :
    hp.choose = hq.choose := by
  have he : p = q := funext fun x => propext (h x)
  subst q
  rfl

/-- The two predicates have the same witness set. Both horizon identities
are retained, including their distinct strict cutoff inequalities. -/
theorem prices {G : Gauge} (s : Sheet G) (T : MapPrices) :
    ThroughLaunch.raging s T = UVExtension.Case.actualPay s T := by
  unfold ThroughLaunch.raging UVExtension.Case.actualPay
  apply choose_eq
  intro K
  constructor <;> intro h a ha hc M hM <;>
    obtain ⟨H, hH, hOverlay, hu, hv⟩ := h a ha hc M hM <;>
    exact ⟨H, hH, hOverlay, hv, hu⟩

/-- The exact provider records agree at the physically selected floor. -/
theorem provider {G : Gauge} (s : Sheet G) (T : MapPrices) (n : ℕ → ℕ) :
    ThroughLaunch.bountyV s T n = UVExtension.Case.provider s T n := by
  unfold ThroughLaunch.bountyV UVExtension.Case.provider
  rw [prices]

end YM.Integration.WilsonLimitConstruction.FundedRetargetAgreement
end
