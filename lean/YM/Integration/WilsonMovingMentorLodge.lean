import YM.AllOrder.Horizon.Order
import YM.Integration.WilsonMovingMentorOffer

/-! The original spatial and derivative rule of the course receives its tariff before the
physical block lengths and delays, on the actual register of the funded factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorLodge
open RG Push PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.Foundations Org RG.Supply Push.PriceCompiler ThroughLaunch
open WilsonLimitConstruction.FundedCompanySelection WilsonMovingStoredFactor

def Held {G : Gauge} (rate : ℕ → ℝ) : Prediction G := fun {_} {D} {A} F =>
  AllOrder.Shop.Lodge D F.shape (fun _ i => rate i) A.delay

theorem paid {G : Gauge} (ask : WilsonMovingShadowPrices.Ask) (slow : ℝ → ℝ) (rate : ℕ → ℝ) (positive : ∀ i, 0 < rate i) :
    WilsonMovingMentorOwnership.AllPrices ask slow (@OnMenu G (@Held G rate)) := by
  intro s T rows E charts C v baton wanting wage
  obtain ⟨q,book⟩ := AllOrder.Shop.leased s rows E
  refine ⟨q,?_⟩
  intro l hl earlier D w u Z φ S θ p P V pocket cap
  let M : Metals G := ⟨raise s l,raging s T,chart G,chart_ok G⟩
  have room : AllOrder.Shop.Freq (s:=M.p) E q := book
  have reach (j i : ℕ) (_ : StepStages j i) : (rows j i).rate < -(3/8:ℝ) := by
    exact (E j i).reach.trans (by rw [wanting]; norm_num)
  obtain ⟨W,hw,paid⟩ := AllOrder.Shop.funding (X:=M) D Z (fun _ i => rate i)
    V room (fun j => (hl j).trans (D.large j).need) reach (fun _ i => positive i)
  refine ⟨W,hw,?_⟩
  intro W' hW b I hp B light A η z E' X J K' f shelter works divides owner menu
  exact paid _ hW

end YM.Integration.WilsonMovingMentorLodge
end
