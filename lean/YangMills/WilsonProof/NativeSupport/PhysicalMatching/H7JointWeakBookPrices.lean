import YM.Integration.WilsonWindowJointPurchase

set_option autoImplicit false
noncomputable section
namespace PhysicalMatching.H7JointWeakBookPrices
open YM YM.Integration
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open Push.PriceCompiler ThroughLaunch WilsonLimitConstruction.FundedCompanySelection
open WilsonFundedWindowMenu WilsonWindowJointPurchase Next.Foundations
open scoped Classical

variable {G : Gauge}

theorem joint (X BB : Prediction G) (first : AllPrices (@X)) (second : AllPrices (@BB)) :
    AllPrices (@Together G (@X) (@BB)) :=
  fun sheet tariff => YM.Integration.WilsonWindowJointPurchase.joint
    (first sheet tariff) (second sheet tariff)

/-- Pre-costs survive raising the floor. Post-costs may read the resulting actual Rolls. -/
structure Costs (G : Gauge) where
  pre : Sheet G → ℕ → ℝ
  post : {s : Sheet G} → Rolls s → ℕ → ℝ
  pre_nonneg : ∀ s j, 0 ≤ pre s j
  post_nonneg : ∀ {s : Sheet G} (D : Rolls s) j, 0 ≤ post D j
  raised : ∀ (s : Sheet G) (l : ℕ → ℕ), pre (ThroughLaunch.raise s l) = pre s

def preBill (c : Costs G) (floor : Sheet G → ℕ → ℕ) (s : Sheet G) (j : ℕ) : ℕ :=
  max (floor s j) (Nat.ceil ((2 + c.pre s j) ^ (j ^ 2)))

def postBill (c : Costs G) (voucher : {s : Sheet G} → Rolls s → ℕ → ℝ)
    {s : Sheet G} (D : Rolls s) (j : ℕ) : ℝ :=
  max (voucher D j) (Real.exp (Real.exp (2 + c.post D j)))

def budget (c : Costs G) (floor : Sheet G → ℕ → ℕ)
    (voucher : {s : Sheet G} → Rolls s → ℕ → ℝ) : Prediction G :=
  fun {M} {D} {A} _ => M.O = chart G ∧ preBill c floor M.p ≤ M.p.floorL ∧
    postBill c (@voucher) D ≤ A.delay.betaEntry

theorem purchase (c : Costs G) (floor : Sheet G → ℕ → ℕ)
    (same : ∀ (s : Sheet G) (l : ℕ → ℕ), floor (ThroughLaunch.raise s l) = floor s)
    (voucher : {s : Sheet G} → Rolls s → ℕ → ℝ) :
    AllPrices (@budget G c floor (@voucher)) := by
  intro s price targets expenses flags programs wages baton
  refine ⟨preBill c floor s,?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu V quarter
  let later := postBill c (@voucher) D
  let W : Delays θ := { V with betaEntry := later ⊔ V.betaEntry }
  refine ⟨W,⟨le_sup_right,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro U hU bar wait priced B archive origins rank
  dsimp only
  intro η q exchange aux rider booth sheltered works divides
  refine ⟨rfl,?_,(show later ≤ W.betaEntry from le_sup_left).trans hU.beta⟩
  change preBill c floor (ThroughLaunch.raise s l) ≤ l
  intro j
  simpa only [preBill,same,c.raised] using hl j

end PhysicalMatching.H7JointWeakBookPrices
end
