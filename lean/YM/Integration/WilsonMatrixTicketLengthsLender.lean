import YM.Integration.WilsonMatrixTicketCommonExpenses

/-! A two-stage purchase for an additional prediction on the retained factor.
The lender commits its sheet, kinetic prices and eligible blocks before the
company sets its length floor. The final reduction uses the same books,
directed history and kinetic invoice which the actual company supplied. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLengthsLender
open Function Filter Set Lattice RG RG.Supply Input Wilson Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup
open Org Next.Foundations Progress.DirectedRecipe
open PhysicalNext.Repeat.Roost
open WilsonLimitConstruction.FundedCompanySelection
open scoped Topology BigOperators Classical

structure Auction (G : Gauge) (K : KernelChoices) (v : Orders) (C : ℕ → ℝ)
    (claim : Prediction G) where
  sheet : Sheet G
  firstPrice : MapPrices
  price : MapPrices
  clock : ℕ → ℝ
  slope : ℕ → ℝ
  worth : Bid.Worth
  kernel : sheet.kernel = K
  stage : WithStage sheet v
  invoices (fees : Tariffs) (scope : Extra.Multi.Scope) :
    ∃ f : ℕ → ℕ, Perceived sheet firstPrice price clock slope C worth fees scope f
  allowed (k : ℕ → ℕ) (D : Rolls (raise sheet k)) : Prop
  floor : ℕ → ℕ
  select (k : ℕ → ℕ) (funded : floor ≤ k) : ∃ D : Rolls (raise sheet k), allowed k D
  paid {k : ℕ → ℕ} {D : Rolls (raise sheet k)}
    (X : Arms (M := bountyV sheet price k) D) (P : PostCost D)
    {θ : Protection D} (V : Delays θ) : Prop
  buy (k : ℕ → ℕ) (D : Rolls (raise sheet k)) (accepted : allowed k D) :
    ∀ (X : Arms (M := bountyV sheet price k) D) (P : PostCost D) (θ : Protection D)
      (V : Delays θ), ∃ W : Delays θ, DelayLe V W ∧ ∀ Y, DelayLe W Y → paid X P Y
  deliver {k : ℕ → ℕ} {D : Rolls (raise sheet k)} {P : PostCost D} {θ : Protection D}
    {V : Delays θ} {b : Bar V} {W : Wait b} {priced : Stock.Priced V}
    {B : Directed G W (chart G) (raging sheet price) P}
    (X : Factor (Alloy.mk P θ V b W priced B : Alloy (bountyV sheet price k) D)) :
    allowed k D → Imperial (s:=sheet) firstPrice price clock P B.a B.M B.kin →
    paid X.books P V → claim X

end YM.Integration.WilsonMatrixTicketLengthsLender
