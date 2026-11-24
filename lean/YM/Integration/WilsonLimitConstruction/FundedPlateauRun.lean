import YM.Integration.NativePreselectedPostnumericPeriodRun
import YM.Integration.NativeFVAPlateauCorrelation
import YM.Integration.RiderResourceDynamics

/-! The selected Run retains the postnumeric request, campaign funding and
the moving FVA regulator windows on the original clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPlateauRun

open Filter Lattice RG RG.Supply Precision
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12

universe v
variable {G : Gauge}

/-- Receipts attached to one literal Run and its campaign. -/
structure Purchase (Δ : Decal G) (ε : ℝ)
    (Demand : Sheet G → MapPrices → Type v)
    (extra : ∀ s q, Demand s q → ℕ → ℕ)
    (numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ)
    (postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ) where
  run : Run G
  campaign : Campaign run
  pillars : Campaign.Pillars run campaign
  penalty : run.family.path.levels.clock.kernel.penalty = ε
  selected : R2I.RG05Joint.PostnumericPreselection Demand extra numeric postnumeric run
  orders (j : ℕ) : j ≤ (run.metals.p.profile j).order ∧ j ≤ (run.metals.p.profile j).power
  treasury : CalendarTreasuryPurchase.TreasuryFunded run.family.path.levels
  period : CommonPeriodPurchase.Funded run.metals.K run.metals.O run.family.path.levels
  funded : R2I.Funded Δ run campaign
  readout : RG05Preconstruction.ReadoutPurchase run.b
  windows : NativeFVAPlateau.Funded run.family.path.levels

/-- Every preselected quote and prepaid factor prediction travels through the
same physical blocks and Wait as the regulator comparison. -/
theorem purchase (hG : G.Simple) (Δ : Decal G) {ε : ℝ} (hε : 0 < ε)
    (Demand : Sheet G → MapPrices → Type v) (available : ∀ s q, Nonempty (Demand s q))
    (extra : ∀ s q, Demand s q → ℕ → ℕ)
    (numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ)
    (postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ)
    (prediction : FundedCompanySelection.Prediction G)
    (paid : FundedPredictionSupply.AllPrices (@prediction)) :
    ∃ A : Purchase Δ ε Demand extra numeric postnumeric, prediction A.run.kit := by
  have hTrue : R2I.EventuallyPaid (fun _ : Levels G => True) :=
    fun _ _ _ V => ⟨V, Push.PriceCompiler.DelayLe.refl _, by intros; trivial⟩
  obtain ⟨R, T, hPrediction, hpenalty, hselected, horders, hWindows, hTreasury,
      hPeriod, ⟨W⟩, hFunded, _, hReadout, _⟩ :=
    R2I.RG05Joint.selectRunWithTreasuryPeriod_preselected_quote_orders_postnumeric_of_prediction_plateau
      (Λ := NativeFVAPlateau.Funded) (RiderResourceDynamics.defaultDynamics G).cultivate
      (CustodyR.minted G) Δ ε hε hG hTrue (fun _ _ h => h)
      Demand available extra numeric postnumeric (@prediction) paid
  exact ⟨⟨R, T, W, hpenalty, hselected, horders, hTreasury, hPeriod, hFunded,
    hReadout, hWindows⟩, hPrediction⟩

/-- Accepted moving correlations use the kernel and branch contract of this purchased Run. -/
theorem Purchase.correlations {Δ : Decal G} {ε : ℝ} {Demand : Sheet G → MapPrices → Type v}
    {extra : ∀ s q, Demand s q → ℕ → ℕ}
    {numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ}
    {postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ}
    (A : Purchase Δ ε Demand extra numeric postnumeric) (hG : G.Simple) :
    NativeFVAPlateau.Correlations A.run :=
  NativeFVAPlateau.correlations hG A.run A.windows

end YM.Integration.WilsonLimitConstruction.FundedPlateauRun
end
