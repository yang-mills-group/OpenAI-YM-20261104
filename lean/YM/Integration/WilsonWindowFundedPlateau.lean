import YM.Integration.WilsonLimitConstruction.FundedPlateauRun
import YM.Integration.WilsonWindowSelectionRun

/-! Original Wilson campaign selection with the marked-window invoice.
Physical choices follow YM.Integration.WilsonLimitConstruction.FundedPlateauRun; see the source map. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPlateauRun

open Filter Lattice RG RG.Supply Precision
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12

universe v
variable {G : Gauge}


/-- Every preselected quote and prepaid factor prediction travels through the
same physical blocks and Wait as the regulator comparison. -/
theorem purchaseAtPhysicalMenu (hG : G.Simple) (Δ : Decal G) {ε : ℝ} (hε : 0 < ε)
    (Demand : Sheet G → MapPrices → Type v) (available : ∀ s q, Nonempty (Demand s q))
    (extra : ∀ s q, Demand s q → ℕ → ℕ)
    (numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ)
    (postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ)
    (prediction : FundedCompanySelection.Prediction G)
    (paid : YM.Integration.WilsonFundedWindowMenu.AllPrices (@prediction)) :
    ∃ A : Purchase Δ ε Demand extra numeric postnumeric, prediction A.run.kit := by
  have hTrue : R2I.EventuallyPaid (fun _ : Levels G => True) :=
    fun _ _ _ V => ⟨V, Push.PriceCompiler.DelayLe.refl _, by intros; trivial⟩
  obtain ⟨R, T, hPrediction, hpenalty, hselected, horders, hWindows, hTreasury,
      hPeriod, ⟨W⟩, hFunded, _, hReadout, _⟩ :=
    R2I.RG05Joint.selectRunAtPhysicalMenu
      (Λ := NativeFVAPlateau.Funded) (RiderResourceDynamics.defaultDynamics G).cultivate
      (CustodyR.minted G) Δ ε hε hG hTrue (fun _ _ h => h)
      Demand available extra numeric postnumeric (@prediction) paid
  exact ⟨⟨R, T, W, hpenalty, hselected, horders, hTreasury, hPeriod, hFunded,
    hReadout, hWindows⟩, hPrediction⟩


end YM.Integration.WilsonLimitConstruction.FundedPlateauRun
end

