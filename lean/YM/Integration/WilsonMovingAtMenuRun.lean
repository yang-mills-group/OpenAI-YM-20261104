import YM.Integration.WilsonMovingAtMenuPostnumericRun
import YM.Integration.WilsonOriginalMarkedExistence

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPlateauRun

open Filter Lattice RG RG.Supply Precision
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12

universe v
variable {slow : ℝ → ℝ} {G : Gauge}

/-- One retained physical family and its augmentation, purchased in the same chronological selection. -/
theorem purchaseAtMenu (ask : YM.Integration.WilsonMovingShadowPrices.Ask) (movable : Stationary.Movable slow) (hG : G.Simple) (Δ : Decal G) {ε : ℝ} (hε : 0 < ε)
    (Demand : Sheet G → MapPrices → Type v) (available : ∀ s q, Nonempty (Demand s q))
    (extra : ∀ s q, Demand s q → ℕ → ℕ)
    (numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ)
    (postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ)
    (prediction : FundedCompanySelection.Prediction G)
    (paid : YM.Integration.WilsonMovingCommonPrices.AllPrices ask slow (@YM.Integration.WilsonMovingStoredFactor.OnMenu G (@prediction))) :
    ∃ A : Purchase Δ ε Demand extra numeric postnumeric, prediction A.run.kit := by
  have hTrue : R2I.EventuallyPaid (fun _ : Levels G => True) :=
    fun _ _ _ V => ⟨V, Push.PriceCompiler.DelayLe.refl _, by intros; trivial⟩
  obtain ⟨R, T, hPrediction, hpenalty, hselected, horders, hWindows, hTreasury,
      hPeriod, ⟨W⟩, hFunded, _, hReadout, _⟩ :=
    R2I.RG05Joint.postnumericRunAtMenu (ask := ask) (movable := movable)
      (Λ := NativeFVAPlateau.Funded) (RiderResourceDynamics.defaultDynamics G).cultivate
      (CustodyR.minted G) Δ ε hε hG hTrue (fun _ _ h => h)
      Demand available extra numeric postnumeric (@prediction) paid
  exact ⟨⟨R, T, W, hpenalty, hselected, horders, hTreasury, hPeriod, hFunded,
    hReadout, hWindows⟩, hPrediction⟩

end YM.Integration.WilsonLimitConstruction.FundedPlateauRun
end
