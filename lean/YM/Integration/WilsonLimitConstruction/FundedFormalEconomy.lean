import YM.Integration.WilsonLimitConstruction.FundedPlateauRun
import YM.Integration.NativeFormalEconomyAgreement
import YM.Integration.NativeFormalDetectorReadings
import YM.Integration.NativeFormalComplexReadout

/-! An arbitrary prepaid original selector retains a single physical
counterterm prescription, continuum economy and moving correlator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedFormalEconomy

open Lattice Labels Precision RG RG.Supply PhysicalNext.Repeat.Legato RegulatorIR
open PhysicalNext.Repeat.Daisy.Charity.RG12
open MS MS.Local.Physical MS.Menus MS.Land FVA2 FVA2.ColorCode FVA2.ArchTurn
open NativeFormalSharedCoupling NativeFormalPrescriptionAgreement

universe v
variable {G : Gauge}

/-- Both proofs concern one specified physical bank and one prescription. -/
def Selected (R : Run G) (hG : G.Simple) (B : Booked (wings G))
    (M : MS_Data G (angular B (warehouse R))) : Prop :=
  ∃ (P : Prescription (wings G)) (S : Blaze.ExactSpin (warehouse R) P)
    (U : Frost.Trusted P) (k : ℝ) (J : PositionX.Bend.Booth k (warehouse R).F),
    RadL.Reg B ∧ Atoll.Main.Economy hG (warehouse R) B M P S U J ∧
    MovingOn R (NativeFormalDeckAgreement.moving_deck R) (angular B (warehouse R)) M P

def Bank (R : Run G) (hG : G.Simple) :=
  Σ B : Booked (wings G), {M : MS_Data G (angular B (warehouse R)) // Selected R hG B M}

abbrev Bank.book {R : Run G} {hG : G.Simple} (W : Bank R hG) := W.1

abbrev Bank.data {R : Run G} {hG : G.Simple} (W : Bank R hG) := W.2.1

theorem Bank.accepted {R : Run G} {hG : G.Simple} (W : Bank R hG) :
    Selected R hG W.book W.data := W.2.2

theorem from_purchase (hG : G.Simple) {Δ : Decal G} {ε : ℝ}
    {Demand : Sheet G → MapPrices → Type v} {extra : ∀ s q, Demand s q → ℕ → ℕ}
    {numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ}
    {postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ}
    (A : FundedPlateauRun.Purchase Δ ε Demand extra numeric postnumeric) :
    Nonempty (Bank A.run hG) := by
  obtain ⟨B, M, P, S, U, k, J, hB, H, K⟩ :=
    NativeFormalEconomyAgreement.common A.run hG (A.correlations hG)
  exact ⟨⟨B, M, P, S, U, k, J, hB, H, K⟩⟩

/-- The cost witness, native factor prediction and both original formal
suppliers all live on the literal Run purchased at the prescribed penalty. -/
theorem purchase (hG : G.Simple) (Δ : Decal G) {ε : ℝ} (hε : 0 < ε)
    (Demand : Sheet G → MapPrices → Type v) (available : ∀ s q, Nonempty (Demand s q))
    (extra : ∀ s q, Demand s q → ℕ → ℕ)
    (numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ)
    (postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ)
    (prediction : FundedCompanySelection.Prediction G)
    (paid : FundedPredictionSupply.AllPrices (@prediction)) :
    ∃ A : FundedPlateauRun.Purchase Δ ε Demand extra numeric postnumeric,
      prediction A.run.kit ∧ Nonempty (Bank A.run hG) := by
  obtain ⟨A, hA⟩ := FundedPlateauRun.purchase hG Δ hε Demand available extra numeric postnumeric
    (@prediction) paid
  exact ⟨A, hA, from_purchase hG A⟩

abbrev Data (B : Deck G) := Σ A : Booked B, MS_Data G A

def transport {D : Deck G} (e : D = wings G) (x : Data (wings G)) : Data D := e.symm ▸ x

private theorem panel_transport (R : Run G) {D : Deck G} (e : D = wings G)
    (x : Data (wings G)) (μ : ℝ) :
    NativeFormalDetectorReadings.panel R e (transport e x).2 μ =
      NativeFormalDetectorReadings.panel R rfl x.2 μ := by
  subst D
  rfl

variable {R : Run G} {hG : G.Simple}

def Bank.native (W : Bank R hG) : Data (nativeDeck R) :=
  transport (NativeFormalDeckAgreement.moving_deck R) ⟨angular W.book (warehouse R), W.data⟩

/-- The native moving data read exactly the physical continuum panel selected
in the very same funded economy. -/
theorem Bank.report (W : Bank R hG) (μ : ℝ) :
    YM.FVAAlt2.Home.Report.science μ W.native.2 R.family.labels =
      NativeFormalDetectorReadings.panel R rfl W.data μ :=
  (NativeFormalDetectorReadings.report R hG (NativeFormalDeckAgreement.moving_deck R) W.native.2 μ).trans
    (panel_transport R (NativeFormalDeckAgreement.moving_deck R) ⟨_, W.data⟩ μ)

/-- Both detector quadratures recover this complete continuum distribution. -/
theorem Bank.panel (W : Bank R hG) (μ : ℝ) (d k : ℕ)
    (p : YM.FVAAlt2.Home.Datum (FormalOPE.RG10.Position.Deck R.family.labels d)) :
    (Pic.marked (warehouse R) W.data μ).lives d k p.1.n p.1.test
        (FormalOPE.RG10.Position.deck R.family.labels d ∘ p.2) =
      ⟨PowerSeries.coeff k (YM.FVAAlt2.Home.Report.science μ W.native.2 R.family.labels d p),
        -PowerSeries.coeff k (YM.FVAAlt2.Home.Report.science μ W.native.2 R.family.labels d
          (NativeFormalComplexReadout.scale Complex.I p))⟩ := by
  have hd := NativeFormalDetectorReadings.report R hG rfl W.data μ
  rw [W.report μ, ← hd]
  exact NativeFormalComplexReadout.panel R hG W.data μ d p k

/-- The induced change of coupling is evaluated at this physical bank in
the purchased Run's own detector. -/
def Bank.convention (W : Bank R hG) (μ : ℝ) :=
  FormalOPE.RG10.Carryon.Convention (FormalOPE.RG10.Carryon.Init
    (NativeFormalDetectorReadings.panel R rfl W.data μ) (RegulatorIR.FVAAlt2.Moving.Study.Plan R).stock)

theorem Bank.coupling (W : Bank R hG) (μ : ℝ) :
    YM.FVAAlt2.Convert.f (RegulatorIR.FVAAlt2.Moving.Study.Plan R) μ W.native.2 =
      (W.convention μ).refund := by
  unfold Bank.convention
  rw [← W.report μ]

/-- The full field matrix on the paid receiver's coordinates. -/
def Bank.field (W : Bank R hG) (μ : ℝ) (d : ℕ) :=
  (Matrix.of (((RegulatorIR.FVAAlt2.Moving.Study.Plan R).stock d).position
    (NativeFormalDetectorReadings.panel R rfl W.data μ d))).map (W.convention μ).refund.charge

theorem Bank.normalized_field (W : Bank R hG) (μ : ℝ) (d : ℕ) :
    YM.FVAAlt2.Mass.ζfinal (RegulatorIR.FVAAlt2.Moving.Study.Plan R) μ W.native.2 d =
      FormalOPE.RG10.Position.Grade.tile (FormalOPE.RG10.Position.Deck.price R.family.labels d)
        (W.field μ d) := by
  unfold Bank.field Bank.convention
  rw [← W.report μ]

/-- The exact target of the original moving regulator estimates. -/
theorem Bank.target (W : Bank R hG) (μ : ℝ) (d : ℕ)
    (p : YM.FVAAlt2.Home.Datum (FormalOPE.RG10.Position.Deck R.family.labels d)) :
    YM.FVAAlt2.Home.mix ((YM.FVAAlt2.Convert.f (RegulatorIR.FVAAlt2.Moving.Study.Plan R) μ W.native.2).charge ∘
        YM.FVAAlt2.Home.Report.science μ W.native.2 R.family.labels d)
        (YM.FVAAlt2.Mass.ζfinal (RegulatorIR.FVAAlt2.Moving.Study.Plan R) μ W.native.2 d) p =
      YM.FVAAlt2.Home.mix ((W.convention μ).refund.charge ∘ NativeFormalDetectorReadings.panel R rfl W.data μ d)
        (FormalOPE.RG10.Position.Grade.tile (FormalOPE.RG10.Position.Deck.price R.family.labels d) (W.field μ d)) p := by
  rw [W.coupling μ, W.report μ, W.normalized_field μ d]

end YM.Integration.WilsonLimitConstruction.FundedFormalEconomy
end
