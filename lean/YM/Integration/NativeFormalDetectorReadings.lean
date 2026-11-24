import YM.Integration.NativeFormalReadoutAgreement

/-! The numerical normalization at the original moving detector can be
computed from the FVA2 physical panel, including both the coupling and
the entire graded matrix of field payments. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalDetectorReadings

open Lattice Labels RegulatorIR PhysicalNext.Repeat.Legato
open MS MS.Local.Physical MS.Land
open FVA2 FVA2.ColorCode
open RegulatorIR.FVAAlt2.Moving
open FormalOPE.RG10.Carryon FormalOPE.RG10.Position.Grade
open NativeFormalPrescriptionAgreement NativeFormalSharedCoupling

variable {G : Gauge}

/-- The actual physical panel expressed in the original RG10 test coordinates. -/
def panel (R : Run G) {D : Deck G} (e : D = wings G) {A : Booked D}
    (M : MS_Data G A) (μ : ℝ) : Rack R.family.labels := by
  subst D
  exact fun d p => PowerSeries.mk fun k =>
    ((Pic.marked (warehouse R) M μ).lives d k p.1.n p.1.test
      (FormalOPE.RG10.Position.deck R.family.labels d ∘ p.2)).re

theorem report (R : Run G) (hG : G.Simple) {D : Deck G} (e : D = wings G)
    {A : Booked D} (M : MS_Data G A) (μ : ℝ) :
    YM.FVAAlt2.Home.Report.science μ M R.family.labels = panel R e M μ := by
  subst D
  funext d p
  ext k
  simp only [panel, PowerSeries.coeff_mk]
  exact NativeFormalReadoutAgreement.panel R hG M μ d p k

/-- The convention recorded by the original Run's detector. -/
def convention (R : Run G) {A : Booked (nativeDeck R)} (M : MS_Data G A) (μ : ℝ) :=
  Convention (Init (panel R (NativeFormalDeckAgreement.moving_deck R) M μ) (Study.Plan R).stock)

theorem charged (R : Run G) (hG : G.Simple) {A : Booked (nativeDeck R)}
    (M : MS_Data G A) (μ : ℝ) : YM.FVAAlt2.Convert.χ (Study.Plan R) M μ = convention R M μ :=
  congrArg (fun W : Rack R.family.labels => Convention (Init W (Study.Plan R).stock))
    (report R hG (NativeFormalDeckAgreement.moving_deck R) M μ)

theorem coupling (R : Run G) (hG : G.Simple) {A : Booked (nativeDeck R)}
    (M : MS_Data G A) (μ : ℝ) : YM.FVAAlt2.Convert.f (Study.Plan R) μ M = (convention R M μ).refund :=
  congrArg (fun W => W.refund) (charged R hG M μ)

/-- The complete field matrix evaluated at the same Run's own detector. -/
def prefield (R : Run G) {A : Booked (nativeDeck R)} (M : MS_Data G A) (μ : ℝ) (d : ℕ) :=
  (Matrix.of (((Study.Plan R).stock d).position
    (panel R (NativeFormalDeckAgreement.moving_deck R) M μ d))).map (convention R M μ).refund.charge

theorem field (R : Run G) (hG : G.Simple) {A : Booked (nativeDeck R)}
    (M : MS_Data G A) (μ : ℝ) (d : ℕ) : YM.FVAAlt2.Convert.Zpre (Study.Plan R) μ M d = prefield R M μ d := by
  unfold YM.FVAAlt2.Convert.Zpre prefield
  rw [congrFun (report R hG (NativeFormalDeckAgreement.moving_deck R) M μ) d, coupling R hG M μ]

theorem normalized_field (R : Run G) (hG : G.Simple) {A : Booked (nativeDeck R)}
    (M : MS_Data G A) (μ : ℝ) (d : ℕ) : YM.FVAAlt2.Mass.ζfinal (Study.Plan R) μ M d =
      tile (FormalOPE.RG10.Position.Deck.price R.family.labels d) (prefield R M μ d) :=
  congrArg (tile (FormalOPE.RG10.Position.Deck.price R.family.labels d)) (field R hG M μ d)

/-- The transformed continuum target appearing in the moving regulator's
source comparison, in terms of the FVA2 physical panel at the same detector. -/
theorem target (R : Run G) (hG : G.Simple) {A : Booked (nativeDeck R)}
    (M : MS_Data G A) (μ : ℝ) (d : ℕ) (v : YM.FVAAlt2.Home.Datum
      (FormalOPE.RG10.Position.Deck R.family.labels d)) :
    YM.FVAAlt2.Home.mix ((YM.FVAAlt2.Convert.f (Study.Plan R) μ M).charge ∘
      YM.FVAAlt2.Home.Report.science μ M R.family.labels d) (YM.FVAAlt2.Mass.ζfinal (Study.Plan R) μ M d) v =
    YM.FVAAlt2.Home.mix ((convention R M μ).refund.charge ∘
      panel R (NativeFormalDeckAgreement.moving_deck R) M μ d)
      (tile (FormalOPE.RG10.Position.Deck.price R.family.labels d) (prefield R M μ d)) v := by
  rw [coupling R hG M μ, congrFun (report R hG (NativeFormalDeckAgreement.moving_deck R) M μ) d,
    normalized_field R hG M μ d]

end YM.Integration.NativeFormalDetectorReadings
end
