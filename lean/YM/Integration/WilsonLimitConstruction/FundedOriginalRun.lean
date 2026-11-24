import YM.R2I.Campaign.Accepted
import YM.Integration.FiniteVolumeLimit.All
import YM.Integration.ActualOriginalOrbitCoefficients
import YM.Integration.ActualRunNativeComponentRecipe
import YM.Integration.WilsonLimitConstruction.FundedPlateauRun
import YM.PhysMS.Frame.Journey

/-!
One funded constant-support-100 Run retains its native startup attachment,
all-order profile bounds, treasury/period/readout receipts, trace exclusions,
every-phase reconstruction, ordinary OPE suppliers and a calibrated all-length
physical frame on the same Final, accepted FVA2 formal comparison on its own
field warehouse, and exact original finite-side RG10 coefficient identity. The
existing proved `garment10`, native component choice and concrete resource
calendar supply the constructor inputs; no analytic premise is added.

The concrete resource calendar uses the original Rolls and PostCost.
The moving-regulator comparison uses the purchased kernel's FVA windows and
the correlation hierarchy on the same Run. The reconstruction, FVA2 packing
and RG10 results retain their respective spectral and coefficientwise statements.
The Trace calibration fixes the measured frame and coupling together.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonLimitConstruction

open Filter Lattice PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12
open scoped BigOperators Topology

universe u

/-- The reconstructed objects, physical frame and exact coefficient result carried
by one original campaign. -/
def FundedOriginalProperties {G : Gauge} (hG : G.Simple) (ε : ℝ)
    {R : Run G} {T : Campaign R} (W : Campaign.Pillars R T) : Prop :=
  R.family.path.levels.clock.kernel.penalty = ε ∧
  R2IGoals.Broad.{u} (garment10 G) W hG ∧
  ActualRunNativeComponentRecipe.Attached R ∧
  (∀ j, j ≤ (R.metals.p.profile j).order ∧
    j ≤ (R.metals.p.profile j).power) ∧
  CalendarTreasuryPurchase.TreasuryFunded R.family.path.levels ∧
  CommonPeriodPurchase.Funded R.metals.K R.metals.O R.family.path.levels ∧
  RG05Preconstruction.ReadoutPurchase R.b ∧
  Run.Ties R ∧
  FVA2.Atoll.Main.Packing hG
    (FVA2.Atoll.share R.family R.makes (CoefficientBridge.run_valuation R)) ∧
  (∀ v : Extraction.Order,
    ∃ (w : Extraction.Order) (S : Table R.family.book)
      (F : Spec.Final R.family (v.refine w) S)
      (L : EveryPhase.Almanac F)
      (Q : OPE.Orbits.Reader F.sector.derivatives F.sector.turns
        F.room.kernel.spin),
      EveryPhase.Completed F L ∧
      Trace.Target.Result.{u} F hG ∧ Trace.Target.Exclusion.{u} F ∧
      OPE.Facilities R.family (v.refine w) S ∧
      OPE.Orbits.Foundation F Q ∧
      ∃ (H : (Climb.Bel R.family.book).Hierarchy)
        (Z : Trace.Terrace.Arch R.family) (l : Ultrafilter (ℕ × ℕ)),
        Trace.Pilot.Bliss F l Z H ∧
        ∃ (P P' : ℝ → Spin.change S 4) (J : ℝ → PhysMS.tower S)
          (φ : E4 → ℝ) (a d e : ℝ → ℝ),
          (∀ᶠ r in Trace.Pilot.trail, J r 4 = P' r) ∧
          Trace.Target.XScheme F hG H l P P' φ ∧
          Trace.Target.FieldComparison F H Z P P' a d e ∧
          PhysMS.Leading F J ∧
          ∀ d, ∀ᶠ r in Trace.Pilot.trail,
            PhysMS.Frame.obedient F H (J r) d) ∧
  ∀ (B : MS.Local.Physical.Deck G) (I : Type) [Fintype I] [LinearOrder I]
    (degree rank : I → ℕ)
    (label : (i : I) → B.BIndex (degree i : ℤ) (rank i))
    (N p : ℕ) (x : I → Cover) (k : ℕ),
    let he := even_iff_two_dvd.mpr
      (ActualOriginalFiniteCoefficients.side_admissible R N p).2
    PowerSeries.coeff (k + ∑ i, rank i)
      ((FormalOPE.RG10.InversionTop.feed he).step
        (FormalOPE.RG10.InversionTop.vertices G (R.family.side N p))
        (FormalOPE.RG10.InversionTop.raw
          (PertExtension.Orb.restrictedO
            (ActualOriginalFiniteCoefficients.joint R B degree rank label
              N p Finset.univ (wrap (R.family.side N p) ∘ x))))) =
    (ActualLeadingIR.engineeringScale R.family degree N : ℂ) *
      PowerSeries.coeff k
        (ActualOrbLeadingIR.orbitSeries R.family N p degree x
          (ActualOriginalOrbitCoefficients.columns R B degree rank label))

/-- Use the receipts of this campaign to obtain its original outputs. This
also applies to a Run on which additional predictions or costs were purchased. -/
theorem fundedOriginalRun_on {G : Gauge} (hG : G.Simple) {ε : ℝ}
    {R : Run G} {T : Campaign R} (W : Campaign.Pillars R T)
    (hpenalty : R.family.path.levels.clock.kernel.penalty = ε)
    (hFunded : R2I.Funded (garment10 G) R T)
    (hAttached : ActualRunNativeComponentRecipe.Attached R)
    (horders : ∀ j, j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power)
    (hTreasury : CalendarTreasuryPurchase.TreasuryFunded R.family.path.levels)
    (hPeriod : CommonPeriodPurchase.Funded R.metals.K R.metals.O R.family.path.levels)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b) :
    FundedOriginalProperties.{u} hG ε W := by
  have hBroad := R2IGoals.fromFunded.{u} W hG hFunded
  have hties := (Run.again R hG).1
  refine ⟨hpenalty, hBroad, hAttached, horders, hTreasury, hPeriod, hReadout,
    hties, FVA2.Atoll.Main.joint_M hG _, ?_, ?_⟩
  · intro v
    obtain ⟨w, _, S, F, _, L, Q, _, _, _, _, hL, hTrace,
      hFacilities, hFoundation, _, _, _⟩ := hBroad.refine v
    exact ⟨w, S, F, L, Q, hL, hTrace, hTrace.exclude,
      hFacilities, hFoundation, PhysMS.Frame.meter_found.{u} hG F hTrace⟩
  · intro B I _ _ degree rank label N p x k
    exact ActualOriginalOrbitCoefficients.RG10_coefficient
      R B degree rank label N p x k

/-- The accepted moving correlations and the prepaid factor predicate
belong to the same Run as every reconstructed output. -/
theorem fundedOriginalRun_with_prediction
    {G : Gauge} (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (prediction : FundedCompanySelection.Prediction G)
    (paid : FundedPredictionSupply.AllPrices (@prediction)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      prediction R.kit ∧ NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W := by
  obtain ⟨A, hPrediction⟩ := FundedPlateauRun.purchase hG (garment10 G) hε
    (fun s (_ : Precision.MapPrices) => NativeComponentRecipe.Choice s)
    (fun s _ => NativeComponentRecipe.available hG s)
    NativeComponentRecipe.floor NativeComponentRecipe.numeric
    ActualRunNativeComponentRecipe.postnumeric (@prediction) paid
  exact ⟨A.run, A.campaign, A.pillars, hPrediction, A.correlations hG,
    fundedOriginalRun_on.{u} hG A.pillars A.penalty A.funded
      (ActualRunNativeComponentRecipe.of_preselection A.run A.selected)
      A.orders A.treasury A.period A.readout⟩

/-- The accepted moving correlations and all original reconstructed outputs
belong to the same positive-penalty Run. -/
theorem fundedOriginalRun_with_moving_correlations
    {G : Gauge} (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W := by
  obtain ⟨R, T, W, _, hMoving, hOriginal⟩ :=
    fundedOriginalRun_with_prediction.{u} hG hε (@FundedPredictionSupply.Always G)
      (fun s _ => FundedPredictionSupply.always s _)
  exact ⟨R, T, W, hMoving, hOriginal⟩

/-- Original funded reconstruction, formal FVA2 comparison and finite-side
coefficient dictionary for the sole selected Run. -/
theorem fundedOriginalRun
    {G : Gauge} (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      R.family.path.levels.clock.kernel.penalty = ε ∧
      R2IGoals.Broad.{u} (garment10 G) W hG ∧
      ActualRunNativeComponentRecipe.Attached R ∧
      (∀ j, j ≤ (R.metals.p.profile j).order ∧
        j ≤ (R.metals.p.profile j).power) ∧
      CalendarTreasuryPurchase.TreasuryFunded R.family.path.levels ∧
      CommonPeriodPurchase.Funded R.metals.K R.metals.O R.family.path.levels ∧
      RG05Preconstruction.ReadoutPurchase R.b ∧
      Run.Ties R ∧
      FVA2.Atoll.Main.Packing hG
        (FVA2.Atoll.share R.family R.makes (CoefficientBridge.run_valuation R)) ∧
      (∀ v : Extraction.Order,
        ∃ (w : Extraction.Order) (S : Table R.family.book)
          (F : Spec.Final R.family (v.refine w) S)
          (L : EveryPhase.Almanac F)
          (Q : OPE.Orbits.Reader F.sector.derivatives F.sector.turns
            F.room.kernel.spin),
          EveryPhase.Completed F L ∧
          Trace.Target.Result.{u} F hG ∧ Trace.Target.Exclusion.{u} F ∧
          OPE.Facilities R.family (v.refine w) S ∧
          OPE.Orbits.Foundation F Q ∧
          ∃ (H : (Climb.Bel R.family.book).Hierarchy)
            (Z : Trace.Terrace.Arch R.family) (l : Ultrafilter (ℕ × ℕ)),
            Trace.Pilot.Bliss F l Z H ∧
            ∃ (P P' : ℝ → Spin.change S 4) (J : ℝ → PhysMS.tower S)
              (φ : E4 → ℝ) (a d e : ℝ → ℝ),
              (∀ᶠ r in Trace.Pilot.trail, J r 4 = P' r) ∧
              Trace.Target.XScheme F hG H l P P' φ ∧
              Trace.Target.FieldComparison F H Z P P' a d e ∧
              PhysMS.Leading F J ∧
              ∀ d, ∀ᶠ r in Trace.Pilot.trail,
                PhysMS.Frame.obedient F H (J r) d) ∧
      ∀ (B : MS.Local.Physical.Deck G) (I : Type) [Fintype I] [LinearOrder I]
        (degree rank : I → ℕ)
        (label : (i : I) → B.BIndex (degree i : ℤ) (rank i))
        (N p : ℕ) (x : I → Cover) (k : ℕ),
        let he := even_iff_two_dvd.mpr
          (ActualOriginalFiniteCoefficients.side_admissible R N p).2
        PowerSeries.coeff (k + ∑ i, rank i)
          ((FormalOPE.RG10.InversionTop.feed he).step
            (FormalOPE.RG10.InversionTop.vertices G (R.family.side N p))
            (FormalOPE.RG10.InversionTop.raw
              (PertExtension.Orb.restrictedO
                (ActualOriginalFiniteCoefficients.joint R B degree rank label
                  N p Finset.univ (wrap (R.family.side N p) ∘ x))))) =
        (ActualLeadingIR.engineeringScale R.family degree N : ℂ) *
          PowerSeries.coeff k
            (ActualOrbLeadingIR.orbitSeries R.family N p degree x
              (ActualOriginalOrbitCoefficients.columns R B degree rank label)) := by
  obtain ⟨R, T, W, _, h⟩ := fundedOriginalRun_with_moving_correlations.{u} hG hε
  exact ⟨R, T, W, h⟩

end YM.Integration.WilsonLimitConstruction
end
