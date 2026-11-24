import YM.Integration.WilsonMatrixTicketLanesReportedClock
import YM.Integration.WilsonMatrixTicketLanesReportedNumerics

/-! Numerical all-order finite reported forest comparison on the actual first and forward Wilson stops. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedRun
open Filter Lattice RG FVA2 FVA2.CityHistory FVA2.Both.Passage FVA2.Both.Passage.Cohort
open FormalOPE.RG10.BlockGauge MS MS.Rake MS.Land MS.Tide MS.Orbit MS.Dial MS.Fleet MS.Local.Physical
open PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2.Lodge WilsonMatrixTicketLanesMirrorClock
open scoped Topology Classical BigOperators
variable {G : Gauge} {B : Deck G} 

open WilsonMatrixTicketLanesReportedClock
open WilsonMeasuredWindow

/-- A single original fully corrected finite-forest report covers all labels, orders and tolerances on the
same extraction, with the physical positions sampled at the exact reported cutoff. -/
def Statement (R : Run G) {O : Booked B} (M : MS_Data G O) (A : Prescription B) (f : Extraction.Order)
    (simple : G.Simple) (J : ℕ) (hJ : 0 < J) {c : ℝ} (hc : 1 < c) : Prop :=
    ∀ᶠ b : ℕ in atTop, ∀ (u : Filter (ℕ×ℕ)), u ≤ f.fuse →
      ∀ (σ : (w : ActualOuterQuarterProfile.Cutoffs ℝ) → Picks R.family.path w.2.2) (μ : ℝ) (n : ℕ)
        (z : ℝ → Fin n → MS.Tone.QP) (K η : ℝ), 0 ≤ K → ∀ hη : 0 < η,
        (∀ r i, ‖z r i‖ ≤ K) → (∀ r i j, i ≠ j → η ≤ ‖z r i-z r j‖) →
        let m := stop R.family.path.levels simple J
        let U := upper R simple J c
        let depth := fun r => U r-b
        let θ := aperture R simple J c η
        let hθ := (parameters R simple J hJ hc hη).1
        let P := ActualRelativeProfileTrial.trial R (fun r => b+depth r) θ hθ μ z
        let L := WilsonMatrixTicketLanesReportedProfiles.panel R b depth σ
        ∃ (paid : (w : ActualOuterQuarterProfile.Cutoffs ℝ) → Long (L w)) (E : (w : _) → Exhibit (L w)),
          (∀ w, (E w).chart=R.metals.O ∧ (E w).quotes=quotes R.family.path w.2.2 b (depth w.1) ∧
            ∀ V : Warehouse G, CapReady.Article V (L w) (E w) (paid w)) ∧
          (∀ᶠ r in 𝓝[>] (0:ℝ), b+depth r = U r ∧ Real.exp (θ r) = r/R.family.S.a (U r)) ∧
          ∀ (v : Fin n → Label B) (s : Finset (Fin n)) (q order : ℕ) (fee : ℝ), 0 < fee →
            ∀ᶠ w in (𝓝[>] (0:ℝ)).curry u,
              ‖fare (Label.h ∘ v) P.profile (WilsonMatrixTicketLanesMirrorAccuracy.receipts
                (WilsonMatrixTicketLanesNativePrices.warehouse R) P A μ v L E) s q w -
                Dial.tour M v μ (testP P w) s q‖ ≤ fee *
                Pert.Asymptotics.regulatorRun R.family w.2.1 w.2.2 (m w.1) ^ order

theorem original (R : Run G) {O : Booked B} (M : MS_Data G O) (A : Prescription B)
    (matched : TaylorOKPl M (FVAAlt2.Lobby.Table (basisR R) B) A) (f : Extraction.Order)
    (simple : G.Simple) (J : ℕ) (hJ : 0 < J) {c : ℝ} (hc : 1 < c) : Statement R M A f simple J hJ hc := by
  filter_upwards [WilsonMatrixTicketLanesReportedNumerics.original (I:=ℝ) R M A matched simple] with b funded
  intro u hu σ μ n z K η hK hη capped separate
  let m := stop R.family.path.levels simple J
  let U := upper R simple J c
  let depth := fun r => U r-b
  let θ := aperture R simple J c η
  obtain ⟨hθ,growing,small⟩ := parameters R simple J hJ hc hη
  have clock := actual R simple J hJ hc η b
  have physical := funded (𝓝[>] (0:ℝ)) f u hu m (stop_tendsto R.family.path.levels simple J hJ)
    c hc depth σ θ hθ growing (clock.mono fun _ h => h.2.2.2) μ n z K η hK hη capped separate small
  obtain ⟨paid,E,source,order⟩ := physical
  refine ⟨paid,E,source,?_,order⟩
  filter_upwards [clock] with r bought
  exact ⟨by have past := bought.1; omega, bought.2.2.1⟩

end YM.Integration.WilsonMatrixTicketLanesReportedRun
