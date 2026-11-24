import YM.Integration.WilsonOrdinaryRetainedWindow
import YM.Integration.WilsonReportSignedLabel

/-! The remaining signed ordinary matrix measurement is one real, unmasked
pair of the two originally registered physical labels. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryCombinedSource
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportReflectedGram WilsonReportEarlySmearing WilsonReportColumnCut
open WilsonOrdinaryHomogeneousDetectors WilsonOrdinaryWindowBuyer WilsonOrdinaryFourGram
open WilsonReportWindowSource
open Pert.Asymptotics
open Cells Push.GridApprox
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} {F : Final R.family f S}

open WilsonOrdinaryWindowBuyer WilsonOrdinarySignedWindow WilsonReportSignedLabel
open WilsonOrdinaryHomogeneousDetectors WilsonOrdinaryRetainedWindow

variable {L : Layout F} {J : ℝ→tower S} {g : ℝ→ℝ} {d e : ℕ}
variable {A B₂ : Module.End ℂ ((Bel R.family.book).Field d)}

/-- The signed four-window statistic is literally the normalized full bead
moment of its previously deposited combined label and its common column. -/
theorem combined {r : ℝ} (P : WindowRows F J L g d A B₂ e r) (i j : Handle F d)
    (N p : ℕ) (grade : R.family.ref d ≤ (berth R 28 (L.level r))) (cutoff : (berth R 28 (L.level r))<N) :
    WilsonOrdinaryWindowBuyer.cut F J L g d P (N,p) i j =
      (WilsonReportWindowMatrix.joint L d ![input P i,P.right j] r (berth R 28 (L.level r)) N p).re := by
  rw [WilsonOrdinarySignedWindow.integral P N p cutoff]
  apply congrArg Complex.re
  apply integral_congr_ae
  filter_upwards [] with U
  rw [Fin.prod_univ_two]
  have first := ((WilsonReportSignedLabel.original P N p i grade cutoff.le).2.2.2.2.1 U).1
  exact congrArg (·*reflected P N p j U) first

/-- The alarm error for this *one* registered source is paid to arbitrary
order, before every physical cutoff, period and choice of the funded rows. -/
theorem purchased (L : Layout F) (g : ℝ→ℝ) (d : ℕ) (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (funding : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) (E : OPE.Services R.family f S)
    {u : Filter UVIndex} {Q : Lenses.Mantle F u} (hQ : Pegs Q L)
    (placed : L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B)
    (scene : Pier.Scene.ScenePlan R F L) (hg : Coupling G g) (e q : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ r in trail,∀ (J : ℝ→tower S) (A B₂ : Module.End ℂ ((Bel R.family.book).Field d))
      (P : WindowRows F J L g d A B₂ e r) (i j : Handle F d) (N p : ℕ), (berth R 28 (L.level r))<N →
      |WilsonOrdinaryWindowBuyer.cut F J L g d P (N,p) i j -
        (openedPair L d r N p ![input P i,P.right j]).re| ≤ ε*(g r)^q := by
  have read := WilsonOrdinaryRetainedWindow.prior_pair L g d hG W funding subsidy pace hB E hQ placed scene hg (e+1) q hε
  have heat := (Station.hat_rate R.family.path.levels hG).comp hQ.level.growing
  have small := (Coupling.conforms hG hg).eventually (gt_mem_nhds (zero_lt_one : (0:ℝ)<1))
  filter_upwards [read,heat.eventually_ge_atTop 4,hQ.level.growing.eventually_ge_atTop (R.family.ref d),
      hg.positive,small] with r now warm grade positive tiny
  intro J A B₂ P i j N p after
  let β := R.family.path.levels.clock.hatBeta (L.level r)
  have hot : 4≤β := warm
  have hn : 0≤β := by linarith only [hot]
  have sign : |g r|≤1 := by rw [abs_of_nonneg positive.le]; exact tiny.le
  have funds (s : Fin 2) : mass R.family d (L.shift d r ((![input P i,P.right j] : Fin 2→_) s))≤β^(e+1) := by
    rw [pow_succ]
    fin_cases s
    · exact (WilsonReportSignedLabel.mass_paid P sign i).trans
        ((mul_le_mul_of_nonneg_right hot (pow_nonneg hn e)).trans_eq (mul_comm _ _))
    · exact (P.second_cost j).trans (le_mul_of_one_le_right (pow_nonneg hn e) (by linarith only [hot]))
  have bill := now ![input P i,P.right j] funds N p after
  rw [combined P i j N p (grade.trans (arrival R 28 (L.level r)).1.le) after,←Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans bill

end YM.Integration.WilsonOrdinaryCombinedSource
