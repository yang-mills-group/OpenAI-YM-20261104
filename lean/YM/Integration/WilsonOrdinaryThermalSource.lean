import YM.Integration.WilsonOrdinaryReportStock
import YM.RG17.Master

/-! One calendar of actual Wilson temperatures inside the original measuring
filter. Its current-date normalized factory columns converge jointly on
the same physical phase as the already deposited named source fields. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryThermalSource
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportReflectedGram WilsonReportEarlySmearing WilsonReportColumnCut
open WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep WilsonOrdinaryFourGram
open WilsonOrdinaryHomogeneousDetectors WilsonOrdinaryMeasuredMarch
open Cells Push.GridApprox
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

open WilsonOrdinaryHomogeneousDetectors

open MS MS.Menus MS.Local.Physical FVAAlt2 FVA2 Extra.Histories
open RegulatorIR.FVAAlt2.Lodge WilsonFactoryFiledGlyphs WilsonOrdinaryUltravioletPair
open WilsonOrdinaryPositionDecoder WilsonOrdinaryHomogeneousDetectors
variable {F : Final R.family f S} (L : Layout F) (d : ℕ)
variable {B : Deck G}

open MS.Land MS.Rake MS.Book MS.Book.Program
open FVAAlt2.Lobby FVAAlt2.Billing PowerSeries
open MeasureTheory

open WilsonOrdinaryReportDeposit Cells Push.GridApprox FullVolume

/-- Chosen on the existing original measuring filter, before all fields or tests. -/
structure Calendar where
  cuts : Ultrafilter UVIndex
  prior : (cuts:Filter UVIndex) ≤ L.lens
  beta : ℕ→ℝ
  measured (m : ℕ) : Tendsto (fun z : UVIndex=>R.family.path.β z.1 z.2 m) (cuts:Filter UVIndex) (𝓝 (beta m))
  band (m : ℕ) : beta m∈Set.Icc (R.family.path.levels.clock.hatBeta m / 2) (2*R.family.path.levels.clock.hatBeta m)

theorem original : Nonempty (Calendar L) := by
  letI : L.lens.NeBot := L.notbot
  let u := Ultrafilter.of L.lens
  have hu : (u:Filter UVIndex) ≤ L.lens := Ultrafilter.of_le _
  let T := R.family.path.levels.clock
  have band (m : ℕ) : ∀ᶠ z : UVIndex in (u:Filter UVIndex),R.family.path.β z.1 z.2 m∈Set.Icc (T.hatBeta m/2) (2*T.hatBeta m) := by
    filter_upwards [(large_mesh f m).filter_mono (hu.trans L.certified)] with z hz
    exact (F.room.cutoff.wilson.represents z.1 z.2 m hz).band
  have size (m : ℕ) : ∀ᶠ z : UVIndex in (u:Filter UVIndex),‖R.family.path.β z.1 z.2 m‖ ≤ 2*T.hatBeta m := by
    filter_upwards [band m] with z bound
    have pos : 0≤T.hatBeta m/2 := div_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed m).le) (by norm_num)
    rw [Real.norm_of_nonneg (pos.trans bound.1)]
    exact bound.2
  choose b hb using fun m=> RG12.ultrafilter_converges u (fun z : UVIndex=>R.family.path.β z.1 z.2 m) (2*T.hatBeta m) (size m)
  exact ⟨⟨u,hu,b,hb,fun m=>isClosed_Icc.mem_of_tendsto (hb m) (band m)⟩⟩

variable (M : Calendar L)

/-- Entire fine positive-coupling original column; its angular factor uses
this particular regulator at m, before the true fine transport. -/
def cut (H : ℕ) (r : ℝ) (w : R.family.label d) (z : UVIndex) : R.family.label d :=
  (((r/R.family.S.a (L.level r))^H : ℝ):ℂ) •
    RG17.Report.finiteColumn R.family F.room.cutoff d (L.level r) z.1 z.2 w

def primary (H : ℕ) (r : ℝ) (w : R.family.label d) : S.Field d :=
  (((r/R.family.S.a (L.level r))^H : ℝ):ℂ) •
    RG17.Report.master R.family S L.charts M.beta d (L.level r) w

theorem at_cut (H : ℕ) (r : ℝ) (w : R.family.label d) (z : UVIndex) :
    cut L d H r w z=
      RG17.atRef L d r z (input L d H r (RG17.Report.thresholdFactor R.family (fun j=>R.family.path.β z.1 z.2 j) (L.level r)) w) := by
  rw [RG17.atRef,shifted,map_smul]
  unfold cut RG17.Report.finiteColumn RG17.Report.rescales
  rw [smul_comm]

theorem at_limit (H : ℕ) (r : ℝ) (w : R.family.label d) :
    master L d r (input L d H r (RG17.Report.thresholdFactor R.family M.beta (L.level r)) w)=primary L d M H r w := by
  unfold master
  rw [LinearMap.comp_apply]
  change (RG12.engineering L.charts d (L.level r)) (L.shift d r (input L d H r _ w))=_
  rw [shifted,map_smul]
  rfl

/-- All numerical instances of the authentic original finiteColumn converge
along this SAME chosen calendar below L.lens. No new frame or measure. -/
theorem transported (H : ℕ) (r : ℝ) (w : R.family.label d) (admitted : R.family.ref d≤L.level r) :
    Tendsto (cut L d H r w) (M.cuts:Filter UVIndex)
      (𝓝 (RG17.locatedRef L d r (input L d H r (RG17.Report.thresholdFactor R.family M.beta (L.level r)) w))) := by
  let m := L.level r
  let T := R.family.path.levels.clock
  have bpos : 0<M.beta m := (div_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed m)) (by norm_num : (0:ℝ)<2)).trans_le (M.band m).1
  have beta := M.measured m
  have running : Tendsto (fun z : UVIndex=>RG17.Report.coupling (fun j=>R.family.path.β z.1 z.2 j) m)
      (M.cuts:Filter UVIndex) (𝓝 (RG17.Report.coupling M.beta m)) :=
    (Real.continuous_sqrt.continuousAt.tendsto.comp beta).inv₀ (Real.sqrt_pos.2 bpos).ne'
  have ht : Tendsto (fun z : UVIndex=>RG17.Report.thresholdFactor R.family (fun j=>R.family.path.β z.1 z.2 j) m)
      (M.cuts:Filter UVIndex) (𝓝 (RG17.Report.thresholdFactor R.family M.beta m)) :=
    tendsto_const_nhds.div running (inv_ne_zero (Real.sqrt_pos.2 bpos).ne')
  have graded : Continuous (fun t : ℝ=>(R.family.labels.level d).scaled t w) := by
    apply continuous_pi;intro i
    simp_rw [Labels.Frame.scaled_apply];fun_prop
  have coef : Continuous (fun _ : ℝ=>(((r/R.family.S.a (L.level r))^H : ℝ):ℂ)) := continuous_const
  have comp : Continuous (fun t : ℝ=>input L d H r t w) :=
    coef.smul ((L.shift d r).symm.continuous_of_finiteDimensional.comp graded)
  have h := RG17.tendsRef L M.prior (comp.continuousAt.tendsto.comp ht) admitted
  change Tendsto (fun z=>cut L d H r w z) _ _
  simp_rw [at_cut]
  exact h

end YM.Integration.WilsonOrdinaryThermalSource
