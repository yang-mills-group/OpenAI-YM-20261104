import YM.Integration.WilsonOrdinarySignedWindow
import YM.Integration.WilsonReportUnmaskedMoments
import YM.Integration.WilsonReportFittedCurrency
import YM.Integration.WilsonReportFittedPositions

/-! Pay the primary alarm in the actual signed ordinary exterior test, to any physical
power, on its own previously fixed left labels and its one common reflected right label.
The residual field is the actual fitted polynomial plus all its retained signed rows. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryRetainedWindow
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
variable (L : Layout F) (g : ℝ→ℝ) (d : ℕ)
set_option quotPrecheck false
local notation "D" => (Bel R.family.book).Field d

def openedPair (r : ℝ) (N p : ℕ) (w : Fin 2 → R.family.label d) : ℂ :=
  ∫ U, ∏ j, opened R.family (N:=N) (atRef L d r (N,p) (w j)) (cells R (berth R 28 (L.level r)) p r detectors j) U
    ∂(OPE.Therm.scene R.family.path N p (berth R 28 (L.level r)))

/-- This bound is bought before all earlier representatives, all sites in the scheduled
pair, all later cutoffs and all periods. The date is the fixed quadratic berth. -/
theorem prior_pair (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (funding : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) (E : OPE.Services R.family f S)
    {u : Filter UVIndex} {Q : Lenses.Mantle F u} (hQ : Pegs Q L)
    (placed : L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B)
    (scene : Pier.Scene.ScenePlan R F L) (hg : Coupling G g) (e q : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ r in trail,∀ w : Fin 2→R.family.label d,
    (∀ j,mass R.family d (L.shift d r (w j))≤R.family.path.levels.clock.hatBeta (L.level r)^e) →
    ∀ N p : ℕ,(berth R 28 (L.level r))<N →
    ‖WilsonReportWindowMatrix.joint L d w r (berth R 28 (L.level r)) N p - openedPair L d r N p w‖ ≤ ε*(g r)^q := by
  let Dg := fun _ : Fin 2 => d
  let Γ : Census (Fin 2) := ⟨univ,mem_univ _,fun _=>mem_univ _,fun _ _ _=>mem_univ _⟩
  let a := 30*((∑ j,Dg j)+1)+e
  let factor := WilsonReportFittedCurrency.factor 2 a 3 q
  have positive : 0<factor := by dsimp only [factor,WilsonReportFittedCurrency.factor]; positivity
  let fee := ε/factor
  have hf : 0<fee := div_pos hε positive
  have product : fee*factor=ε := div_mul_cancel₀ ε positive.ne'
  have bought := WilsonReportUnmaskedMoments.physical hG W funding subsidy Dg (q+2*(a*3)) hf
  obtain ⟨stage,moment⟩ := eventually_atTop.1 bought
  have temp := WilsonPhysicalCutoffCurrency.temperature R hG pace hB g hg
  have warm := temp.eventually (lt_mem_nhds (by norm_num : (1/2:ℝ)<1))
  rw [←placed] at warm
  have flags := scene.allFlags Γ Dg 3 1 1 e (by decide)
  filter_upwards [flags,hQ.level.growing.eventually_ge_atTop stage,
    hQ.level.growing.eventually_ge_atTop (R.family.ref d),warm,hg.positive] with r permissions late grade fit gp
  obtain ⟨deep,_,context,_,_⟩ := permissions
  intro w mass N p hk
  let V (j : Fin 2) := atRef L d r (N,p) (w j)
  let x := cells R (berth R 28 (L.level r)) p r detectors
  let A := 1+∑ j,Spindle.paid R.family d (berth R 28 (L.level r)) N p (V j)
  let z := regulatorRun R.family N p (berth R 28 (L.level r))
  have geom : R.family.S.a (L.level r)/R.family.S.a (berth R 28 (L.level r)) ≤ R.family.path.levels.clock.hatBeta (berth R 28 (L.level r))^30 := context.zoom
  have billed := WilsonReportFittedCurrency.at_fields (p:=p) hG L E Dg w gp fit.le deep.le hk.le
    (fun _ => grade) geom mass 3 q
  have spend : fee*A^3*z^(q+2*(a*3)) ≤ ε*(g r)^q :=
    (mul_assoc fee _ _).le.trans ((mul_le_mul_of_nonneg_left billed hf.le).trans_eq
      ((mul_assoc fee factor ((g r)^q)).symm.trans (congrArg (· * (g r)^q) product)))
  have raw := moment (berth R 28 (L.level r)) (late.trans deep.le) N p hk V x univ
  exact raw.trans spend

def retainedCut {J : ℝ→tower S} {A B : Module.End ℂ D} {e : ℕ} {r : ℝ}
    (P : WindowRows F J L g d A B e r) (N p : ℕ) (i j : Handle F d) : ℝ :=
  signed (g r) (fun h => (openedPair L d r N p ![P.left h i,P.right j]).re)

/-- On the literal signed four-term test the true primary alarm is smaller than
εg(r)^q for every q, uniformly after the measured reporting threshold. -/
theorem signed_price (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (funding : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) (E : OPE.Services R.family f S)
    {u : Filter UVIndex} {Q : Lenses.Mantle F u} (hQ : Pegs Q L)
    (placed : L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B)
    (scene : Pier.Scene.ScenePlan R F L) (hg : Coupling G g) (e q : ℕ) {ε : ℝ} (hε : 0<ε)
    {J : ℝ→tower S} {A B : Module.End ℂ D} : ∀ᶠ r in trail,
    ∀ P : WindowRows F J L g d A B e r,∀ N p : ℕ,(berth R 28 (L.level r))<N → ∀ i j,
    |cut F J L g d P (N,p) i j-retainedCut L g d P N p i j| ≤ ε*(g r)^q := by
  have fourth : 0<ε/4 := by positivity
  have small := (Coupling.conforms hG hg).eventually (gt_mem_nhds (zero_lt_one : (0:ℝ)<1))
  filter_upwards [prior_pair L g d hG W funding subsidy pace hB E hQ placed scene hg e q fourth,
    hg.positive,small] with r price gp cap
  intro P N p hk i j
  have each (h : Fin 4) : |(WilsonReportWindowMatrix.joint L d ![P.left h i,P.right j] r (berth R 28 (L.level r)) N p).re -
      (openedPair L d r N p ![P.left h i,P.right j]).re| ≤ ε/4*(g r)^q := by
    have mass (z : Fin 2) : mass R.family d (L.shift d r (![P.left h i,P.right j] z)) ≤
        R.family.path.levels.clock.hatBeta (L.level r)^e := by
      fin_cases z
      · exact P.first_cost _ _
      · exact P.second_cost _
    exact (Complex.abs_re_le_norm _).trans (price _ mass N p hk)
  exact (WilsonOrdinaryFourGram.error gp.le cap.le (mul_nonneg fourth.le (pow_nonneg gp.le _))
    _ _ each).trans_eq (by ring)

end YM.Integration.WilsonOrdinaryRetainedWindow
