import YM.Integration.WilsonOrdinaryReportDeposit

/-! Combined engineering and angular charge for the actual independently
named primary deposited at the reporting stop. This estimate holds before
the entire fine ultraviolet tail and costs any prescribed positive power. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryReportStock
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
variable {W : Type} (Q : MS.Land.Prescription B) (y : ℝ) (p : W→MS.Rake.Label B)


open WilsonOrdinaryReportDeposit Real

private theorem combined (A : RG.Levels G) (hG : G.Simple) (k j : ℕ) (η : ℝ) (positive : 0<η) :
    ∀ᶠ m in atTop,(RG16.Lambda A m)^k*(A.clock.monitor m)^j≤(A.clock.hatBeta m)^η := by
  let h := k+j
  let c := η/((h:ℝ)+1)
  have hc : 0<c := div_pos positive (by positivity)
  have grows := Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate A hG)
  have again := Real.tendsto_log_atTop.comp grows
  have lower := grows.eventually_ge_atTop (2:ℝ)
  have large := again.eventually_ge_atTop (2:ℝ)
  have small := grows.eventually ((Real.isLittleO_pow_log_id_atTop (n:=2)).bound hc)
  filter_upwards [lower,large,small] with m hm hl hs
  let B := A.clock.hatBeta m
  let l := Real.log B
  let a := Real.log l
  have βpos : 0<B := zero_lt_one.trans (A.fits.delayed m)
  change 2≤l at hm
  change 2≤a at hl
  change ‖a^2‖≤c*‖l‖ at hs
  have lpos : 0<l := by linarith only [hm]
  have apos : 0≤a := by linarith only [hl]
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg a),abs_of_nonneg lpos.le] at hs
  have ceiling : 2+l≤Real.exp (a^2) := by
    calc
      _ ≤ l*l := by nlinarith [mul_nonneg (sub_nonneg.mpr hm) (by linarith : 0≤l+1)]
      _ = Real.exp (a+a) := by rw [Real.exp_add,Real.exp_log lpos]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hl) apos])
  have run : (h:ℝ)*a^2 ≤ l*η := calc
    _ ≤ ((h:ℝ)+1)*a^2 := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg _)
    _ ≤ ((h:ℝ)+1)*(c*l) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by dsimp only [c]; field_simp
  change (2+l)^k*(Real.exp (a^2))^j≤B^η
  calc
    _ ≤ (Real.exp (a^2))^k*(Real.exp (a^2))^j := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by linarith only [hm]) ceiling _) (by positivity)
    _ = (Real.exp (a^2))^h := (pow_add _ _ _).symm
    _ ≤ _ := by rw [←Real.exp_nat_mul,Real.rpow_def_of_pos βpos];exact Real.exp_le_exp.mpr run

/-- The original selected stop pays arbitrarily small temperature power
for the real relative reporting cost, before *any* independently chosen
input coefficient or actual ultraviolet period/cutoff. -/
theorem original (hG : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit) {B₀ : ℕ}
    (hB : 0<B₀) (stopped : L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B₀)
    (H : ℕ) (η : ℝ) (positive : 0<η) :
    ∀ᶠ r in trail, ∀ v : R.family.label d,
      RG12.mass R.family d (L.shift d r (input L d H r (R.family.path.levels.clock.monitor (L.level r)) v)) ≤
        (R.family.path.levels.clock.hatBeta (L.level r))^η * RG12.mass R.family d v := by
  let A := R.family.path.levels
  let m := WilsonMeasuredWindow.stop A hG B₀
  let j := slots d (R.family.labels.level d)
  obtain ⟨future,window⟩ := WilsonFundedMeasuredWindow.all_radii R slow hG hB
  have stock := future.eventually (combined A hG ((B₀+1)*H) j η positive)
  have positive_r : ∀ᶠ r in trail,0<r := self_mem_nhdsWithin
  filter_upwards [stock,positive_r,(gt_mem_nhds (R.family.S.a_pos 0)).filter_mono nhdsWithin_le_nhds] with r hr hp hs v
  have win := (window r hp hs.le).2
  have one : 1≤A.clock.monitor (L.level r) := Real.one_le_exp (sq_nonneg _)
  have bought := reserve L d H r (A.clock.monitor (L.level r)) hp.le one v
  apply bought.trans
  apply mul_le_mul_of_nonneg_right _ (RG12.mass_nonneg ..)
  rw [stopped]
  have ratio := pow_le_pow_left₀ (div_nonneg hp.le (R.family.S.a_pos _).le) win H
  have cap := mul_le_mul_of_nonneg_right ratio (pow_nonneg (show 0≤A.clock.monitor (m r) from (Real.exp_pos _).le) j)
  rw [←pow_mul] at cap
  exact cap.trans hr

/-- In particular this applies to the real installed independently chosen
MS fee and named source symbol, not simply to a postulated ticket. -/
theorem filed (hG : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit) {B₀ : ℕ}
    (hB : 0<B₀) (stopped : L.level=WilsonMeasuredWindow.stop R.family.path.levels hG B₀)
    (i : W) (n : ℕ) (v : Glyph B (p i).h) (η : ℝ) (positive : 0<η) :
    ∀ᶠ r in trail,
      RG12.mass R.family v.size (L.shift v.size r (mode L Q y p i n r v)) ≤
        (R.family.path.levels.clock.hatBeta (L.level r))^η *
          RG12.mass R.family v.size (PowerSeries.coeff n (bore p Q y i v) • Lobby.γ (basisR R) (owner v)) :=
  (original L v.size hG slow hB stopped (p i).h η positive).mono fun _ hr=>hr _

end YM.Integration.WilsonOrdinaryReportStock
