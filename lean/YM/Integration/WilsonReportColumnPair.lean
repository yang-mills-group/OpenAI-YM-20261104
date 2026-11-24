import YM.Integration.WilsonReportColumnCut

/-! Truncate the full signed two-field regular moment on its actual
normalized coarse Wilson law. No estimate on a replacement denominator enters. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportColumnPair
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Cells
open Next.Rank OPE OPE.Orbits OPE.Strobe OPE.Strobe.Vista26 RG12 RG17 RG17.Panoramic SharpGram
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol OPE.Strobe.Panoramic Push.GridApprox
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportColumnCut
open scoped Topology Classical BigOperators
universe u
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book} {F:Spec.Final R.family f S}

private theorem two (x y X Y : ℂ) {A t : ℝ} (hA : 0 ≤ A) (ht : 0 ≤ t)
    (hy : ‖y‖ ≤ 3*A) (hX : ‖X‖ ≤ 5*A) (dX : ‖x-X‖ ≤ 2*(t*A)) (dY : ‖y-Y‖ ≤ 2*(t*A)) :
    ‖x*y-X*Y‖ ≤ 16*(t*A^2) := by
  have split : x*y-X*Y=(x-X)*y+X*(y-Y) := by ring
  calc
    _ ≤ ‖(x-X)*y‖+‖X*(y-Y)‖ := split ▸ norm_add_le _ _
    _ = ‖x-X‖*‖y‖+‖X‖*‖y-Y‖ := by rw [norm_mul,norm_mul]
    _ ≤ (2*(t*A))*(3*A)+(5*A)*(2*(t*A)) := add_le_add
      (mul_le_mul dX hy (norm_nonneg _) (by positivity)) (mul_le_mul hX dY (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem retained (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (funding : FundedOriginalProperties.{u} hG δ W) (subsidy : WilsonReportColumnSubsidy.Eligible R.kit)
    (L : Layout F) (E : OPE.Services R.family f S) (r : ℝ) {d k N p t h : ℕ} (w : Fin 2→R.family.label d)
    (grade : R.family.ref d ≤ L.level r) (zero : R.family.ref 0 < k) (deep : L.level r ≤ k) (cut : k < N)
    (zoom : R.family.S.a (L.level r)/R.family.S.a k ≤ R.family.path.levels.clock.hatBeta k^t)
    (price : ∀ j,mass R.family d (L.shift d r (w j)) ≤ R.family.path.levels.clock.hatBeta (L.level r)^h)
    (x : Fin 2→Site (R.family.side k p)) :
    let C := R.family; let β := C.path.levels.clock.hatBeta k
    let B := (C.path.levels.budget k).B; let μ := Therm.scene C.path N p k
    let M (j : Fin 2) := regularRead C d k N p (atRef L d r (N,p) (w j)) (x j)
    let Q (j : Fin 2) := localized L r d k N p (w j) (x j)
    (∀ j,Interior (window (x j) (omen C d k B)) (Q j)) ∧
    Integrable (fun U=>∏ j,Q j U) μ ∧
    ‖(∫ U,∏ j,M j U ∂μ) - ∫ U,∏ j,Q j U ∂μ‖ ≤
      16*(Real.exp (-2*(B:ℝ))*β^((1+t*(d+1)+h)*2)) := by
  let C := R.family
  let β := C.path.levels.clock.hatBeta k
  let B := (C.path.levels.budget k).B
  let μ := Therm.scene C.path N p k
  letI : IsProbabilityMeasure μ := Therm.probability R.makes.wilson cut.le
  let M (j : Fin 2) := regularRead C d k N p (atRef L d r (N,p) (w j)) (x j)
  let Q (j : Fin 2) := localized L r d k N p (w j) (x j)
  let A := β^(1+t*(d+1)+h)
  let amp := Real.exp (-2*(B:ℝ))
  have b0 : 0 ≤ β := zero_le_one.trans (C.path.levels.fits.delayed k).le
  have a0 : 0 ≤ A := pow_nonneg b0 _
  have left (j : Fin 2) := field hG W funding subsidy L E r (w j) grade zero deep cut zoom (x j)
  have mono := WilsonStartup.Timing.hat_mono C.path.levels (Gauge.slopeConstant_pos hG).le deep
  have size (j : Fin 2) : β^(1+t*(d+1))*mass C d (L.shift d r (w j)) ≤ A := by
    apply (mul_le_mul_of_nonneg_left ((price j).trans (pow_le_pow_left₀
      (zero_le_one.trans (C.path.levels.fits.delayed _).le) mono _)) (pow_nonneg b0 _)).trans_eq
    exact (pow_add ..).symm
  have M₀ := ((left 0).2.1.mulC (left 1).2.1).integrableC μ
  have Q₀ := ((left 0).2.2.1.mulC (left 1).2.2.1).integrableC μ
  dsimp only
  refine ⟨fun j=>(left j).1,?_,?_⟩
  · simpa only [Fin.prod_univ_two] using Q₀
  have measured (U) : ‖M 0 U*M 1 U-Q 0 U*Q 1 U‖ ≤ 16*(amp*A^2) := by
    apply two _ _ _ _ a0 (Real.exp_nonneg _)
    · exact ((left 1).2.2.2 U).1.trans (mul_le_mul_of_nonneg_left (size 1) (by norm_num))
    · exact ((left 0).2.2.2 U).2.2.trans (mul_le_mul_of_nonneg_left (size 0) (by norm_num))
    · exact ((left 0).2.2.2 U).2.1.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (size 0) (Real.exp_nonneg _)) (by norm_num))
    · exact ((left 1).2.2.2 U).2.1.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (size 1) (Real.exp_nonneg _)) (by norm_num))
  have h := norm_integral_le_of_norm_le_const (μ:=μ) (Eventually.of_forall measured)
  rw [probReal_univ,mul_one] at h
  simp only [Fin.prod_univ_two]
  rw [←integral_sub M₀ Q₀,pow_mul]
  exact h

end YM.Integration.WilsonReportColumnPair
end

