import YM.Integration.WilsonReportingPlaquetteWindows
import YM.Integration.WilsonCoefficientPreparation
import YM.Next.RANK.Station

/-! The compact reporting-window estimate for the actual registered basis
fields. The microscopic order normalization uses the threshold in the
original representation purchased by this physical cutoff and period. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonReportingRegisteredWindows
open Function Filter Finset MeasureTheory Lattice RG Wilson Source RG05Readout.Pulse
open PhysicalNext.Repeat.Legato RGComparison.Core16.Spool OPE.Therm
open WilsonReportingPlaquetteWindows
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} (R : Run G) {V : Type} [Fintype V] [DecidableEq V] (D : V → ℕ)

abbrev rows := (i : V) → (R.family.labels.level (D i)).Index

private def order (a : rows R D) := ∑ i, ((R.family.labels.level (D i)).grades (a i)).2

private theorem inverse_threshold {N k : ℕ} (per : ℕ) (live : k ≤ N) :
    (R.family.path.rep N per k).p.threshold⁻¹ ≤ R.family.path.levels.clock.hatBeta k := by
  let X := R.family.path.levels.clock.hatBeta k
  have one : 1 ≤ X := (R.family.path.levels.fits.delayed k).le
  have xp := zero_lt_one.trans_le one
  have receipt : (R.family.path.rep N per k).p = R.family.path.levels.budget k :=
    (R.makes.wilson.represents N per k live).vac
  rw [receipt]
  change ((Real.sqrt X)⁻¹ * Real.exp ((Real.log (Real.log X))^2))⁻¹ ≤ X
  have fuel : 1 ≤ Real.exp ((Real.log (Real.log X))^2) := Real.one_le_exp (sq_nonneg _)
  have root := Real.sqrt_pos.mpr xp
  calc
    _ ≤ ((Real.sqrt X)⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr root)
      (le_mul_of_one_le_right (inv_nonneg.mpr root.le) fuel)
    _ = _ := inv_inv _
    _ ≤ X := (Real.sqrt_le_left xp.le).mpr (by nlinarith only [mul_nonneg xp.le (sub_nonneg.mpr one)])

/-- Signed filed basis coefficient, including its original grade normalization. -/
def price (k N per : ℕ) (y : (i : V) → R.family.label (D i)) (a : rows R D) : ℂ :=
  (∏ i, y i (a i)) * (((R.family.path.rep N per k).p.threshold⁻¹ : ℝ) : ℂ)^(order R D a)

/-- For an arbitrary fixed compact jointly smooth signed profile, all its
original basis positions and grade normalizations are already paid. Later
regulators, periods, component coefficients, translations and dilation of
the test are selected after the reporting date. -/
theorem tested (stoves : Poetry R.family.path.levels) (simple : G.Simple)
    (φ : Wave V) (compact : HasCompactSupport φ.val) (d s e q : ℕ) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N per, k ≤ N → ∀ t : ℕ, (t:ℝ) ≤ R.family.path.levels.clock.hatBeta k^s →
      ∀ (y : (i : V) → R.family.label (D i)),
      (∀ i b, ‖y i b‖ ≤ R.family.path.levels.clock.hatBeta k^e) →
      ∀ (r : ℝ) (ξ : Cloud V)
        (cells : placements (V:=V) R.family k per t × rows R D → V → Finset (Face (Per (R.family.side k per)))),
      (∀ a i, ((cells a i).card:ℝ) ≤ R.family.path.levels.clock.hatBeta k^d) →
      ∫ U, ‖∑ a : placements (V:=V) R.family k per t × rows R D,
        (⋃ i, (House.chilly (cells a i) (cool R.family.path.levels k))ᶜ).indicator
          (fun Z => (φ.val (fun i => r⁻¹ • (R.family.S.place (a.1.val i) - ξ i)) *
            price R D k N per y a.2) *
            ∏ i, (R.family.localSection (D i)).places (Pi.single (a.2 i) 1) (a.1.val i) Z) U‖
        ∂scene R.family.path N per k ≤ ε * Pert.Asymptotics.regulatorRun R.family N per k^q := by
  let H := Finset.univ.sup (order R D)
  let J (a : rows R D) (i : V) : Lamp G :=
    investment (R.makes.sections (D i)) (CoefficientBridge.run_valuation R (D i)) (a i)
  obtain ⟨B,hB⟩ := compact.exists_bound_of_continuousOn
    ((show ContDiff ℝ ∞ φ.val from φ.property).continuous.continuousOn)
  have bound (x : Cloud V) : ‖φ.val x‖ ≤ max 0 B := by
    by_cases hx : x ∈ tsupport φ.val
    · exact (hB x hx).trans (le_max_right ..)
    · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]; exact le_max_left ..
  let n := Fintype.card V
  filter_upwards [(Next.Rank.Station.hat_rate R.family.path.levels simple).eventually_ge_atTop (max 0 B),
    WilsonReportingPlaquetteWindows.original R.family R.makes stoves simple J d s (1+(e*n+H)) q ep]
    with k covers openWindow
  intro N per live t width y weights r ξ cells size
  let X := R.family.path.levels.clock.hatBeta k
  have one : 1 ≤ X := (R.family.path.levels.fits.delayed k).le
  have xp := zero_lt_one.trans_le one
  let θ := (R.family.path.rep N per k).p.threshold
  have positive : 0 < θ := (R.family.path.rep N per k).p.threshold_pos
  let w (a : placements (V:=V) R.family k per t × rows R D) :=
    φ.val (fun i => r⁻¹ • (R.family.S.place (a.1.val i) - ξ i)) * price R D k N per y a.2
  have paid (a : placements (V:=V) R.family k per t × rows R D) : ‖w a‖ ≤ X^(1+(e*n+H)) := by
    have each : ∏ i, ‖y i (a.2 i)‖ ≤ X^(e*n) := by
      rw [pow_mul]
      simpa only [Finset.prod_const,card_univ,n] using
        (Finset.prod_le_prod (s:=Finset.univ) (fun i _ => norm_nonneg (y i (a.2 i))) (fun i _ => weights i (a.2 i)))
    have powers : θ⁻¹^(order R D a.2) ≤ X^H := by
      apply (pow_le_pow_left₀ (inv_nonneg.mpr positive.le) (inverse_threshold R per live) _).trans
      exact pow_le_pow_right₀ one (Finset.le_sup (s:=Finset.univ) (f:=order R D) (Finset.mem_univ a.2))
    change ‖_ * ((_ : ℂ) * ((θ⁻¹ : ℝ) : ℂ)^_)‖ ≤ _
    rw [norm_mul,norm_mul,norm_prod,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr positive)]
    rw [pow_add,pow_one,pow_add]
    exact mul_le_mul ((bound _).trans covers) (mul_le_mul each powers (pow_nonneg (inv_nonneg.mpr positive.le) _) (pow_nonneg xp.le _))
      (mul_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (pow_nonneg (inv_nonneg.mpr positive.le) _)) xp.le
  have purchased := openWindow N per k live (le_refl k) t width w (fun a => a.1.val) cells paid size
  have genuine (a : placements (V:=V) R.family k per t × rows R D) (Z) :
      tally (J a.2) a.1.val Z = ∏ i, (R.family.localSection (D i)).places
        (Pi.single (a.2 i) 1) (a.1.val i) Z := by
    rfl
  simpa only [actualTransport_base R.family R.makes live,genuine,w] using purchased

end YM.Integration.WilsonReportingRegisteredWindows
