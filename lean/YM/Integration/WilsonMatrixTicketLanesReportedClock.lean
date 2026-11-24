import YM.Integration.WilsonPhysicalExteriorMeshStops
import YM.Integration.WilsonMeasuredWindow

/-! The original reporting and forward mesh stops buy the physical aperture on the selected calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedClock
open Filter Real Lattice RG RG16 PhysicalNext.Repeat.Legato
open WilsonPhysicalExteriorMeshStops WilsonMeasuredWindow
open scoped Topology Classical
variable {G : Gauge} (R : Run G) (simple : G.Simple) (B : ℕ)
local notation "m" => stop R.family.path.levels simple B
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "s" => R.family.S.scale
local notation "a" => R.family.S.a

/-- The reporting UV date is chosen from the original calendar before the final cutoff and period. -/
abbrev upper (c r : ℝ) := ultraviolet R.family c (m r)
local notation "U" => upper R simple B

/-- The forward least-stop crosses this actual clock threshold. -/
private theorem earns (c r : ℝ) : s (m r)+(Λ (m r))^c ≤ s (U c r) := by
  unfold upper ultraviolet crossing
  exact Nat.find_spec (p:=fun j : ℕ => s (m r)+(Λ (m r))^c ≤ s j) _

theorem before (c r : ℝ) : m r ≤ U c r := by
  by_contra! reverse
  have old := (OPE.scale_mono R.family.S).monotone reverse.le
  linarith only [earns R simple B c r,old,Real.rpow_pos_of_pos (RG16.Literal.lambda_pos R.family (m r)) c]

/-- At a positive physical radius the reported logarithmic aperture already exceeds Λᶜ. -/
theorem height (c r : ℝ) (hr : 0 < r) : (Λ (m r))^c ≤ log (r/a (U c r)) := by
  have simpleFit : a (m r) ≤ r := calc
    _ ≤ a (m r) * (WilsonMeasuredAdmission.mast R.family.path.levels (m r))^B :=
      le_mul_of_one_le_right (R.family.S.a_pos _).le (one_le_pow₀ (WilsonMeasuredAdmission.mast_gt_one _ _).le)
    _ ≤ _ := stop_spec R.family.path.levels simple B hr
  have distance : s (U c r)-s (m r) = log (a (m r)/a (U c r)) := by
    rw [Schedule.scale,Schedule.scale,log_inv,log_inv,log_div (R.family.S.a_pos _).ne' (R.family.S.a_pos _).ne']
    ring
  calc (Λ (m r))^c ≤ s (U c r)-s (m r) := by linarith only [earns R simple B c r]
    _ = _ := distance
    _ ≤ _ := log_le_log (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _))
      ((div_le_div_iff_of_pos_right (R.family.S.a_pos _)).mpr simpleFit)

/-- The arbitrary total-function regularization affects only the portion of the radius filter before the physical asymptotic. -/
def aperture (c η r : ℝ) := max (max 0 (log (4/η))) (log (r/a (U c r)))

private theorem high (hB : 0 < B) {c : ℝ} (hc : 1 < c) :
    Tendsto (fun r : ℝ => log (r/a (U c r))) (𝓝[>] (0:ℝ)) atTop := by
  have stopGoing := stop_tendsto R.family.path.levels simple B hB
  have growing := (tendsto_rpow_atTop (zero_lt_one.trans hc)).comp ((RG16.Literal.lambda_leads R.family simple).comp stopGoing)
  apply tendsto_atTop.mpr
  intro x
  filter_upwards [growing.eventually_ge_atTop x, self_mem_nhdsWithin] with r tall pos
  exact tall.trans (height R simple B c r pos)

/-- All three true clock facts hold at the same radius on the original positive-radius filter. -/
theorem actual (hB : 0 < B) {c : ℝ} (hc : 1 < c) (η : ℝ) (b : ℕ) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), b ≤ U c r ∧ aperture R simple B c η r = log (r/a (U c r)) ∧
      exp (aperture R simple B c η r) = r / a (U c r) ∧ (Λ (m r))^c ≤ aperture R simple B c η r := by
  filter_upwards [(stop_tendsto R.family.path.levels simple B hB).eventually_ge_atTop b,
    (high R simple B hB hc).eventually_ge_atTop (max 0 (log (4/η))),self_mem_nhdsWithin] with r past grown pos
  have real : aperture R simple B c η r = log (r/a (U c r)) := max_eq_right grown
  exact ⟨past.trans (before R simple B c r),real,real ▸ Real.exp_log (div_pos pos (R.family.S.a_pos _)),
    real ▸ height R simple B c r pos⟩

theorem parameters (hB : 0 < B) {c η : ℝ} (hc : 1 < c) (hη : 0 < η) :
    (∀ r, 0 ≤ aperture R simple B c η r) ∧ Tendsto (aperture R simple B c η) (𝓝[>] (0:ℝ)) atTop ∧
    ∀ r, 4 * exp (-(aperture R simple B c η r)) ≤ η := by
  refine ⟨fun _ => (le_max_left _ _).trans (le_max_left _ _),
    tendsto_atTop_mono (fun r => le_max_right _ _) (high R simple B hB hc),?_⟩
  intro r
  have h : log (4/η) ≤ aperture R simple B c η r := (le_max_right _ _).trans (le_max_left _ _)
  have e := Real.exp_le_exp.mpr (neg_le_neg h)
  rw [Real.exp_neg (log _),Real.exp_log (div_pos (by norm_num) hη),inv_div] at e
  linarith only [e]

end YM.Integration.WilsonMatrixTicketLanesReportedClock
