import YM.Integration.WilsonReportConnectedCurrency

/-! Price the physical inner mesh against the true numerical coupling, retaining
all the polynomial costs of the spectator moments on the same reporting stop. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportBerthCurrency
open Filter Set Trace.Pilot Pert.Asymptotics PhysicalNext.Repeat.Legato
open scoped Topology
variable {G : Gauge} (R : Run G) (hG : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) (g : ℝ→ℝ) (hg : Coupling G g)

include pace hB hg in
theorem purchased (D q : ℕ) {K ε c : ℝ} (hK : 0<K) (hε : 0<ε) (hc : 0<c) :
    let m := WilsonMeasuredWindow.stop R.family.path.levels hG B
    let o := D+q+1
    ∀ᶠ r in 𝓝[>] (0:ℝ),∀ b : ℕ,o≤b →
      let β := R.family.path.levels.clock.hatBeta (m r)
      (β^b)⁻¹ ≤ c ∧ K*β^D*(β^b)⁻¹ ≤ ε*(g r)^q := by
  let m := WilsonMeasuredWindow.stop R.family.path.levels hG B
  let C := K*2^(q+1)
  have cp : 0<C := by dsimp [C]; positivity
  have drop := Coupling.conforms hG hg
  have temperature := WilsonPhysicalCutoffCurrency.temperature R hG pace hB g hg
  dsimp only
  filter_upwards [hg.positive,temperature.eventually (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num)),
      drop.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
      drop.eventually (gt_mem_nhds (div_pos hε cp)),
      drop.eventually (gt_mem_nhds (show 0<c/2 by positivity))] with r gp unit small tiny near
  intro b hb
  let β := R.family.path.levels.clock.hatBeta (m r)
  have one : 1≤β := (R.family.path.levels.fits.delayed _).le
  have bp : 0<β := zero_lt_one.trans_le one
  have ht : 1/2 < β*(g r)^2 := unit
  have inv : β⁻¹ ≤ 2*(g r)^2 := by
    rw [←one_div,div_le_iff₀ bp]; nlinarith [ht]
  have hp (i j:ℕ) (hij:i≤j) : (β^j)⁻¹≤(β^i)⁻¹ :=
    inv_anti₀ (pow_pos bp _) (pow_le_pow_right₀ one hij)
  have g2 : (g r)^2 ≤ g r := by nlinarith [mul_nonneg gp.le (sub_nonneg.mpr small.le)]
  constructor
  · exact ((hp 1 b (by omega)).trans (by simpa using inv)).trans (by linarith)
  · calc
      K*β^D*(β^b)⁻¹ ≤ K*β^D*(β^(D+(q+1)))⁻¹ :=
        mul_le_mul_of_nonneg_left (hp _ _ (by omega)) (mul_nonneg hK.le (pow_nonneg bp.le _))
      _ = K*(β⁻¹)^(q+1) := by rw [pow_add, mul_inv, inv_pow]; field_simp
      _ ≤ K*(2*(g r)^2)^(q+1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr bp.le) inv _) hK.le
      _ = (C*(g r)^(q+2))*(g r)^q := by
        rw [mul_pow,←pow_mul,show 2*(q+1)=(q+2)+q by omega,pow_add]
        dsimp [C]; ring
      _ ≤ ε*(g r)^q := by
        have multiple : (g r)^(q+2) ≤ g r :=
          (pow_le_pow_of_le_one gp.le small.le (show 1≤q+2 by omega)).trans_eq (pow_one _)
        have bill := ((lt_div_iff₀ cp).mp tiny).le
        exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left multiple cp.le).trans (by linarith)) (pow_nonneg gp.le _)

end YM.Integration.WilsonReportBerthCurrency
