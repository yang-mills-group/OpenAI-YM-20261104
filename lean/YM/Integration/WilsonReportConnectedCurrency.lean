import YM.Integration.WilsonPhysicalCutoffCurrency

/-! An original finite early-report price can absorb every fixed polynomial
in the true temperature at the physical stop, uniformly in the fine cutoff
and the torus, before the continuum coupling order is read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportConnectedCurrency
open Filter Set Next.Rank Trace.Pilot Pert.Asymptotics PhysicalNext.Repeat.Legato
open scoped Topology
variable {G : Gauge} (R : Run G) (hG : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0<B) (g : ℝ→ℝ) (hg : Coupling G g)

include pace hB hg in
theorem absorb (D q : ℕ) {K ε : ℝ} (hK : 0<K) (hε : 0<ε) :
    let m := WilsonMeasuredWindow.stop R.family.path.levels hG B
    let E := q+D+1
    ∀ᶠ r in 𝓝[>] (0:ℝ),∀ N p : ℕ,m r≤N →
    let z := regulatorRun R.family N p (m r)
    let fee := (8:ℝ)^E*z^(2*E)
    fee≤1 ∧ K*fee*R.family.path.levels.clock.hatBeta (m r)^D ≤ ε*(g r)^q := by
  let m := WilsonMeasuredWindow.stop R.family.path.levels hG B
  let E := q+D+1
  let A := K*(8:ℝ)^E*2^(2*E)
  let C := A*2^D
  have ap : 0<A := by dsimp [A]; positivity
  have cp : 0<C := by dsimp [C]; positivity
  have drop := Coupling.conforms hG hg
  have temperature := WilsonPhysicalCutoffCurrency.temperature R hG pace hB g hg
  have prices := WilsonPhysicalCutoffCurrency.band R hG pace hB g hg
  dsimp only
  filter_upwards [hg.positive,prices,
    temperature.eventually (gt_mem_nhds (show (1:ℝ)<2 by norm_num)),
    drop.eventually (gt_mem_nhds (show (0:ℝ)<1/8 by norm_num)),
    drop.eventually (gt_mem_nhds (div_pos hε cp))] with r gp band unit small tiny
  intro N p visible
  let β := R.family.path.levels.clock.hatBeta (m r)
  let z := regulatorRun R.family N p (m r)
  have bz : 0≤β := zero_le_one.trans (R.family.path.levels.fits.delayed _).le
  have zp : 0≤z := (RG16.Literal.g_pos R.makes visible).le
  have upper : z≤2*g r := (band N p visible).2
  have one : g r≤1 := by linarith only [small]
  have zsmall : z≤1/4 := by linarith only [upper,small]
  have mass : β*(g r)^2≤2 := unit.le
  have fee : C*g r≤ε := by simpa only [mul_comm] using ((lt_div_iff₀ cp).mp tiny).le
  change (8:ℝ)^E*z^(2*E)≤1 ∧ K*(8^E*z^(2*E))*β^D≤ε*(g r)^q
  constructor
  · rw [pow_mul,←mul_pow]
    have square := pow_le_pow_left₀ zp zsmall 2
    exact pow_le_one₀ (by positivity) (by nlinarith only [square])
  have powers : (g r)^(2*E)=(g r)^(2*D)*(g r)^(2*(q+1)) := by
    rw [←pow_add]
    congr 1
    dsimp only [E]
    omega
  calc
    _ ≤ K*(8^E*(2*g r)^(2*E))*β^D := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zp upper _) (by positivity)) hK.le)
      (pow_nonneg bz _)
    _ = A*(β*(g r)^2)^D*(g r)^(2*(q+1)) := by
      rw [mul_pow (2:ℝ) (g r),powers,mul_pow β ((g r)^2),←pow_mul]
      dsimp only [A]
      ring
    _ ≤ C*(g r)^(2*(q+1)) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg bz (sq_nonneg _)) mass D) ap.le) (pow_nonneg gp.le _)
    _ ≤ C*(g r)^(q+1) := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one gp.le one (by omega)) cp.le
    _ = (C*g r)*(g r)^q := by rw [pow_succ]; ring
    _ ≤ ε*(g r)^q := mul_le_mul_of_nonneg_right fee (pow_nonneg gp.le _)

end YM.Integration.WilsonReportConnectedCurrency
end

