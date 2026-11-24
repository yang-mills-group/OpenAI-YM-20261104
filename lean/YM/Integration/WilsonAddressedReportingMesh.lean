import YM.Integration.WilsonAddressedReportingScale

/-! Both sides of the reporter mesh are paid by the same measured receipt. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedReportingMesh
open Function Filter Set RG Wilson Extraction Table Spec Trace.Pilot GapsContact.Seams
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFourPool WilsonAddressedReportingScale
open scoped Topology
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) (l : Ultrafilter (ℕ×ℕ))
local notation "C₀" => R.family

theorem priced (simple : G.Simple) (g : ℝ → ℝ) (hg : Coupling G g) (T : ℕ) :
    ∃ U : ℝ, 0<U ∧ ∀ᶠ r in trail, ∀ t ≤ T, ∀ j m d,
      Receipt F l (radius T r) j m d (dock (radius T r)^t) →
      (C₀).S.a j/r ≤ (g r)^2 ∧ (r/(C₀).S.a j)*(g r)^(2*(2*T+2)) ≤ U := by
  obtain ⟨lo,u,lp,up,temperature⟩ := currency simple g hg
  have ht : Tendsto dock trail atTop := tendsto_atTop_add_const_left _ _
    (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  have cp : 0 < overhead T := by unfold overhead; positivity
  refine ⟨overhead T*u^(2*T+2),mul_pos cp (pow_pos (zero_lt_one.trans_le up) _),?_⟩
  filter_upwards [self_mem_nhdsWithin,ht.eventually_ge_atTop 1,ht.eventually_ge_atTop (overhead T/lo),
    growth T,temperature] with r rp dr large growth sale t order j m d posted
  let D := dock r
  let a := (C₀).S.a j
  have dp : 0 < D := zero_lt_one.trans_le dr
  have ap : 0 < a := (C₀).S.a_pos _
  have pp : 0 ≤ radius T r := (div_pos rp (pow_pos dp _)).le
  have seen := growth t order
  have top : a ≤ radius T r*(overhead T*D^T) := ((C₀).S.strictAnti.antitone posted.fore).trans
    (posted.front.le.trans (mul_le_mul_of_nonneg_left seen pp))
  have low : radius T r ≤ (overhead T*D^T)*a := posted.breadth.le.trans (mul_le_mul_of_nonneg_right seen ap.le)
  have cb : overhead T ≤ lo*D := by simpa only [D,mul_comm lo] using (div_le_iff₀ lp).mp large
  constructor
  · apply (div_le_iff₀ rp).mpr
    apply le_of_mul_le_mul_right _ (pow_pos dp 2)
    calc
      a*D^2 ≤ (radius T r*(overhead T*D^T))*D^2 := mul_le_mul_of_nonneg_right top (sq_nonneg _)
      _ = r*overhead T := by dsimp only [radius,D];rw [pow_add];field_simp [dp.ne']
      _ ≤ r*(lo*D) := mul_le_mul_of_nonneg_left cb rp.le
      _ ≤ r*((D*(g r)^2)*D) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right sale.2.2.1 dp.le) rp.le
      _ = (g r)^2*r*D^2 := by ring
  · have raw : r/a ≤ overhead T*D^(2*T+2) := by
      apply (div_le_iff₀ ap).mpr
      have l : r ≤ (overhead T*D^T*a)*D^(T+2) := (div_le_iff₀ (pow_pos dp _)).mp low
      exact l.trans_eq (by rw [show 2*T+2=T+(T+2) by omega,pow_add]; ring)
    calc
      _ ≤ (overhead T*D^(2*T+2))*(g r)^(2*(2*T+2)) := mul_le_mul_of_nonneg_right raw (pow_nonneg sale.1.le _)
      _ = overhead T*(D*(g r)^2)^(2*T+2) := by rw [mul_pow,pow_mul];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg dp.le (sq_nonneg _)) sale.2.2.2 _) cp.le

end YM.Integration.WilsonAddressedReportingMesh
end
