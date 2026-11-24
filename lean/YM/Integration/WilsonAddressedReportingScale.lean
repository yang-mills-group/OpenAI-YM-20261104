import YM.Integration.WilsonOriginalMicroscopicGuardedGridSchool
import YM.Integration.WilsonPhysicalCutoffCurrency

/-! A single polynomially resolving physical mesh for all subsequent test
orders. Shrink the election radius while keeping the submitted fields fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedReportingScale
open Filter Set Lattice Wilson RG Trace.Pilot GapsContact GapsContact.Stamps GapsContact.Seams
open scoped Topology

def radius (T : ℕ) (r : ℝ) := r/dock r^(T+2)
def overhead (T : ℕ) : ℝ := ((T:ℝ)+3)^T

theorem near (T : ℕ) : Tendsto (radius T) trail trail := by
  have stay : ∀ᶠ r : ℝ in trail, 0 < radius T r ∧ radius T r ≤ r := by
    filter_upwards [self_mem_nhdsWithin,(gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with r rp top
    have h : 1 ≤ dock r := dock_valid r ⟨rp,top.le⟩
    exact ⟨div_pos rp (pow_pos (zero_lt_one.trans_le h) _),div_le_self rp.le (one_le_pow₀ h)⟩
  exact tendsto_nhdsWithin_iff.mpr ⟨squeeze_zero' (stay.mono fun _ h=>h.1.le)
    (stay.mono fun _ h=>h.2) nhdsWithin_le_nhds,stay.mono fun _ h=>h.1⟩

theorem growth (T : ℕ) : ∀ᶠ r : ℝ in trail, ∀ t ≤ T,
    dock (radius T r)^t ≤ overhead T*dock r^T := by
  filter_upwards [self_mem_nhdsWithin,(gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with r rp top t small
  have h : 1 ≤ dock r := dock_valid r ⟨rp,top.le⟩
  have d0 := zero_lt_one.trans_le h
  have ρ : 0 < radius T r := div_pos rp (pow_pos d0 _)
  have ρ₁ : radius T r ≤ 1 := (div_le_self rp.le (one_le_pow₀ h (n:=T+2))).trans top.le
  have eq : dock (radius T r)=dock r+(T+2:ℕ)*Real.log (dock r) := by
    change 8+Real.log (r/dock r^(T+2))⁻¹=(8+Real.log r⁻¹)+(T+2:ℕ)*Real.log (dock r)
    rw [Real.log_inv,Real.log_inv,Real.log_div rp.ne' (pow_ne_zero _ d0.ne'),Real.log_pow]
    ring
  have ratio : dock (radius T r) ≤ ((T:ℝ)+3)*dock r := by
    rw [eq]
    have p : 0 ≤ (T:ℝ)+2 := by positivity
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_left ((Real.log_le_sub_one_of_pos d0).trans (sub_le_self _ zero_le_one)) p]
  exact ((pow_le_pow_right₀ (dock_valid _ ⟨ρ,ρ₁⟩) small).trans
    (pow_le_pow_left₀ (zero_le_one.trans (dock_valid _ ⟨ρ,ρ₁⟩)) ratio T)).trans_eq (mul_pow _ _ _)

theorem currency {G : Gauge} (simple : G.Simple) (g : ℝ → ℝ) (hg : Coupling G g) :
    ∃ l u : ℝ, 0 < l ∧ 1 ≤ u ∧ ∀ᶠ r in trail,
      0 < g r ∧ g r ≤ 1 ∧ l ≤ dock r*(g r)^2 ∧ dock r*(g r)^2 ≤ u := by
  let c := G.slopeConstant⁻¹
  have cp : 0 < c := inv_pos.mpr (Gauge.slopeConstant_pos simple)
  refine ⟨c/2,c+9,half_pos cp,by linarith only [cp],?_⟩
  filter_upwards [hg.positive,(hg.conforms simple).eventually (gt_mem_nhds zero_lt_one),
    hg.running.eventually (lt_mem_nhds (half_lt_self cp)),hg.running.eventually (gt_mem_nhds (lt_add_one c))]
    with r gp top lo hi
  refine ⟨gp,top.le,?_,?_⟩
  · unfold dock
    nlinarith only [lo,sq_nonneg (g r)]
  · unfold dock
    have gs : g r ^ 2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ gp.le top.le 2
    nlinarith only [hi,gs]

end YM.Integration.WilsonAddressedReportingScale
end
