import YM.Integration.WilsonIndependentCapturedRootTariff
import YM.Integration.WilsonPositionProgramCapturedGroupReturn

/-! Pass the signed finite-board estimates on finite families of named
directions to the genuine quadratic rooted charge on the capture page. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedRootLimit
open Filter Finset Lattice RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Spatial
open RegulatorIR.Budget.FVAAlt2.Wind RegulatorIR.Budget.FVAAlt2.Wind.Pine
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky WilsonIndependentCapturedRootTariff
open scoped BigOperators Topology ENNReal Classical
variable {W : Type} {M : W → ℕ} {X Y : Page M → Type} (S : Sky X Y)
variable (root : W → Room) (b : Page M) {r : ℕ}
theorem passed {A B : Packet (X b) r} {left right : ℕ → Packet (X b) r}
    (issued : above atTop A left) (scheduled : above atTop B right)
    {D ρ fee : ℝ} (hd : 0 ≤ D) (hr : 0 < ρ)
    (finite : ∀ E : Finset (Tuple (X b) r), ∀ᶠ n : ℕ in atTop,
      ∃ t : Tuple (X b) r → ℝ,
        (∀ x ∈ E, 0 ≤ t x ∧ ∀ j, dist (root b.bindW) ((S.maps b).pos (x j)) ≤ (t x+D)*S.radius b) ∧
        (∑ x ∈ E, Real.exp (ρ*t x/2)*‖left n x-right n x‖) ≤ fee) :
    markQ (S.coverQ root 2 b) (A-B) ≤ ENNReal.ofReal (cost D ρ * fee) := by
  let width (x : Tuple (X b) r) := (S.coverQ root 2 b).width x
  have k0 : 0 ≤ cost D ρ := sq_nonneg _
  have bound (x : Tuple (X b) r) : width x ≠ ⊤ := by
    obtain ⟨n,t,h,_⟩ := (finite {x}).exists
    obtain ⟨hx,reach⟩ := h x (mem_singleton_self x)
    exact ne_of_lt ((atPage S root b x hx hd hr reach).trans_lt ENNReal.ofReal_lt_top)
  change (∑' x, ‖A x-B x‖ₑ * width x) ≤ _
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro E
  have pay : (∑ x ∈ E, ‖A x-B x‖*(width x).toReal) ≤ cost D ρ * fee := by
    apply le_of_tendsto (tendsto_finsetSum E (fun x _=>
      (((issued.choose_spec.point x).sub (scheduled.choose_spec.point x)).norm.mul_const ((width x).toReal))))
    filter_upwards [finite E] with n h
    obtain ⟨t,h,priced⟩ := h
    calc
      _ ≤ ∑ x ∈ E, cost D ρ * (Real.exp (ρ*t x/2)*‖left n x-right n x‖) := by
        apply sum_le_sum
        intro x hx
        have hit := atPage S root b x (h x hx).1 hd hr (h x hx).2
        have w : (width x).toReal ≤ cost D ρ * Real.exp (ρ*t x/2) := by
          simpa only [ENNReal.toReal_ofReal (mul_nonneg k0 (Real.exp_pos _).le)] using
            ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hit
        exact (mul_le_mul_of_nonneg_left w (norm_nonneg _)).trans_eq (by ring)
      _ ≤ _ := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left priced k0
  refine (ENNReal.ofReal_le_ofReal pay).trans_eq' ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg)]
  apply sum_congr rfl
  intro x _
  rw [ENNReal.ofReal_mul (norm_nonneg _),ofReal_norm,ENNReal.ofReal_toReal (bound x)]

end YM.Integration.WilsonIndependentCapturedRootLimit
