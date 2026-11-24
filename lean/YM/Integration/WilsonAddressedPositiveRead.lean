import YM.Integration.WilsonThermometerUnitFilingPosterior

/-! A pointwise majorant from an original positive quiet owner is heard by
the very same positive Wilson kernels through every earlier flat date. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedPositiveRead
open MeasureTheory Lattice RG Wilson MergeProof.Accent PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingCoarse Primitives.GCC.Anchor
open scoped BigOperators Classical
variable {G : Gauge} (R : Run G) {N per j : ℕ}
local notation "H" => R.family.path
local notation "Y" => Config G (R.family.side j per)

theorem field (f b : Y→ℂ) (live : Integrable b (prior G _)) {K : ℝ}
    (bound : ∀U, ‖f U‖ ≤ K*(b U).re) {u : ℕ} (uj : u ≤ j) :
    ∀U, ‖gust H N per j f u uj U‖ ≤ K*(gust H N per j b u uj U).re := by
  induction uj using Nat.decreasingInduction with
  | self => simpa only [gust_base] using bound
  | of_succ q hq ih =>
    intro U
    rw [gust_step _ _ _ _ _ hq,gust_step _ _ _ _ _ hq]
    let V := ((H).levels.clock.op q per)
    let k := fun z => V.density ((H).β N per (q+1)) z U
    let F := gust H N per j f (q+1) hq
    let B := gust H N per j b (q+1) hq
    have kept : Integrable (fun z => k z • B z) (prior G _) :=
      StepData.push_slice ((H).levels.transition_mass ..) U _ (gust_live _ _ _ _ _ live hq)
    change ‖∫ z,k z • F z ∂prior G _‖ ≤ K*(∫ z,k z • B z ∂prior G _).re
    apply (norm_integral_le_integral_norm _).trans
    calc
      (∫ z,‖k z • F z‖ ∂prior G _) ≤ ∫ z,K*(k z • B z).re ∂prior G _ := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun _=>norm_nonneg _))
          (kept.re.const_mul K) (ae_of_all _ _)
        intro z
        have hp : 0≤k z := V.density_positive _ _ _
        have hit := mul_le_mul_of_nonneg_left (ih z) hp
        change ‖k z • F z‖ ≤ K*(Complex.reCLM (k z • B z))
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hp,Complex.reCLM.map_smul]
        change k z*‖F z‖ ≤ K*(k z*(B z).re)
        simpa only [F,B,mul_left_comm] using hit
      _ = K*(∫ z,k z • B z ∂prior G _).re := by
        rw [integral_const_mul]
        exact congrArg (K*·) (integral_re kept)

theorem original (f b : Y→ℂ) (live : Integrable b (prior G _)) {K : ℝ} (kp : 0 ≤ K)
    (bound : ∀U, ‖f U‖ ≤ K*(b U).re) {u : ℕ} (uj : u ≤ j) :
    ‖reading R (N:=N) f u uj‖ ≤ K*‖reading R (N:=N) b u uj‖ := by
  have price := (field R (N:=N) f b live bound uj 1).trans
    (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) kp)
  unfold reading
  rw [norm_mul,norm_mul,mul_left_comm]
  exact mul_le_mul_of_nonneg_left price (norm_nonneg _)

end YM.Integration.WilsonAddressedPositiveRead
