import YM.Integration.WilsonAddressedCollarPalette

/-! Sum the true measured returns with the coefficients of the incoming field.
    Both the returned lower companion and the residual stay on the same filing. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedCollarSlates
open Finset Filter Lattice Wilson RG Source Extra.Histories RG05Readout RG05Readout.Address
open RG05Readout.Native RG05Readout.Planes RG05Readout.Pulse WilsonLimitConstruction
open Trace.Pilot PhysicalNext.Repeat.Legato Bandage
open scoped Classical BigOperators Topology
variable {G : Gauge} {R : Run G}

private theorem ledger {C : Family G} {d : ℕ}
    (land upper : Palette C d →ₗ[ℂ] Palette C d) (low : Mark C d → Palette C d)
    (x : Palette C d) {g q : ℝ} (gpos : 0 ≤ g) (qpos : 0 ≤ q) (small : q ≤ 1)
    (each : ∀ a, size (land (upper (ticket a)-low a)) ≤ g*q^(weights a))
    (total : size (land (upper x)) ≤ g * size x) :
    let lo := ∑ a, val x a • low a
    size (land (upper x - lo)) ≤ g * ∑ a, ‖val x a‖ * q^(weights a) ∧
      size (land lo) ≤ 2*g*size x := by
  intro lo
  have left : land (upper x-lo) =
      ∑ a, val x a • land (upper (ticket a)-low a) := by
    have list : upper x = ∑ a, val x a • upper (ticket a) :=
      calc
        _ = upper (∑ a, val x a • ticket a) := congrArg upper (cardp x).symm
        _ = _ := by rw [map_sum]; simp only [map_smul]
    unfold lo
    rw [list,←Finset.sum_sub_distrib,map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [←smul_sub,map_smul]
  have cap : size (land (upper x-lo)) ≤ g * ∑ a, ‖val x a‖ * q^(weights a) := by
    rw [left,Finset.mul_sum]
    apply (size_sum _ _).trans
    apply Finset.sum_le_sum
    intro a _
    rw [size_smul]
    exact (mul_le_mul_of_nonneg_left (each a) (norm_nonneg _)).trans_eq (mul_left_comm _ _ _)
  have budget : (∑ a, ‖val x a‖ * q^(weights a)) ≤ size x := by
    apply Finset.sum_le_sum
    intro a _
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ qpos small)
  have loose := cap.trans (mul_le_mul_of_nonneg_left budget gpos)
  refine ⟨cap,?_⟩
  have sum : land lo = land (upper x) + -land (upper x-lo) := by rw [map_sub]; abel
  rw [sum]
  have bound := size_add (land (upper x)) (-land (upper x-lo))
  rw [size_neg] at bound
  exact bound.trans ((add_le_add total loose).trans_eq (by ring))

theorem original (P : WilsonCloseCaptureCalendar.Funding R) (d : ℕ)
    {ε : ℝ} (positive : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ {u N : ℕ} (mu : m ≤ u) (uN : u ≤ N) (per : ℕ)
      (x : Palette R.family d),
      let U := P.basis d (N,per)
      let growth := Real.exp (ε*(R.family.S.scale u-R.family.S.scale m))
      let mesh := R.family.S.a u / R.family.S.a m
      ∃ low : Mark R.family d → Palette R.family d,
        (∀ a, low a = 0 ∨ (0 < weights a ∧
          Address.clear R.family d (weights a-1) (low a) = low a)) ∧
        let lo := lightest R.family d m u • (finer U (mu.trans uN)).symm
          (∑ a, val x a • low a)
        let rest := lightest R.family d m u • (finer U mu).symm x - lo
        size rest ≤ growth * ∑ a, ‖val x a‖ * mesh^(weights a) ∧
        size lo ≤ 2*growth*size x ∧
        ∀ φ : Body, fieldC R.family u N per d (Many.point U x u N) φ =
          fieldC R.family m N per d (Many.point U (rest+lo) m N) φ := by
  filter_upwards [WilsonAddressedCollarPalette.original P d positive,
    WilsonAddressedCollarPalette.total P d positive] with m tariffs all u N mu uN per x
  let U := P.basis d (N,per)
  let g := Real.exp (ε*(R.family.S.scale u-R.family.S.scale m))
  let q := R.family.S.a u / R.family.S.a m
  let p : Palette R.family d →ₗ[ℂ] Palette R.family d :=
    lightest R.family d m u • ((finer U (mu.trans uN)).symm).toLinearMap
  choose low paid using tariffs mu uN per
  refine ⟨low,fun a => (paid a).1.imp_right (fun t => ⟨t.1,t.2.1⟩),?_⟩
  let lo := ∑ a, val x a • low a
  let top := finer U uN x
  have up : p top = lightest R.family d m u • (finer U mu).symm x := by
    change lightest R.family d m u • (finer U (mu.trans uN)).symm ((finer U uN) x) = _
    rw [Many.sumwalk U mu uN, LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply]
  have each (a) : size (p (finer U uN (ticket a)-low a)) ≤ g * q^(weights a) :=
    (paid a).2.1
  have small : q ≤ 1 := (div_le_one (R.family.S.a_pos m)).mpr (R.family.S.strictAnti.antitone mu)
  have qpos : 0 ≤ q := div_nonneg (R.family.S.a_pos u).le (R.family.S.a_pos m).le
  have total : size (p top) ≤ g * size x := by rw [up]; exact all mu uN per x
  obtain ⟨cap,old⟩ := ledger p (finer U uN).toLinearMap low x
    (Real.exp_pos _).le qpos small each total
  refine ⟨?_,old,?_⟩
  · change size (lightest R.family d m u • (finer U mu).symm x - p lo) ≤ _
    rw [←up,←map_sub]
    exact cap
  · intro φ
    rw [sub_add_cancel]
    exact summit U x mu uN φ

end YM.Integration.WilsonAddressedCollarSlates
