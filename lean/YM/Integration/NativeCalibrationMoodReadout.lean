import YM.Integration.ActualRunCalibrationTests

/-! The original calibration-coordinate reader on the native qlocal Mood.
The coordinate pullback, factorial, basis norm and affine scale are explicit.
No alternative tensor basis or physical comparison estimate is substituted. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeCalibrationMoodReadout
open Function Finset Lattice Tensor RG05Readout.Native
open ComparisonDensity.Address ActualRunCalibrationTests
open scoped Classical Topology ContDiff

private theorem native_smooth (U : Orbit) (f : U.Mood) {k : ℕ} (hk : k ≤ U.D) :
    ContDiff ℝ (k : WithTop ℕ∞) (f.val ∘ coordinates.symm) :=
  (((U.admits f).choose_spec.orders).of_le (Nat.cast_le.mpr hk)).comp
    coordinates.symm.contDiff

private def records (U : Orbit) (k : ℕ) (hk : k ≤ U.D) (x : E4) :
    U.Mood →ₗ[ℂ] Orb k where
  toFun f := ⟨Tensor.coeff (f.val ∘ coordinates.symm) k x,
    Tensor.coeff_symm (native_smooth U f hk).contDiffAt⟩
  map_add' f g := Subtype.ext
    (coeff_add (native_smooth U f hk).contDiffAt (native_smooth U g hk).contDiffAt)
  map_smul' z f := by
    apply Subtype.ext
    change Tensor.coeff (fun y => z • (f.val ∘ coordinates.symm) y) k x =
      z • Tensor.coeff (f.val ∘ coordinates.symm) k x
    rw [Tensor.coeff, Tensor.coeff,
      iteratedFDeriv_const_smul_apply' (native_smooth U f hk).contDiffAt, smul_comm]

/-- The literal Native.readJ coordinate, extended to finite-smooth native tests. -/
def readout (U : Orbit) {d : ℕ} (i : Letter d) (hi : depth i ≤ U.D)
    (δ : E4) (r : ℝ) : U.Mood →ₗ[ℂ] ℂ :=
  ((r ^ depth i : ℝ) : ℂ) •
    (LinearMap.proj (R := ℂ) (φ := fun _ : Beam (depth i) => ℂ) i.2 ∘ₗ
      (writeC (depth i)).toLinearMap ∘ₗ records U (depth i) hi δ)

/-- Fixed coordinate/basis cost; the displayed factorial is not absorbed. -/
def coordinateCost (k : ℕ) : ℝ :=
  (write_cost k).choose * (k.factorial : ℝ)⁻¹ *
    ‖coordinates.symm.toContinuousLinearMap‖ ^ k

theorem readout_bound (U : Orbit) {d : ℕ} (i : Letter d) (hi : depth i ≤ U.D)
    (δ : E4) {r : ℝ} (hr : 0 ≤ r) (f : U.Mood) {c : ℝ}
    (hf : U.Bill f.val c) (hδ : coordinates.symm δ ∈ U.scope) :
    ‖readout U i hi δ r f‖ ≤
      r ^ depth i * (coordinateCost (depth i) * (U.height (coordinates.symm δ) * c)) := by
  let k := depth i
  have hD :
      ‖iteratedFDeriv ℝ k (f.val ∘ coordinates.symm) δ‖ ≤
        (U.height (coordinates.symm δ) * c) *
          ‖coordinates.symm.toContinuousLinearMap‖ ^ k := by
    rw [show (f.val ∘ coordinates.symm) =
      f.val ∘ coordinates.symm.toContinuousLinearMap from rfl,
      ContinuousLinearMap.iteratedFDeriv_comp_right _ hf.orders _ (Nat.cast_le.mpr hi)]
    exact ((iteratedFDeriv ℝ k f.val (coordinates.symm δ)).norm_compContinuousLinearMap_le
      (fun _ => coordinates.symm.toContinuousLinearMap)).trans (by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_right (hf.limits k hi _ hδ) (by positivity))
  have hR : ‖records U k hi δ f‖ ≤
      (k.factorial : ℝ)⁻¹ *
        ((U.height (coordinates.symm δ) * c) *
          ‖coordinates.symm.toContinuousLinearMap‖ ^ k) := by
    change ‖Tensor.coeff (f.val ∘ coordinates.symm) k δ‖ ≤ _
    rw [Tensor.coeff, norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hD (by positivity)
  change ‖((r ^ k : ℝ) : ℂ) • (writeC k (records U k hi δ f)) i.2‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hr _)]
  calc
    _ ≤ r ^ k * ((write_cost k).choose *
        ((k.factorial : ℝ)⁻¹ *
          ((U.height (coordinates.symm δ) * c) *
            ‖coordinates.symm.toContinuousLinearMap‖ ^ k))) :=
      mul_le_mul_of_nonneg_left
        ((norm_le_pi_norm (writeC k (records U k hi δ f)) i.2).trans
          (((write_cost k).choose_spec.2 _).trans
            (mul_le_mul_of_nonneg_left hR (write_cost k).choose_spec.1.le)))
        (pow_nonneg hr _)
    _ = _ := by unfold coordinateCost; dsimp only [k]; ring

theorem readout_cell_bound {d D : ℕ} (i : Letter d) (hi : depth i ≤ D)
    (δ : E4) (hδ : δ ∈ RG05Readout.Native.box)
    {r : ℝ} (hr : 0 ≤ r) (f : (orbit d D).Mood) {c : ℝ}
    (hf : (orbit d D).Bill f.val c) :
    ‖readout (orbit d D) i hi δ r f‖ ≤
      r ^ depth i * (coordinateCost (depth i) * (2 ^ d * c)) := by
  have hx : coordinates.symm δ ∈ (orbit d D).scope := by
    apply (coordinate_box (d := d) (coordinates.symm δ)).2
    simpa only [coordinates.apply_symm_apply] using hδ
  have hn : ‖coordinates.symm δ‖ ≤ 1 / 2 := by
    simpa only [Orbit.scope, orbit, space, Metric.mem_closedBall,
      dist_zero_right] using hx
  have hh : (orbit d D).height (coordinates.symm δ) ≤ 2 ^ d := by
    unfold Orbit.height orbit
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  exact (readout_bound (orbit d D) i hi δ hr f hf hx).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh hf.nonneg)
        (by
          unfold coordinateCost
          exact mul_nonneg (mul_nonneg (write_cost _).choose_spec.1.le (by positivity))
            (by positivity)))
      (pow_nonneg hr _))

def lineMood {d : ℕ} (D : ℕ) (j : Letter d) : (orbit d D).Mood :=
  ⟨lineForm j, ⟨lineCost D j, (line_bill D j).choose_spec.2⟩⟩

def unitMood {d : ℕ} (D : ℕ) (j : Letter d) : (orbit d D).Mood :=
  ⟨unitLine D j, ⟨1, unitLine_bill D j⟩⟩

theorem readout_line {d D : ℕ} (i j : Letter d) (hi : depth i ≤ D)
    (δ : E4) (r : ℝ) :
    readout (orbit d D) i hi δ r (lineMood D j) =
      readJ i 0 (pull δ r (line j)) := by
  have he : (lineMood D j).val ∘ coordinates.symm = (line j).val := by
    funext x
    simp only [lineMood, lineForm, Function.comp_apply,
      coordinates.apply_symm_apply]
  have hR : records (orbit d D) (depth i) hi δ (lineMood D j) =
      RG05Readout.Native.records δ (depth i) (line j) := by
    apply Subtype.ext
    change Tensor.coeff ((lineMood D j).val ∘ coordinates.symm) (depth i) δ =
      Tensor.coeff (line j).val (depth i) δ
    rw [he]
  rw [readJ, rate_consider]
  simp only [smul_zero, add_zero]
  change ((r ^ depth i : ℝ) : ℂ) •
    (writeC (depth i) (records (orbit d D) (depth i) hi δ (lineMood D j))) i.2 = _
  rw [hR]
  rfl

theorem readout_unit_line {d D : ℕ} (i j : Letter d) (hi : depth i ≤ D)
    (δ : E4) (r : ℝ) :
    readout (orbit d D) i hi δ r (unitMood D j) =
      ((lineCost D j : ℂ)⁻¹) • readJ i 0 (pull δ r (line j)) := by
  have he : unitMood D j = ((lineCost D j : ℂ)⁻¹) • lineMood D j :=
    Subtype.ext rfl
  rw [he, map_smul, readout_line]

end YM.Integration.NativeCalibrationMoodReadout
end
