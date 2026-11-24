import YM.Integration.WilsonFirstReceivedIssuedPhysical
import YM.Integration.WilsonFirstReceivedRadialRoom

/-! Funded true path widths on the original local axial room, uniformly
in the microscopic cutoff and in the period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFirstReceivedIssuedRoom
open Filter Lattice Wilson RG QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Advent Org
open AllOrder AllOrder.Floe.Step.PlanV AllOrder.Transit PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonFirstReceivedRadialStencil
open scoped Classical Topology

private theorem budget_one (d : ℕ) : 1 ≤ WilsonFirstReceivedRadialStencil.budget d := by
  simpa only [Polynomial.eval_one, norm_one, abs_zero, add_zero, one_pow, one_mul, mul_one] using
    (priced (1 : Polynomial ℂ) (d := d) (by simp) (A := 1) (fun _ _ => by simp) 0)

/-- The original prior-aperture purchase is at the actual delay of this run. -/
theorem purchased {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G := G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (paid : ∀ x k : ℕ, k ≤ x → ∀ b : ℝ, R.alloy.delay.betaEntry x ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) x)⁻¹ ^ 2) ≤ b)
    (d k : ℕ) (A H : ℝ) (ha : 0 ≤ A) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, ∀ N per : ℕ, i + 1 ≤ N → ∀ s : ℕ, s ≤ R.alloy.B.a.clock.J i →
      let x := R.family.path.levels.clock.hatBeta i
      let g := regulatorRun R.family N per (i + 1)
      let B := R.family.path.levels.budget i
      let σ := Poetry.Agenda.seed D φ (Burn.horizon s) (R.alloy.B.a.clock.J i)
      ∀ z : ℝ, |z| ≤ |H| * (Real.log x)^k * ((B.B : ℝ)^2 * B.threshold) / g →
        (A * |z| / σ)^d * g ≤ ε := by
  let V := R.family.path.levels
  have grows := RG01.Physical.hats simple V
  filter_upwards [eventually_ge_atTop (1 : ℕ),
      (Real.tendsto_log_atTop.comp grows).eventually_ge_atTop (1 : ℝ),
      WilsonFirstReceivedRadialRoom.original R simple d (k + 1) (A * H) ep] with i hi logs room
  intro N per level s deep x g B σ z hz
  have hs : 0 < σ := Poetry.Agenda.stem ..
  have width : σ⁻¹ ^ 2 ≤ Real.log x := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
    have price := paid _ s deep _ ((R.alloy.B.valid.pays j).trans
      (Push.Corrected.Last.band_le R.alloy.B.a simple (Nat.le_succ j)))
    exact (Real.log_exp _).symm.le.trans (Real.log_le_log (Real.exp_pos _) price)
  change 1 ≤ Real.log x at logs
  have slim : σ⁻¹ ≤ Real.log x := by nlinarith only [width, logs, sq_nonneg (σ⁻¹ - 1)]
  have gp : 0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  let t := A * |z| / σ
  have tp : 0 ≤ t := div_nonneg (mul_nonneg ha (abs_nonneg z)) hs.le
  have lp : 0 ≤ Real.log x := zero_le_one.trans logs
  have bound : |t| ≤ |A * H| * (Real.log x)^(k+1) * ((B.B : ℝ)^2 * B.threshold) / g := by
    rw [abs_of_nonneg tp, abs_mul, abs_of_nonneg ha, pow_succ]
    calc
      t = (A * |z|) * σ⁻¹ := div_eq_mul_inv ..
      _ ≤ (A * |z|) * Real.log x := mul_le_mul_of_nonneg_left slim (mul_nonneg ha (abs_nonneg _))
      _ = (A * Real.log x) * |z| := by ring
      _ ≤ (A * Real.log x) * (|H| * (Real.log x)^k * ((B.B : ℝ)^2 * B.threshold) / g) :=
        mul_le_mul_of_nonneg_left hz (mul_nonneg ha lp)
      _ = _ := by ring
  have quoted := room N per level t bound
  have lift : t^d ≤ (1 + |t|)^d := pow_le_pow_left₀ tp (by rw [abs_of_nonneg tp]; linarith) _
  have nonneg : 0 ≤ (1 + |t|)^d := pow_nonneg (by linarith [abs_nonneg t]) _
  exact (mul_le_mul_of_nonneg_right (lift.trans (le_mul_of_one_le_left nonneg (budget_one d))) gp).trans quoted

end YM.Integration.WilsonFirstReceivedIssuedRoom
