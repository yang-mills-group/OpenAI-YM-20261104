import YM.OPE.Therm.Law

/-! A signed cofactor on the normalized original one-step Wilson kernel.
The earlier field is held fixed throughout the finite Haar integral. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonHeldHaarCofactor

open Set MeasureTheory Lattice Wilson RG Next.Extract Push.GridApprox OPE.Therm Cells WardBin.Wheels
open scoped Classical

variable {G : Gauge} (H : History G) (N per j : ℕ)
local notation "fine" => Config G (H.S.side (j+1) per)
local notation "coarse" => Config G (H.S.side j per)
local notation "Q" => H.rep N per (j+1)
local notation "Q'" => H.rep N per j
local notation "S" => H.levels.clock.op j per
local notation "β" => H.β N per (j+1)
local notation "ν" => prior G (H.S.side (j+1) per)

/-- The genuine blocked conditional at the specified lower field. -/
def conditional (X : fine → ℂ) (V : coarse) : ℂ :=
  (S).push β (fun U => (Q).eval U • X U) V / ((Q').eval V : ℂ)

theorem normalized (history : H.Selected) (live : j+1 ≤ N) (V : coarse) :
    conditional H N per j (fun _ => 1) V = 1 := by
  let q : fine → ℂ := fun U => ((Q).eval U : ℂ)
  have stage : pushTo H N per (Nat.le_succ j) q = (S).push β q := by
    simpa only [pushTo_self] using pushTo_next H N per (le_rfl : j ≤ j) q
  have law := congrFun (enact history (p := per) (Nat.le_succ j) live) V
  change pushTo H N per (Nat.le_succ j) q V = ((Q').eval V : ℂ) at law
  rw [stage] at law
  have positive := gravity history ((Nat.le_succ j).trans live) V
  have nz : ((Q').eval V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  unfold conditional
  simp only [Complex.real_smul, mul_one]
  exact (congrArg (fun z : ℂ => z / ((Q').eval V : ℂ)) law).trans (div_self nz)

/-- A complete signed density identity at the fine date remains exact at
every lower field, with the full positive pushed vacuum in the denominator. -/
theorem held (E : Set fine) (X F T : fine → ℂ)
    (paid : ∀ U ∈ E, ((Q).eval U : ℂ) * X U = F U) (V : coarse) :
    conditional H N per j (E.indicator (fun U => T U * X U)) V =
      (∫ U, E.indicator (fun W => ((S).density β W V : ℂ) * T W * F W) U ∂ν) /
        ((Q').eval V : ℂ) := by
  unfold conditional StepData.push
  apply congrArg (fun z : ℂ => z / ((Q').eval V : ℂ))
  apply integral_congr_ae
  apply ae_of_all
  intro U
  by_cases h : U ∈ E
  · simp only [Set.indicator_of_mem h, Complex.real_smul]
    rw [← paid U h]
    ring
  · simp only [Set.indicator_of_notMem h, smul_zero]

/-- The absolute invoice uses only the actual exterior, true Wilson kernel,
and the signed fine cofactor after its original cancellation. -/
theorem price (history : H.Selected) (live : j+1 ≤ N)
    (E : Set fine) (X F T : fine → ℂ)
    (paid : ∀ U ∈ E, ((Q).eval U : ℂ) * X U = F U) (V : coarse) :
    ‖conditional H N per j (E.indicator (fun U => T U * X U)) V‖ ≤
      (∫ U, E.indicator (fun W => ‖(S).density β W V‖ * ‖T W‖ * ‖F W‖) U ∂ν) /
        (Q').eval V := by
  have positive := gravity history ((Nat.le_succ j).trans live) V
  rw [held H N per j E X F T paid V, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos positive]
  apply div_le_div_of_nonneg_right _ positive.le
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  apply ae_of_all
  intro U
  by_cases h : U ∈ E
  · simp only [Set.indicator_of_mem h, norm_mul, Complex.norm_real]
  · simp only [Set.indicator_of_notMem h, norm_zero]

end YM.Integration.WilsonHeldHaarCofactor

