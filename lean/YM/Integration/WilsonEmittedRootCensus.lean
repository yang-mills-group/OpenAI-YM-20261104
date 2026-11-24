import YM.Integration.WilsonEmittedRootRecovery
import YM.QuadraticLocal.Fk.Broadcast

/-! Differentiated invoices for the actual countable signed Wilson census
on the joint field and coupling. The retained indicator is chosen before
varying the fields, so the same statement applies to cut and wound words. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedRootCensus
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn
open AnalyticBridge.SectorAffine.Offset Comparison.Density Push.AbsoluteSums
open WilsonEmittedWordJointFare
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
variable {P : Passport n V} {Γ : Census V} (M : ι → Row P Γ G X)
variable (q : ι → ℂ) (μ : ι → Prop)

def price (j : ℕ) (i : ι) : ℝ :=
  if μ i then ‖q i‖ * fare (M i) (M i).lamp.power j else 0

def field (z : Chart G n) : ℂ := Air.sums M q μ z.1 (increment 1 z.2)

private theorem letter (i : ι) (j : ℕ) (z : Chart G n) (hz : ‖z‖ ≤ 1) :
    Through j (fun y : Chart G n =>
      if μ i then ScatterR.familyAt M q i y.1 (increment 1 y.2) else 0)
      z (price M q μ j i) := by
  by_cases h : μ i
  · let T := M i
    let L : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight (q i)
    have hp : ‖L‖ = ‖q i‖ := by simp [L,ContinuousLinearMap.norm_smulRight_apply]
    have bound := Render.abroad (tested T T.lamp.power j z hz) L
    have eqn : (fun y : Chart G n => ScatterR.familyAt M q i y.1 (increment 1 y.2)) =
        fun y => L (grain T T.lamp.power y) := by
      funext y
      simp only [ScatterR.familyAt, QuadraticLocal.Sunrise.Loan.letter, grain, power, L,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, Complex.real_smul]
      rw [mul_comm (q i)]
      congr 4
    simp only [h,if_pos,price,eqn]
    rwa [hp] at bound
  · simp [h,price]
    exact Through.control (Push.Uniform.allows_const z (v := (0:ℂ)) (le_of_eq (norm_zero)))

variable (w : V → ℕ) {a : ℝ} {k : ℕ} (staff : Air.Staff M q w a k)

include staff in
private theorem draws (i : ℕ) (z : Chart G n) (v : Fin i → Chart G n) :
    ContDiffAt ℝ ω (field M q μ) z ∧ HasSum
      (fun b => iteratedFDeriv ℝ i (fun u : Chart G n =>
        if μ b then ScatterR.familyAt M q b u.1 (increment 1 u.2) else 0) z v)
      (iteratedFDeriv ℝ i (field M q μ) z v) := by
  apply Air.rings M q w staff μ Prod.fst (fun u : Chart G n => increment 1 u.2) z contDiffAt_fst
  intro e
  have he : ContDiff ℝ ω fun u : Directions G n => G.mat (increment 1 u e) :=
    ((G.exp_jet.comp (contDiff_apply ..))).mul contDiff_const
  exact (he.comp contDiff_snd).contDiffAt

include staff in
theorem tested (j : ℕ) {D : ℝ} (fund : SumBudget (price M q μ j) D)
    (z : Chart G n) (hz : ‖z‖ ≤ 1) :
    Through j (field M q μ) z D := by
  refine ⟨(draws M q μ w staff 0 z 0).1.of_le le_top, fun i hi => ?_⟩
  have hD : 0 ≤ D := (tsum_nonneg fund.1).trans fund.2.2
  apply ContinuousMultilinearMap.opNorm_le_bound hD
  intro v
  let volume := ∏ u : Fin i, ‖v u‖
  have pos : 0 ≤ volume := Finset.prod_nonneg fun _ _ => norm_nonneg _
  let d b := iteratedFDeriv ℝ i (fun u : Chart G n =>
        if μ b then ScatterR.familyAt M q b u.1 (increment 1 u.2) else 0) z v
  have costs : SumBudget (fun b => ‖d b‖) (volume*D) := by
    apply budget_mono (budget_scale pos fund) (fun _ => norm_nonneg _)
    intro b
    exact ((ContinuousMultilinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right ((letter M q μ b j z hz).pay i hi) pos)).trans_eq (mul_comm ..)
  rw [← (draws M q μ w staff i z v).2.tsum_eq]
  exact ((norm_tsum_le_tsum_norm costs.2.1).trans costs.2.2).trans_eq (mul_comm ..)

end YM.Integration.WilsonEmittedRootCensus
