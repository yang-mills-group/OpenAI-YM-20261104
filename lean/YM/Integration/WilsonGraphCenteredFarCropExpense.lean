import YM.Integration.WilsonGraphCenteredFarReverseBudget

/-! Finite Cauchy products of the two actual field transports. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredCrop

open Finset PowerSeries Function Register MS MS.Fleet MS.Land Continuation
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Jury
open MS.Native MS.Book MS.Menus MS.Tide MS.Book.Program
open scoped BigOperators Classical
variable {G : Gauge} {h : ℕ}

private def crossColumn (t : ℝ) (A B : Guard G h) (q : ℕ × ℕ) : Module.End ℂ (Sec G h) :=
  (t : ℂ)^(q.1 + q.2) • (coeff q.1 A * coeff q.2 B)

/-- The two cropped columns are multiplied in their filed order. -/
theorem product (k : ℕ) (t : ℝ) (A B : Guard G h) :
    atColumn A k t * atColumn B k t =
      atColumn (A * B) k t + ∑ q ∈ pairsAbove k, crossColumn t A B q := by
  let S := (Finset.range (k+1)) ×ˢ (Finset.range (k+1))
  have expand : atColumn A k t * atColumn B k t = ∑ q ∈ S, crossColumn t A B q := by
    unfold atColumn S
    rw [sum_product, Finset.sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun j _ => ?_
    dsimp only [crossColumn]
    rw [pow_add, smul_mul_smul_comm]
  have low : atColumn (A * B) k t =
      ∑ q ∈ S with q.1 + q.2 ∈ Finset.range (k+1), crossColumn t A B q := by
    rw [← sum_fiberwise_eq_sum_filter S (Finset.range (k+1)) (fun q => q.1+q.2)]
    unfold atColumn
    refine sum_congr rfl fun j hj => ?_
    have top := mem_range_succ_iff.mp hj
    rw [coeff_mul, Finset.smul_sum]
    have fiber : S.filter (fun q => q.1+q.2=j) = antidiagonal j := by
      ext q
      simp only [S, mem_filter, mem_product, mem_range_succ_iff, HasAntidiagonal.mem_antidiagonal]
      omega
    rw [fiber]
    refine sum_congr rfl fun q hq => ?_
    rw [crossColumn, HasAntidiagonal.mem_antidiagonal.mp hq]
  rw [expand, low, ← sum_filter_add_sum_filter_not S (fun q => q.1+q.2 ∈ Finset.range (k+1))]
  rcongr _
  simp

theorem price (k : ℕ) (t : ℝ) (A B : Guard G h) (inv : A * B = 1) (heater : |t| ≤ 1) :
    ‖Growth.chairs G h (atColumn A k t) * Growth.chairs G h (atColumn B k t) - 1‖ ≤
      |t|^(k+1) * ∑ q ∈ pairsAbove k,
        ‖Growth.chairs G h (coeff q.1 A)‖ * ‖Growth.chairs G h (coeff q.2 B)‖ := by
  have base : atColumn (1 : Guard G h) k t = 1 := by
    unfold atColumn
    rw [sum_eq_single 0]
    · simp
    · intro j hj ne
      rw [coeff_one, if_neg ne, smul_zero]
    · simp
  have identity := product k t A B
  rw [inv, base] at identity
  have defect :
      Growth.chairs G h (atColumn A k t) * Growth.chairs G h (atColumn B k t) - 1 =
        ∑ q ∈ pairsAbove k, (t : ℂ)^(q.1 + q.2) •
          (Growth.chairs G h (coeff q.1 A) * Growth.chairs G h (coeff q.2 B)) := by
    rw [← Growth.chairs_mul, identity, map_add, Growth.chairs_one, map_sum]
    simp only [crossColumn, _root_.map_smul, Growth.chairs_mul]
    abel
  rw [defect, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => ?_)
  have beyond := ((mem_pairsAbove k q).mp hq).2
  rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (pow_le_pow_of_le_one (abs_nonneg t) heater beyond)
    (norm_mul_le _ _) (norm_nonneg _) (pow_nonneg (abs_nonneg t) _)

open YangMills YM.Answer.ContinuumLimit YM.Integration
universe u

/-- Apply the full above-crop price to the nominated field bank at its signed physical heater. -/
theorem original (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
    (h k : ℕ) (r s : ℝ) :
    let V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let Q := WilsonGraphPaperPublication.perspective.{u} g hg
    let t := ElectedMeasurement.clock V Z r
    let A := Kseries Z Q.MS h (-s)
    let B := AppointedCenteredReverse.reverseSeries Z Q.MS h s
    |t| ≤ 1 → ‖Growth.chairs g.core h (atColumn A k t) * Growth.chairs g.core h (atColumn B k t) - 1‖ ≤
      |t|^(k+1) * ∑ q ∈ pairsAbove k,
        ‖Growth.chairs g.core h (coeff q.1 A)‖ * ‖Growth.chairs g.core h (coeff q.2 B)‖ := by
  intro V Z Q t A B heater
  exact price k t A B (AppointedCenteredReverse.reverseIdentity Z Q.MS Q.matching h s) heater

end YM.FVA2.GradedFar.AppointedCenteredCrop

