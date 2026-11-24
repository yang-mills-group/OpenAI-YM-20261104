import YM.Integration.WilsonPhysicalHistoryPictureRestore

/-! The field-independent mixed marker exponential is a unit. Its removal
from the complete integrable pupil never divides by a gauge-dependent
partition function or by the previously registered painter. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryPictureHaar
open Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open WilsonPhysicalHistoryGroupedLamps WilsonPhysicalHistoryGroupedClear
open WilsonPhysicalHistoryPictureRestore MeasureTheory
open scoped BigOperators Classical

variable {V T I J : Type*} [DecidableEq V] [Fintype V] [Countable I]
  {G : Gauge} {n : Side} {Z : Census V} {P : Rep G n} {o : V → Site n}
  (A : Gallery T I o P Z) (previous : Lamps T J G P.p o Z)
  (w : V → ℝ) (positive : ∀ v, 0 < w v)

omit [Countable I] in
include positive in
theorem cleared {a q : ℝ} (expo : 0 ≤ a) (reg : A.E.Paid w P.p.B a q) (t : T) :
    Poly.pass (-(constant A.E t)) * Poly.pass (constant A.E t) = 1 := by
  have quiet : (constant A.E t).part Z.quiet = 0 := by
    unfold constant
    rw [Poly.share ((Towed.repair (stored A.E w positive {i | A.E.clear i} expo reg t) positive 1).2) _]
    calc
      _ = ∑' _ : I, (0:ℂ) := by
        apply tsum_congr
        intro i
        by_cases h : A.E.clear i <;> simp [row, h]
      _ = 0 := tsum_zero
  have neg : (-(constant A.E t)).part Z.quiet = 0 := by rw [Poly.part_neg, quiet, neg_zero]
  rw [← Extra.Trajectories.pass_add neg quiet, neg_add_cancel, Extra.Trajectories.pass_zero]

include positive in
theorem retained {a q h s bound : ℝ} (expo : 0 ≤ a) (reg : A.E.Paid w P.p.B (a+2) q)
    (hard : A.K.Paid w P.p.B a h) (t : T) (ω : V → ℝ) (pos : ∀ v, 0 < ω v)
    (spatial : 0 ≤ s) (whole : (picture A previous).E.Paid ω P.p.B s bound)
    {μ : Measure (Config G n)} (original : Integrable ((picture A previous).density t) μ) :
    Integrable (WilsonPhysicalHistoryPictureRestore.retained A previous t) μ := by
  let inverse := Poly.pass (-(constant A.E t))
  let mult : Poly Z →ₗ[ℂ] Poly Z := Algebra.lmul ℂ (Poly Z) inverse
  have fixed : WilsonPhysicalHistoryPictureRestore.retained A previous t =
      fun U => inverse * (picture A previous).density t U := by
    funext U
    rw [filed A previous w positive expo reg hard t ω pos spatial whole U, ← mul_assoc]
    change _ = (Poly.pass (-(constant A.E t)) * Poly.pass (constant A.E t)) * _
    rw [cleared A w positive (by linarith : 0 ≤ a+2) reg t, one_mul]
  rw [fixed]
  exact ((LinearMap.toContinuousLinearMap mult).restrictScalars ℝ).integrable_comp original

end YM.Integration.WilsonPhysicalHistoryPictureHaar
end

