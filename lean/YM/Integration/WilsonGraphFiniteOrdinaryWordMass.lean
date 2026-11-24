import YM.GradedFar.Operands
import YM.Integration.WilsonGraphUniformMixedShapeMass

set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
noncomputable section
namespace YM.Integration.GradedFar.AppointedOrdinaryWordMass

open Filter Set YM.FVA2 YM.FVA2.Dframe YM.FVA2.O.Score YM.FVA2.GradedFar
open YM.XSpace YM.XSpace.Normalize YM.Integration.GradedFar.Tariff.Sunshine
open YM.Integration.WilsonGraphUniformMixedShapeMass
open scoped BigOperators Topology ContDiff Classical

/-- Read a signed Cartesian word through any output covector on its actual open chart. -/
theorem dualWord (g : YangMills.GaugeGroup) {n h : ℕ}
    (f : Points n → Sec g.core h) (out : Sec g.core h →ₗ[ℂ] ℂ)
    (word : TraceOrder n) {U : Set (Points n)} (openU : IsOpen U)
    (smooth : ∀ t : Toon g.core h, ContDiffOn ℝ ∞ (fun y => coord t (f y)) U)
    {x : Points n} (hx : x ∈ U) :
    δ word (fun y => out (f y)) x =
      ∑ t : Toon g.core h, out (theory t) * δ word (fun y => coord t (f y)) x := by
  have read (y : Points n) : out (f y) = ∑ t : Toon g.core h, out (theory t) * coord t (f y) := by
    have restored : (∑ t : Toon g.core h, coord t (f y) • theory t) = f y :=
      by simpa only [coord, Module.Basis.coord_apply] using (YM.FVA2.Dframe.all_sig (f y))
    conv_lhs => rw [← restored, map_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [δ_congr openU (fun y _ => read y) word hx,
    δ_sum openU Finset.univ (fun t y => out (theory t) * coord t (f y))
      (fun t _ => contDiffOn_const.mul (smooth t)) word hx]
  apply Finset.sum_congr rfl
  intro t _
  exact δ_const_mul openU (smooth t) (out (theory t)) word hx

/-- Use every original input basis word and its signed output coordinate.
The event is uniform in the inputs and the contractive output covector. -/
theorem finitePrice (g : YangMills.GaugeGroup) {n : ℕ} (d : Fin n → ℕ) (h q : ℕ)
    {ι : Type*} {β : Type*} (l : Filter ι) (clock : ι → ℝ)
    (err : ι → β → AppointedH140Inputs g.core d → Toon g.core h → ℂ)
    (expand : ∀ᶠ r in l, ∀ (x : β) (v : AppointedH140Inputs g.core d) (t : Toon g.core h),
      err r x v t = ∑ b : Picks g.core d, multipliers v b * err r x (basisWord b) t)
    (basis : ∀ (t : Toon g.core h) (b : Picks g.core d), ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ r in l, ∀ x : β, ‖err r x (basisWord b) t‖ ≤ C * |clock r|^(q+1)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r in l, ∀ (x : β) (v : AppointedH140Inputs g.core d)
      (out : Sec g.core h →ₗ[ℂ] ℂ),
      (∀ z, ‖out z‖ ≤ YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) z) →
      ‖∑ t : Toon g.core h, out (theory t) * err r x v t‖ ≤
        A * inputMass g (d := d) v * |clock r|^(q+1) := by
  classical
  choose C hC price using basis
  obtain ⟨D, hD, bound⟩ := multipliersMass g d
  let M (t : Toon g.core h) := YangMills.Matching.sectorMass
    (B := YangMills.maxwellReference g) (theory t)
  let A := ∑ t : Toon g.core h, M t * ∑ b : Picks g.core d, C t b
  have hA : 0 ≤ A := Finset.sum_nonneg fun t _ => mul_nonneg
    (YangMills.Matching.sectorMass_nonneg _) (Finset.sum_nonneg fun b _ => hC t b)
  refine ⟨A * D, mul_nonneg hA hD, ?_⟩
  have common := Filter.eventually_all.mpr fun t => Filter.eventually_all.mpr (price t)
  filter_upwards [expand, common] with r actual paid
  intro x v out contract
  have mass : 0 ≤ inputMass g (d := d) v := Finset.prod_nonneg fun _ _ => YangMills.Matching.sectorMass_nonneg _
  have coordBound (t : Toon g.core h) : ‖err r x v t‖ ≤
      (∑ b : Picks g.core d, C t b) * (D * inputMass g (d := d) v) * |clock r|^(q+1) := by
    rw [actual x v t]
    have charged := sumPrice (multipliers v) (fun b => err r x (basisWord b) t)
      (fun _ => 0) (C t) (D * inputMass g (d := d) v) (|clock r|^(q+1))
      (mul_nonneg hD mass) (bound v) (fun b => by simpa only [sub_zero] using paid t b x)
    simpa only [mul_zero, Finset.sum_const_zero, sub_zero] using charged
  calc
    _ ≤ ∑ t : Toon g.core h, ‖out (theory t) * err r x v t‖ := norm_sum_le _ _
    _ ≤ ∑ t : Toon g.core h, M t * ((∑ b : Picks g.core d, C t b) *
          (D * inputMass g (d := d) v) * |clock r|^(q+1)) := Finset.sum_le_sum fun t _ => by
      rw [norm_mul]
      exact mul_le_mul (contract _) (coordBound t) (norm_nonneg _)
        (YangMills.Matching.sectorMass_nonneg _)
    _ = ∑ t : Toon g.core h, (M t * ∑ b : Picks g.core d, C t b) *
          ((D * inputMass g (d := d) v) * |clock r|^(q+1)) := Finset.sum_congr rfl fun t _ => by ring
    _ = A * ((D * inputMass g (d := d) v) * |clock r|^(q+1)) := (Finset.sum_mul ..).symm
    _ = _ := by ring

end YM.Integration.GradedFar.AppointedOrdinaryWordMass
