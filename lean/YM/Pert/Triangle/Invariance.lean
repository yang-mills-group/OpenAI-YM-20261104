import YM.Pert.Triangle.Determinants
/-!
Spherical transfer identities for the continuum expression. The epsilon-weighted
determinant at large radius is independent of the direction; the convolution
of the two gradient legs only supplies an off-site scalar.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
noncomputable section

namespace YM.Pert.Triangle
open Maxwell Analysis Set Function Metric Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Matrix
local notation "I3" => Fin 3


lemma det_raw (x : Axis→ℝ) : Matrix.det (n:=I3) (fun i j => rawPolynomial i j x) = (∑ i:Axis,x i ^2)^3 := by
  rw [Matrix.det_fin_three]; -- dsimp only
  simp only [raw_entry00, raw_entry01, raw_entry02, raw_entry10, raw_entry11, raw_entry12, raw_entry20, raw_entry21, raw_entry22, Fin.sum_univ_four]
  ring
lemma det_wind (x:E4) : Matrix.det (wind x) = ((8:ℝ)⁻¹ * ‖x‖^6) := by
  have he (i j : I3) : wind x i j = (2:ℝ)⁻¹ * rawPolynomial i j (fun a:Axis=>x a) := by rw [←raw_match];ring
  have hu := det_raw (fun i=>x i)
  rw [Matrix.det_fin_three,← EuclideanSpace.real_norm_sq_eq] at hu; dsimp only at hu
  rw [Matrix.det_fin_three]; simp only [he]
  calc _ = (8:ℝ)⁻¹ * Matrix.det (n:=I3) (fun i j => rawPolynomial i j (fun a:Axis=>x a)) := by rw [Matrix.det_fin_three]; dsimp only;ring
       _ = ((8:ℝ)⁻¹ * ‖x‖^6) := by rw [det_raw,← EuclideanSpace.real_norm_sq_eq]; ring

def blowTwo (A : Matrix I3 I3 ℝ) (i j : I3) :=
    ∑ t:I3,∑ m:I3,∑ n:I3, ((eps3 i j (i+1)):ℝ) * A j m * A (i+1) n * A i t * eps3 m t n
-- contraction weighted by free epsilon at first helicity and flipped labels on second
def blowThree (κ s:ℝ) (A:Matrix I3 I3 ℝ) :=
  ∑ i,∑ j,∑ k,∑ m,∑ n, (eps3 i j k: ℝ) * (κ*A j m) * (κ*A k n) * (∑ t, (κ*A i t) * (eps3 m t n:ℝ) * s)


end YM.Pert.Triangle
