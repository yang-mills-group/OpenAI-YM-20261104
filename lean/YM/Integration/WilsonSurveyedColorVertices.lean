import YM.Integration.WilsonSurveyedColorTensor

/-! The actual continuum action tables use the same color contraction in the
Landau kernels and the dimensional dot-tensor presentation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVertices
open Function Maxwell Maxwell.Free WilsonSurveyedColorTensor
open SchemeConversionRG11.Corona (arch)
open MSbar.Pole.Book.Action (spin)
open scoped BigOperators InnerProductSpace Classical
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
local notation "I" => G.ColorIndex
local notation "e" => EuclideanSpace.basisFun I ℝ

private theorem expanded (x y z : G.Color) :
    ∑ i, ∑ j, ∑ k, (x i : ℂ) * y j * z k * spin i j k = (arch x y z : ℂ) := by
  have back (v : G.Color) : (∑ a, v a • e a) = v := by
    simpa only [EuclideanSpace.basisFun_apply, unitColor] using color_sum v
  conv_rhs => rw [← back x, ← back y, ← back z]
  unfold spin SchemeConversionRG11.Corona.arch
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext
    rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Full tensor equality for the dimensionally continued cubic, ghost and
antifield vertices. The external color need not be individually fixed. -/
theorem cubic (same : ∀ x y z, arch (U x) (U y) (U z) = arch x y z)
    (a b c : I) :
    ∑ i, ∑ j, ∑ k, entry U i a * entry U j b * entry U k c * spin i j k =
      spin a b c := by
  exact (expanded (U (e a)) (U (e b)) (U (e c))).trans (congrArg Complex.ofReal (same ..))

theorem landau (a b c : I) : MS.Motif.rune a b c = spin c a b := by
  unfold MS.Motif.rune spin
  rw [MS.Native.scaled_tensor, real_inner_comm]

theorem landauCubic (same : ∀ x y z, arch (U x) (U y) (U z) = arch x y z)
    (a b c : I) :
    ∑ i, ∑ j, ∑ k, entry U i c * entry U j a * entry U k b * MS.Motif.rune j k i =
      MS.Motif.rune a b c := by
  simp only [landau]
  exact cubic U same c a b

/- Both independent action tables preserve the internal commutator color in
the quartic vertex. No action on links of the microscopic gauge group enters. -/
theorem four (same : ∀ x y z, arch (U x) (U y) (U z) = arch x y z)
    (a b c d : I) :
    (∑ t, (∑ i, ∑ j, ∑ k, entry U i t * entry U j a * entry U k b * spin i j k) *
      (∑ l, ∑ m, ∑ n, entry U l t * entry U m c * entry U n d * spin l m n)) / 4 =
      (MSbar.Pole.Book.Action.quartic a b c d).c := by
  simp_rw [cubic U same]
  rfl

end YM.Integration.WilsonSurveyedColorVertices
end
