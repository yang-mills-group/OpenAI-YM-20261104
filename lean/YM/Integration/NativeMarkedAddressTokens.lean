import YM.Integration.LocalComparisonPackets
import YM.WilsonCoeffUV.Marked.Paths.Height

/-! Render a native marked path packet on independently chosen complex test
functions. Each original kernel is sampled at its own cell coordinate and
derivative address. The joint Riesz measure is fixed before all tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeMarkedAddressTokens
open Function Set Finset MeasureTheory Lattice RG Wilson
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open scoped BigOperators Classical ContDiff

variable {ι : Type} [DecidableEq ι] {G : Gauge} {r : ℕ} {n : Side}
variable (O : ι → Orbit) (J : Finset ι) (Y : ι → Dip)
abbrev axes (v : ι) := (O v).D

/-- The actual affine restriction for each source is applied before its
prescribed, undivided derivative in the indexed coordinate directions. -/
def slot (x : TestSpace O) (v : ι) (k : Knob (axes O v)) (a : Chamber) : ℂ :=
  (iteratedFDeriv ℝ k.1.val ((Y v).plant (x v).val) a.val) (dot ∘ k.2)

def addressValue (x : TestSpace O) (q : Sky (axes O)) : ℂ :=
  (positiveP q.1 : ℝ) * ∏ v ∈ J, slot O Y x v (q.2 v).1 (q.2 v).2

def cellPrice := ∏ v ∈ J, (6 : ℝ)^(O v).W

private lemma chamber_mem (o : Orbit) (a : Chamber) : a.val ∈ o.scope := by
  cases h : o.field with
  | whole => simp only [Orbit.scope, h, ComparisonDensity.Address.space, Set.mem_univ]
  | cell => simpa only [Orbit.scope, h, ComparisonDensity.Address.space, one_div] using a.property

omit [DecidableEq ι] in
lemma slot_paid (fits : ∀ v, (Y v).Fits (O v).field) (x : IndependentTests O)
    (v : ι) (k : Knob (axes O v)) (a : Chamber) :
    ‖slot O Y (testInclusion O x) v k a‖ ≤ (6 : ℝ)^(O v).W := by
  let M := iteratedFDeriv ℝ k.1.val ((Y v).plant (x v).val) a.val
  have h := (Dip.held (fits v) (testInclusion O x v) (x v).property).limits
    k.1.val (Nat.le_of_lt_succ k.1.isLt) a.val (chamber_mem (O v) a)
  have a2 : (1 : ℝ) + ‖a.val‖ ≤ 2 := by linarith [c_norm a]
  calc
    ‖M (dot ∘ k.2)‖ ≤ ‖M‖ := by simpa [Function.comp_apply, dot, Pi.norm_single] using M.le_opNorm (dot ∘ k.2)
    _ ≤ (O v).height a * (3^(O v).W * 1) := h
    _ ≤ 2^(O v).W * 3^(O v).W := by
      rw [mul_one]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) a2 _) (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num

omit [DecidableEq ι] in
lemma address_paid (fits : ∀ v, (Y v).Fits (O v).field) (x : IndependentTests O)
    (q : Sky (axes O)) : ‖addressValue O J Y (testInclusion O x) q‖ ≤ cellPrice O J := by
  simp only [addressValue, norm_mul, Complex.norm_real, pointV, one_mul, norm_prod, cellPrice]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun v _ => slot_paid O Y fits x v _ _)

/-- A concrete token for each native invariant colour atom. Its plot carries
the genuine field footprint and every separately declared source stencil. -/
def token (P : Comet G (Pen (axes O) J) r) (μ : Stationary.Ink G r → Measure (Sky (axes O)))
    (i : Stationary.Ink G r) (z : ι → Cover) (c : ι) (o : Site n) (support : ι → Support n) :
    Token G n (fun v => (O v).Mood) r where
  root := o
  path := (sprigB P i).leg
  gem := fun b x => ((sprigB P i).coeff b : ℂ) * ∫ q, addressValue O J Y x q ∂(μ i)
  fall := (sprigB P i).length + feeH z c J
  plot := (sprigB P i).footprint o ∪ J.biUnion support
  coin := (sprigB P i).magnitude * (cellPrice O J * (μ i).real univ)

omit [DecidableEq ι] in
lemma funds (fits : ∀ v, (Y v).Fits (O v).field) (P : Comet G (Pen (axes O) J) r)
    (μ : Stationary.Ink G r → Measure (Sky (axes O))) (paid : Barn P μ)
    (i : Stationary.Ink G r) (z : ι → Cover) (c : ι) (o : Site n) (support : ι → Support n)
    (x : IndependentTests O) :
    let T := token O J Y P μ i z c o support
    0 ≤ T.coin ∧ ∑ b, ‖T.gem b (testInclusion O x)‖ ≤ T.coin := by
  letI : IsFiniteMeasure (μ i) := (paid i).2.1
  have h := norm_integral_le_of_norm_le_const (μ:=μ i)
    (Filter.Eventually.of_forall (address_paid O J Y fits x))
  have hn : 0 ≤ (sprigB P i).magnitude := Finset.sum_nonneg fun _ _ => abs_nonneg _
  constructor
  · exact mul_nonneg hn (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) ENNReal.toReal_nonneg)
  · change (∑ b, ‖((sprigB P i).coeff b : ℂ) * _‖) ≤ _
    simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_left h hn

omit [DecidableEq ι] in
lemma supports (P : Comet G (Pen (axes O) J) r) (μ : Stationary.Ink G r → Measure (Sky (axes O)))
    (i : Stationary.Ink G r) (z : ι → Cover) (c : ι) (o : Site n) (support : ι → Support n)
    (x : TestSpace O) :
    let T := token O J Y P μ i z c o support
    (T.re x).length ≤ T.fall ∧ (T.re x).footprint o ⊆ T.plot ∧
      ∀ v ∈ J, support v ⊆ T.plot := by
  exact ⟨Nat.le_add_right .., Finset.subset_union_left, fun _ hv _ hh =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, hv, hh⟩)⟩

omit [DecidableEq ι] in
/-- Exact bare invoice at any width. Every original source and field leg
is in the exponent at the same time. This identity also holds at zero fall. -/
theorem expense (P : Comet G (Pen (axes O) J) r) (μ : Stationary.Ink G r → Measure (Sky (axes O)))
    (z : ι → Cover) (c : ι) (o : Site n) (support : ι → Support n) (s : ℝ) :
    (∑ i, let T := token O J Y P μ i z c o support
       T.coin * Real.exp (s * T.fall)) = cellPrice O J * (Real.exp (s * feeH z c J) * lease P μ s) := by
  simp only [lease, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [token, Atom.budget, Nat.cast_add, mul_add, Real.exp_add]
  ring

omit [DecidableEq ι] in
/-- Each evaluation has the native original invariant atom, with its sign
and independent source coefficient supplied by the same measure. -/
theorem value (P : Comet G (Pen (axes O) J) r) (μ : Stationary.Ink G r → Measure (Sky (axes O)))
    (i : Stationary.Ink G r) (z : ι → Cover) (c : ι) (o : Site n) (support : ι → Support n)
    (x : TestSpace O) (U : Config G n) :
    (token O J Y P μ i z c o support).read x U =
      ((sprigB P i).unmasked U o : ℂ) * ∫ q, addressValue O J Y x q ∂(μ i) := by
  simp only [Token.read, Token.touch, token, Atom.unmasked, Atom.poly, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  ring

end YM.Integration.NativeMarkedAddressTokens
end
