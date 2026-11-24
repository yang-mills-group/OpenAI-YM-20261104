import YM.Integration.WilsonIndependentSchemeTruncation

/-! Finite numerical values of the original independently prescribed position coupling.
The compact test is applied after forming the connected polynomial of the seven
unsmeared three-point arrays. Only the single constant coefficient is removed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionIndependentIntegral

open Filter Set MeasureTheory PowerSeries XSpace XSpace.Normalize XSpace.Cirrus XSpace.Structure1
open FVA2 FVA2.Arrival FVA2.Register FVA2.Scale MS MS.Land
open WilsonIndependentSchemeTruncation
open scoped Topology BigOperators Classical Polynomial

private def Regular (A : Points 3 → PowerSeries ℂ) : Prop :=
  ∀ i : ℕ, ContinuousOn (fun x => coeff i (A x)) (conf 3)

private theorem regular_add {A B : Points 3 → PowerSeries ℂ} (a : Regular A) (b : Regular B) :
    Regular (fun x => A x+B x) := by
  intro i
  apply ((a i).add (b i)).congr
  exact fun x _ => map_add _ _ _

private theorem regular_sub {A B : Points 3 → PowerSeries ℂ} (a : Regular A) (b : Regular B) :
    Regular (fun x => A x-B x) := by
  intro i
  apply ((a i).sub (b i)).congr
  exact fun x _ => map_sub _ _ _

private theorem regular_smul {A : Points 3 → PowerSeries ℂ} (a : Regular A) (z : ℂ) :
    Regular (fun x => z • A x) := by
  intro i
  apply ((a i).const_smul z).congr
  exact fun x _ => map_smul _ z _

private theorem regular_mul {A B : Points 3 → PowerSeries ℂ} (a : Regular A) (b : Regular B) :
    Regular (fun x => A x*B x) := by
  intro i
  simp only [PowerSeries.coeff_mul]
  exact continuousOn_finsetSum _ (fun k _ => (a k.1).mul (b k.2))

variable {G : Gauge} (Z : WilsonPrescription G) (ν : ℝ)
variable {O : MS.Land.Booked (Press.portDeck G)} (T : MS_Data G O)

theorem coefficient (i : ℕ) :
    ContinuousOn (fun x : Points 3 => coeff i (Reg.Choice.trace ν T Z.store x)) (conf 3) := by
  let A (s : Rose.Badge) (x : Points 3) := Rose.batchT (Reg.State.wall ν Z.store T 6 x) s
  have a (s : Rose.Badge) : Regular (A s) := by
    intro k
    simpa only [A,Rose.batchT,coeff_mk] using
      (Reg.State.road ν Z.store T (Rose.missing (Rose.tag G) s) k)
  exact (regular_add
    (regular_sub (a Finset.univ) (regular_add (regular_add
      (regular_mul (a {0,1}) (a {2})) (regular_mul (a {0,2}) (a {1})))
      (regular_mul (a {1,2}) (a {0}))))
    (regular_smul (regular_mul (regular_mul (a {0}) (a {1})) (a {2})) 2)) i

/-- Orders one through q, in the true independent connected continuum array. -/
def positive (q : ℕ) (t : ℝ) (x : Points 3) : ℂ :=
  ∑ k ∈ Finset.range q, (t:ℂ)^(k+1) * coeff (k+1) (Reg.Choice.trace ν T Z.store x)

theorem positive_continuous (q : ℕ) (t : ℝ) :
    ContinuousOn (positive Z ν T q t) (conf 3) :=
  continuousOn_finsetSum _ (fun k _ => continuousOn_const.mul (coefficient Z ν T (k+1)))

private theorem test_linear (φ : Test 3) (q : ℕ) (u : ℕ → Points 3 → ℂ) (z : ℕ → ℂ)
    (h : ∀ k, ContinuousOn (u k) (conf 3)) :
    φ.applyTo (fun x => ∑ k ∈ Finset.range q, z k*u k x) =
      ∑ k ∈ Finset.range q, z k*φ.applyTo (u k) := by
  unfold Test.applyTo
  have prod (x : Points 3) : φ x*(∑ k ∈ Finset.range q,z k*u k x) =
      ∑ k ∈ Finset.range q,z k*(φ x*u k x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => mul_left_comm _ _ _)
  simp only [prod]
  rw [integral_finsetSum _ (fun k _ => (φ.smearing (h k)).const_mul (z k))]
  simp only [integral_const_mul]

private theorem positive_coeff (k : ℕ) :
    coeff (k+1) (Measure.chi Z.criterion ν T) =
      ((Rose.c_T Z.criterion:ℝ):ℂ)⁻¹ *
        (Rose.test Z.criterion).applyTo (fun x => coeff (k+1) (Reg.Choice.trace ν T Z.store x)) := by
  simp [Measure.chi,Reg.Choice.choice,Reg.Choice.tune,Reg.Choice.sky,smul_eq_mul]

private theorem eval_positive (z : PowerSeries ℂ) (zero : coeff 0 z=0) (q : ℕ) (t : ℝ) :
    (finite q z).eval (t:ℂ) = ∑ k ∈ Finset.range q, (t:ℂ)^(k+1)*coeff (k+1) z := by
  induction q with
  | zero => simp [finite,PowerSeries.trunc_apply,zero]
  | succ q ih =>
    rw [Finset.sum_range_succ]
    change (PowerSeries.trunc (q+1+1) z).eval (t:ℂ)=_
    rw [PowerSeries.trunc_succ,Polynomial.eval_add,Polynomial.eval_monomial]
    exact congrArg₂ (·+·) ih (mul_comm _ _)

/-- The numerical polynomial in the original chi is exactly the compact test
of the finite positive part of the original connected coefficient kernel. -/
theorem polynomial (q : ℕ) (t : ℝ) :
    (finite q (Measure.chi Z.criterion ν T)).eval (t:ℂ) =
      ((Rose.c_T Z.criterion:ℝ):ℂ)⁻¹ * (Rose.test Z.criterion).applyTo (positive Z ν T q t) := by
  rw [eval_positive _ (Reg.Choice.proper ν Z.criterion T)]
  simp only [positive_coeff Z ν T]
  have tested : (Rose.test Z.criterion).applyTo (positive Z ν T q t) =
      ∑ k ∈ Finset.range q, (t:ℂ)^(k+1) *
        (Rose.test Z.criterion).applyTo (fun x => coeff (k+1) (Reg.Choice.trace ν T Z.store x)) :=
    test_linear (Rose.test Z.criterion) q (fun k x => coeff (k+1) (Reg.Choice.trace ν T Z.store x))
      (fun k => (t:ℂ)^(k+1)) (fun k => coefficient Z ν T (k+1))
  rw [tested,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => mul_left_comm _ _ _)

theorem real_polynomial (q : ℕ) (t : ℝ) :
    ((finite q (Measure.chi Z.criterion ν T)).eval (t:ℂ)).re =
      ((Rose.test Z.criterion).applyTo (positive Z ν T q t)).re / Rose.c_T Z.criterion := by
  rw [polynomial,← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,div_eq_inv_mul]

theorem point_first (hG : G.Simple) {x : Points 3} (hx : x ∈ conf 3) :
    coeff 1 (Reg.Choice.trace ν T Z.store x) = Reg.State.wall ν Z.store T 6 x 1 (Rose.tag G) :=
  Rose.tangent Z.scheme hG _ (Reg.State.spirit ν Z.store T x hx) hx

variable {hG : G.Simple} {U : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S : Prescription (Press.portDeck G)} {dial : Bool} (M : Main.Match Z hG U S dial)

include M in
theorem unit :
    coeff 1 (Measure.chi Z.criterion ν U) = 1 := by
  obtain ⟨hf,hp⟩ := M.positionCoupling ν
  have e := congrArg (coeff 1 (R:=ℂ)) hp.right
  rw [Reg.Choice.stating_one _ _ hf.start,hf.lead,mul_one,coeff_one_X] at e
  exact e

include M in
/-- The signed independent linear coefficient integrates to the original negative
calibration constant itself. No inversion or convergence of an infinite series is used. -/
theorem first :
    (Rose.test Z.criterion).applyTo (fun x => coeff 1 (Reg.Choice.trace ν U Z.store x)) =
      ((Rose.c_T Z.criterion:ℝ):ℂ) := by
  have e := (positive_coeff Z ν U 0).symm.trans (unit Z ν M)
  have nz : ((Rose.c_T Z.criterion:ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_lt Z.criterion.fresh)
  calc
    _ = ((Rose.c_T Z.criterion:ℝ):ℂ) *
        (((Rose.c_T Z.criterion:ℝ):ℂ)⁻¹ *
          (Rose.test Z.criterion).applyTo (fun x => coeff 1 (Reg.Choice.trace ν U Z.store x))) := by
        rw [←mul_assoc,mul_inv_cancel₀ nz,one_mul]
    _ = _ := by rw [e,mul_one]

include M in
theorem linear (t : ℝ) :
    (finite 1 (Measure.chi Z.criterion ν U)).eval (t:ℂ) = (t:ℂ) := by
  rw [eval_positive _ (Reg.Choice.proper ν Z.criterion U)]
  simp [unit Z ν M]

include M in
theorem full_first :
    (Rose.test Z.criterion).applyTo (fun x => Reg.State.wall ν Z.store U 6 x 1 (Rose.tag G)) =
      ((Rose.c_T Z.criterion:ℝ):ℂ) := by
  rw [← first Z ν M]
  unfold Test.applyTo
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change Rose.test Z.criterion x * (Reg.State.wall ν Z.store U 6 x 1 (Rose.tag G)) =
    Rose.test Z.criterion x * coeff 1 (Reg.Choice.trace ν U Z.store x)
  by_cases hx : x ∈ conf 3
  · rw [point_first Z ν U hG hx]
  · have hz : Rose.test Z.criterion x=0 := by
      by_contra hn
      exact hx ((Rose.test Z.criterion).tsupport_subset (subset_closure hn))
    rw [hz,zero_mul,zero_mul]

end YM.Integration.WilsonPositionIndependentIntegral


