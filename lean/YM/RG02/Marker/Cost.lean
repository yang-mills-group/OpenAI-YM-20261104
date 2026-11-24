import YM.RG02.Marker.Evaluation

/-!
# Conditional error of division

Several options for budgeting the next step. Important: `separate_cost`
should not in general be applied estimating each unnormalized term by
its *uniform volume* cost -- it applies for example for fixed-volume
or after one has factored out enough of the extensive vacuum *with the
same factor from numerator and denominator*. For comparing two actual
values (no truncation), `relative_log` keeps numerator and denominator
tails assembled to one relative error BEFORE imposing any bound. All costs
for the nil marker operations themselves use literal `Marker.Poly.price`
at the given weights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Evaluation
open Marker Extra.Trajectories Finset Grade PowerSeries Marks
open scoped BigOperators
variable {ι : Type} [DecidableEq ι] {B : Census ι} {w : ι → ℝ}

/-- Actual conditioning in the marker algebra. -/
def divideAway (x : Poly B) := (x.part B.quiet)⁻¹ • x

lemma remains_one {x : Poly B} (hx : x.part B.quiet≠0) : (divideAway x).part B.quiet=1 := by
  rw [divideAway,Poly.part_smul,inv_mul_cancel₀ hx]

/-- With overflow and vacuum loss explicit. Charge at this evaluated
field; no inference of a support representation of its difference. -/
theorem remainder_formula (x y : Poly B) (z : Script B) (r : ℕ) (t : ℂ)
    (h : x = hist z r t + y) (hb : basepoint z ≠ 0) (hx : x.part B.quiet≠0) :
    divideAway x - hist (Grade.quotient z) r t = (x.part B.quiet)⁻¹ •
      ((y - (y.part B.quiet) • hist (Grade.quotient z) r t) -
        overflow (scalar B (den z)) (Grade.quotient z) r t) := by
  let Q := hist (Grade.quotient z) r t
  let e := overflow (scalar B (den z)) (Grade.quotient z) r t
  have hv : hist z r t + e=solo (den z) r t • Q := by
    rw [show e= _ from rfl]; unfold e
    rw [show hist z r t=hist (scalar B (den z)*Grade.quotient z) r t from congr_arg (fun m => hist m r t) (unnormalized hb).symm, ← multiply]
    rw [scalar_hist,Poly.product_bead]
  let p := x.part B.quiet
  have he : p=solo (den z) r t+y.part B.quiet := by unfold p; rw [h,Poly.part_plus,hist_den]
  apply smul_right_injective (r:=p) _ hx
  change p • (p⁻¹ • x - Q)=p • p⁻¹ • _
  rw [smul_sub, smul_inv_smul₀ hx, smul_inv_smul₀ hx, he, h, add_smul]
  change hist _ _ _ + _ - (solo (den z) r t • Q + _) = (y - _ • Q) - e
  rw [← hv]; abel

lemma neg_price (m : Poly B) : Poly.price w (-m) = Poly.price w m := by unfold Poly.price; simp
lemma sub_price (hw : ∀ i,0<w i) (m n : Poly B) : Poly.price w (m-n) ≤ Poly.price w m+Poly.price w n := by
  rw [sub_eq_add_neg]; exact (Poly.addition hw ..).trans_eq (by rw [neg_price])

/-- Evaluation bound retaining the centered error. Both that error and
this overflow accounting (which uses an unnormalized coefficient cost),
after division by the constant at x, still require estimates. -/
theorem separate_cost (x y : Poly B) (z : Script B) (r : ℕ) (t : ℂ)
    (h : x = hist z r t + y) (hb : basepoint z ≠ 0) (hx : x.part B.quiet≠0)
    (ht : ‖t‖ ≤ 1) (hw : ∀ i, 0<w i) :
    let Q := Grade.quotient z
    Poly.price w (divideAway x - hist Q r t) ≤ ‖(x.part B.quiet)⁻¹‖ *
      (Poly.price w (y - y.part B.quiet • hist Q r t) +
       ‖t‖^(r+1)*cost w (scalar B (den z)) Q r) := by
  intro Q; unfold Q; rw [remainder_formula x y _ _ _ h hb hx,Poly.adapted]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (sub_price hw _ _).trans (add_le_add ?_ (overflow_cost hw ht _ _ _)); rfl

/-- Corollary, *pointwise* on x,y,z. Has an absolute inverse denominator
cost and coefficient costs -- don't silently convert it to a uniform
bound. Keep weights explicit. -/
theorem order_bound (x y : Poly B) (z : Script B) (r : ℕ) (t : ℂ)
    (h : x=hist z r t+y) (hb : basepoint z ≠ 0) (hx : x.part B.quiet ≠ 0)
    (ht : ‖t‖ ≤ 1) (hw : ∀ i,0<w i) (C K : ℝ) (hy : Poly.price w y ≤ C*‖t‖^(r+1))
    (hq : Poly.price w (hist (Grade.quotient z) r t) ≤ K) :
    let Q := Grade.quotient z
    Poly.price w (divideAway x - hist Q r t) ≤ ‖(x.part B.quiet)⁻¹‖ *
      (C+C*K+cost w (scalar B (den z)) Q r)*‖t‖^(r+1) := by
  intro Q
  have hp : Poly.price w (y - y.part B.quiet • hist Q r t) ≤ (C+C*K)*‖t‖^(r+1) := by
    have he : ‖y.part B.quiet‖ ≤ C*‖t‖^(r+1) := (by simpa using Poly.member hw B.quiet y : ‖y.part B.quiet‖ ≤ Poly.price w y) |>.trans hy
    refine (sub_price hw ..).trans ?_
    rw [Poly.adapted]
    exact (add_le_add hy (mul_le_mul he hq (Poly.nonnegative hw _) ((Poly.nonnegative hw _).trans hy))).trans_eq (by ring)
  refine (separate_cost x y z _ _ h hb hx ht hw).trans ?_
  rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [add_mul,mul_comm (cost ..)]
  exact add_le_add hp (le_refl _)

section Relative
variable [Fintype ι] {x y : Poly B} (hx : x.part B.quiet≠0) (hy : y.part B.quiet≠0)

/-- Compare two full tables. `y` can include an extensive background
already paid for inside the logarithm. -/
def centered (x y : Poly B) : Poly B :=
  let m := x-y
  m - m.part B.quiet • divideAway y

open Primitives.GCC.Anchor

def reldelta (x y : Poly B) := (x.part B.quiet)⁻¹ • (inverseMass (divideAway y)*centered x y)

include hx hy
omit [Fintype ι] in
theorem centered_formula : divideAway x = divideAway y+(x.part B.quiet)⁻¹ • centered x y := by
  have hp : y.part B.quiet • divideAway y=y := by rw [divideAway, smul_inv_smul₀ hy]
  apply smul_right_injective _ hx
  change x.part B.quiet • divideAway x=x.part B.quiet • (divideAway y+_)
  rw [smul_add,show x.part B.quiet • divideAway x=x by rw [divideAway,smul_inv_smul₀ hx],smul_inv_smul₀ hx]
  unfold centered; simp only [Extra.Trajectories.part_sub,sub_smul,hp]; abel

theorem relative_factor : divideAway x = divideAway y * (1+reldelta x y) := by
  rw [centered_formula hx hy]; unfold reldelta
  rw [mul_add, mul_one,mul_smul_comm, ← mul_assoc, right_inverse (remains_one hy),one_mul]

lemma relative_quiet : (1+reldelta x y).part B.quiet=1 := by
  have he := congrArg (fun v : Poly B => v.part B.quiet) (relative_factor hx hy)
  simpa only [remains_one hx,Poly.quiet_mul,remains_one hy,one_mul] using he.symm

/-- Exact relative log. Can charge `reldelta` with more of the expression
held as one discrepancy than estimating all appearances of (x-y). -/
theorem relative_log : connected (divideAway x)-connected (divideAway y)=
    ∑ i∈range (Fintype.card ι), (((-1:ℂ)^i)/(i+1:ℂ)) • (reldelta x y)^(i+1) := by
  rw [relative_factor hx hy, connected_mul (remains_one hy) (relative_quiet hx hy),add_sub_cancel_left,
    connected_eq_logTable (relative_quiet hx hy),logTable, add_sub_cancel_left]

theorem relative_cost (hw : ∀ i,0<w i) : Poly.price w (connected (divideAway x) - connected (divideAway y)) ≤
    ∑ i∈range (Fintype.card ι), (((i+1:ℕ):ℝ)⁻¹) * (Poly.price w (reldelta x y))^(i+1) := by
  rw [relative_log hx hy]; apply (Poly.batch hw ..).trans
  apply sum_le_sum; intro i _; rw [Poly.adapted]
  have he : ‖(-1:ℂ)^i / (i+1:ℂ)‖=(((i+1:ℕ):ℝ)⁻¹) := by
    rw [norm_div,norm_pow,norm_neg,norm_one,one_pow,one_div]
    rw [← Nat.cast_add_one, Complex.norm_natCast]
  rw [he]; apply mul_le_mul_of_nonneg_left (Poly.powers hw ..); positivity

omit hx hy in
lemma relative_reciprocal (hw : ∀ i,0<w i) :
    Poly.price w (reldelta x y) ≤ ‖(x.part B.quiet)⁻¹‖ *
      (Poly.price w (inverseMass (divideAway y)) * Poly.price w (centered x y)) := by
  rw [reldelta,Poly.adapted]
  exact mul_le_mul_of_nonneg_left (Poly.multiplication hw ..) (norm_nonneg _)
end Relative
end YM.RG02.Evaluation
