import YM.WilsonMS.Beta.Clicks
/-!
# Special zero-momentum payments: longitudinal cancellations

No $MS$ argument about finite parts being zero (contact schemes).
Instead calculate vanishing from the precise `Archive` via the log flow.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue
open Function Filter Set Finset MeasureTheory Metric
open LoopRank Lattice MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect
  Native
open Book Convolve City Logarithm Signal Landau.Detect.Mark Wind High Knobs
open LogTime LogTime.IntervalFamily Outlook Land Arc Wire Rock Path Oceans Plum Alps Garment Color
  Pearl
open Arts Motif Halo
open Complex (I)
open scoped Topology ContDiff BigOperators
variable {G : Gauge}
variable (r : ℝ) (X : Law G) (i j k s : CI G) (p q : QP) (x y : Axis) (w μ : Legs (Lane4 G))

lemma Lace_neg : Lace r (-p) x y = Lace r p x y := by rw [Lace, k_even, brush_neg]

lemma Lace_symm : Lace r p x y = Lace r p y x := by rw [Lace, realK]

lemma Span_neg : SpanH r (-p) x = -SpanH r p x := by
  unfold SpanH
  rw [brush_neg, sq_neg, Pi.neg_apply, Complex.ofReal_neg, mul_neg]

lemma Lace_null : ∑ i : Axis, Lace r p i x * p i = 0 := by
  simp_rw [Lace, Complex.ofReal_mul, mul_assoc, ← Finset.mul_sum, czero, mul_zero]

local notation "K" => HeatLine G r

lemma seal_WC (u : ℝ) (X : Law G) (m : Legs (Lane4 G)) :
    ∑ a : Axis, Lace u p a x * HitM K X [W a i p, C j 0] m = 0 := by
  simp_rw [clickWC, add_zero, Finset.mul_sum, Span_neg, SpanH]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun a _ => ?_
  let V := -2 * I * ((City.brush r p) : ℂ) * p.sq * (-fColor a i j) * X (C a p :: m)
  suffices HE :
    ∀ a' : Axis,
      Lace u p a' x * (2 * (-(SpanH r p a')) * (-fColor a i j) * X (C a p :: m)) =
        V * (Lace u p a' x * (p a' : ℂ))
    by
    change
      (∑ a' : Axis, Lace u p a' x * (2 * (-(SpanH r p a')) * (-fColor a i j) * X (C a p :: m))) = _
    simp_rw [HE, ← Finset.mul_sum, Lace_null, mul_zero]
  intro a'
  unfold V SpanH
  push_cast
  ring

lemma seal_UC (u : ℝ) (X : Law G) (m : Legs (Lane4 G)) :
    ∑ a : Axis, SpanH u p a * HitM K X [U a i p, C j 0] m = 0 := by
  simp_rw [ClickUC, add_zero, Finset.mul_sum, SpanH, Lace_neg]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b _ => ?_
  let V := I * (City.brush u p : ℂ) * (p.sq : ℂ) * 2 * fColor i s j * X (W b s p :: m)
  let U' (a : Axis) := SpanH u p a * (2 * Lace r p a b * fColor i s j * X (W b s p :: m))
  have he a : U' a = V * (Lace r p a b * p a) := by
    unfold U' V SpanH
    ring
  change ∑ a : Axis, U' a = 0
  simp_rw [he, ← Finset.mul_sum, Lace_null, mul_zero]

private lemma seal_four (u : ℝ) :
    ∑ a : Axis, SpanH r p a * Exchange (HeatLine G u) [U a s p, U x i (-p), C j 0, C k 0] = 0 := by
  let Q := Cubic G
  let F := HeatLine G u
  let T := U x i (-p)
  let c := C j 0
  let d := C k 0
  have he (y : Axis) :
    Exchange F [U y s p, T, c, d] =
      2 * (-HitM F Q [U y s p, c] [T, d] + HitM F Q [U y s p, d] [T, c]) := by
    rw [book_exchange (U y s p) T c d (law_S u) (by simp [T, c, d, U, C, net, qnote]),
      hit_light F (law_S u) _ [U y s p, T] _ (by simp [T, U, net, qnote]) (line_zero u)]
    change 2 * (0 + -1 * _ + -1 * -1 * _) = _
    ring
  change ∑ a : Axis, SpanH r p a * Exchange F [U a s p, T, c, d] = 0
  simp_rw [he]
  conv_lhs => arg 2; ext a; arg 2; rw [mul_add];
  let z (a : Axis) :=
    SpanH r p a * (2 * (-HitM F Q [U a s p, c] [T, d]) + 2 * HitM F Q [U a s p, d] [T, c])
  have hx (a : Axis) :
    z a =
      -(2 * (SpanH r p a * HitM F Q [U a s p, c] [T, d])) +
        2 * (SpanH r p a * HitM F Q [U a s p, d] [T, c]) := by
    unfold z
    ring
  change ∑ a : Axis, z a = 0
  simp_rw [hx, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    show ∑ a : Axis, SpanH r p a * HitM F Q [U a s p, c] [T, d] = _ from seal_UC u s j p r Q [T, d],
    show ∑ a : Axis, SpanH r p a * HitM F Q [U a s p, d] [T, c] = _ from seal_UC u s k p r Q [T, c]]
  ring
variable {B : Local.Physical.Deck G} {M : Booked B}
variable (F : MS_Data G M) (hG : G.Simple) (v t : ℝ)

include hG in
lemma seal_four_p : ∑ a : Axis, SpanH r p a * Reach F 2 v t [U a s p, U x i (-p), C j 0, C k 0] = 0 := by
  let P (a : Axis) := [U a s p, U x i (-p), C j 0, C k 0]
  have he (a : Axis) : Reach F 2 v t (P a) = primitive (P a) (exp t) := by
    rw [tree_equation F v t hG _ rfl (show net (P a) = 0 from (by simp [P, U, C, net, qnote])),
      if_neg
        (show crown (P a) ≠ 4 from
          (by norm_num [P, crown, fieldDim, wfield, qnote, U, C, dim, anti, ghost])),
      zero_add]
  let W (a : Axis) (b : ℝ) := Exchange (HeatLine G b) (P a)
  change ∑ a : Axis, SpanH r p a * Reach F 2 v t (P a) = 0
  simp_rw [he, primitive, mul_left_comm (SpanH ..), ← Finset.mul_sum]
  suffices h : (∑ a : Axis, SpanH r p a * (∫ b in 0..exp t, W a b)) = 0 from
    (mul_eq_zero.mpr (Or.inr h))
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum (s := Finset.univ) ?_]
  swap
  · intro i _
    exact ((arc_cont (P i)).intervalIntegrable ..).const_mul _
  simp_rw [W, P, seal_four]
  simp
end YM.WilsonMS.BetaValue
