import YM.WilsonMS.Beta.SquaresW
/-!
# Two-point from joining cubic vertices: charged CU part

C (site ghost), U (antifield). This block prices the `Cx-Ax` probe.
The projection orientation needs consistency with `styleScale`.
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
variable {G : Gauge} (r : ℝ) (i j k : CI G) (p q : QP) (t : ℝ) (x y : Axis)
local notation "H" => HeatLine G r
local notation "X" => Cubic G

lemma spin_ac :
    HitM H X [W x i q, C j p] [W y i (-q), U 0 j (-p)] =
      if y = 0 then 2 * SpanH r (q + p) x * colorP i j else 0 := by
  rw [clickWC]
  simp_rw [Span_neg, wing_CWU _ _ j (q + p) (-q) y 0 (-p) (by abel)]
  split_ifs with he hh
  · unfold colorP
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    unfold Angle
    rw [angle_flip j i k]
    ring
  · exact False.elim (hh he.symm)
  · subst y
    exact False.elim (he rfl)
  simp only [neg_zero, mul_zero, Finset.sum_const_zero]

lemma spin_wu :
    HitM H X [W x i q, U 0 j (-p)] [W y i (-q), C j p] =
      -(HitM H X [W y i (-q), C j p] [W x i q, U 0 j (-p)]) := by
  let S := Cubic G
  let l := [W x i q, U 0 j (-p)]
  let v := [W y i (-q), C j p]
  have hx := Crown G |>.solid
  rw [show HitM H X l v = (-1 : ℂ) * HitM H X v l from
      swap_funding
        (show net v + net l = 0 from
          (by
            simp [net, l, v, W, U, C, qnote]
            abel))
        (law_S r) hx hx,
    neg_one_mul]

lemma bearing_wu :
    (2 : ℂ)⁻¹ * Exchange (HeatLine G r) [W x i q, W y i (-q), C j p, U 0 j (-p)] =
      (if y = 0 then 2 * SpanH r (q + p) x * colorP i j else 0) +
        (if x = 0 then 2 * SpanH r (-q + p) y * colorP i j else 0) := by
  have Hh := spin_ac r i j p (-q) y x
  rw [neg_neg] at Hh
  rw [book_exchange _ _ _ _ (law_S r) (by simp [net, W, C, U, qnote]),
    hit_light _ (law_S r) X [W x i q, W y i (-q)] _ (by simp [net, W, qnote]) (line_zero r), spin_ac,
    spin_wu, Hh]
  norm_num [field, parity, Landau.p, W, Landau.gauge, C, U, anti, ghost, cross]
  split_ifs <;> ring

lemma spin_KP :
    HitM H X [C i q, U 0 j (-p)] [U x i (-q), C j p] = 2 * Lace r (q - p) 0 x * colorP i j := by
  rw [hit_fade H (law_S r), ClickUC]
  change (-1 : ℂ) * (∑ i, _) = _
  simp_rw [ahead _ _ (-p + q) (-q) _ _ p (by abel) _, show -p + q = q - p from (by abel), Lace_neg]
  rw [colorP, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single x, if_pos rfl]
  unfold Angle
  rw [f_orient j k i, f_swap i k j]
  ring
  · intro b hb h
    rw [if_neg h.symm, mul_zero]
  simp

lemma bearing_pu :
    (2 : ℂ)⁻¹ * Exchange (HeatLine G r) [C i q, U x i (-q), C j p, U 0 j (-p)] =
      2 * Lace r (q - p) 0 x * colorP i j := by
  let l := [C i q, U x i (-q)]
  rw [book_exchange _ _ _ _ (law_S r) (by simp [net, U, C, qnote]),
    hit_light _ (law_S r) X l _ (by simp [l, U, C, qnote, net]) (line_zero r),
    empty_hit r X _ [C i q, C j p] (by norm_num [C, qnote, fieldDim, ghostNo, ghost, ghostChannel])
      (by norm_num [C, qnote, fieldDim, ghostNo, ghost, ghostChannel])
      (by norm_num [C, qnote, fieldDim, ghostNo, ghost, ghostChannel]),
    spin_KP]
  change (2 : ℂ)⁻¹ * (2 * (0 + _ * 0 + (-1) * (-1) * (2 * Lace _ _ _ _ * colorP _ _))) = _
  ring
end YM.WilsonMS.BetaValue
