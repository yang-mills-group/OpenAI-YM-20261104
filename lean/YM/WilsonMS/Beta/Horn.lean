import YM.WilsonMS.Beta.ContactPower
/-!
# Physical numerator on the four-plane

Will contract against two transversal projectors. Factor the trident to
avoid a proof (and accounting) explosion by opening 256 leg assignments.
Compute exact polynomial, not just its rotational projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue.Horn
open Function Filter Set Finset MeasureTheory Metric
open LoopRank Lattice MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect
  Native
open Book Convolve City Logarithm Signal Landau.Detect.Mark Wind High Knobs
open LogTime LogTime.IntervalFamily Outlook Land Arc Wire Rock Path Oceans Plum Alps Garment Color
  Pearl
open Arts Motif Halo HeatPapers
open Complex (I)
open scoped Topology ContDiff BigOperators

abbrev Duo :=
  Axis → QP

def pingP (q : QP) (p : QP) (A B : Duo) : ℝ :=
  ∑ a : Axis, ∑ b : Axis, precision a b q * ∑ i : Axis, ∑ j : Axis, precision i j p * A i a * B j b
variable (p q u v x y : QP) (A B C : Duo) (k : ℝ) (a b : Axis)

lemma hinge : pingP q p (A + B) C = pingP q p A C + pingP q p B C := by
  unfold pingP
  simp_rw [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]

lemma rep : pingP q p (k • A) C = k * pingP q p A C := by
  unfold pingP
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm _ k, ← Finset.mul_sum,
    mul_left_comm _ k, ← Finset.mul_sum]

lemma tip : pingP q p A B = pingP q p B A := by
  unfold pingP
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [realK j i]
  refine congr_arg₂ _ rfl ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [realK l k]
  ring

lemma hingeR : pingP q p A (B + C) = pingP q p A B + pingP q p A C := by
  rw [tip _ _ A, hinge, tip _ _ B, tip _ _ C]

lemma repR : pingP q p A (k • B) = k * pingP q p A B := by rw [tip _ _ A, rep, tip _ _ B]

private def tie (a b : QP) : Duo := fun i j => a i * b j

lemma null_left : pingP p q (tie q x) A = 0 := by
  unfold pingP tie
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  apply mul_eq_zero_of_right
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp_rw [← mul_assoc, ← Finset.sum_mul, kernel_zero, zero_mul]

lemma null_right : pingP p q (tie x p) A = 0 := by
  unfold pingP tie
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b _ => ?_
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  simp_rw [show
      ∀ z,
        precision z b p * (precision i j q * (x i * p z) * A j b) =
          (precision z b p * p z) * (precision i j q * x i * A j b)
      from fun z => by ring,
    ← Finset.sum_mul, kernel_zero, zero_mul]

private abbrev charge (p : QP) (a b : Axis) :=
  precision a b p

private lemma dyadic (l q a b z x : QP) :
    pingP q l (tie a b) (tie z x) =
      (∑ i : Axis, ∑ j : Axis, charge q i j * b i * x j) *
        (∑ i : Axis, ∑ j : Axis, charge l i j * a i * z j) := by
  unfold pingP
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  refine
    Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
  unfold tie
  ring

private def I₄ : Duo := fun a b => if a = b then 1 else 0

private lemma mixed (l q a b : QP) :
    pingP q l (tie a b) I₄ =
      ∑ j : Axis, (∑ i : Axis, charge q i j * b i) * ∑ i : Axis, charge l i j * a i := by
  unfold pingP tie I₄
  simp [mul_ite]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  unfold charge
  ring

private lemma pinned : pingP p q I₄ I₄ = ∑ i : Axis, ∑ j : Axis, precision i j p * precision i j q :=
  by simp [pingP, I₄, mul_ite]

private abbrev ann :=
  Detect.spike 1
local notation "P" => Kproj k
local notation "L'" => q + Kproj k

private lemma moneyT :
    (fun i j => Vtri P q i j) =
      ((2 : ℝ) • ((q 1) • I₄ + tie P ann + (-1 : ℝ) • tie ann P)) + (-1 : ℝ) • tie L' ann +
        (-1 : ℝ) • tie ann q := by
  funext i j
  fin_cases i <;> fin_cases j <;>
      norm_num [Vtri, trident, Motif.polar0, Landau.delta, ann, I₄, Kproj, Punit, tie] <;>
    ring

abbrev R_A {S : Type*} [CommRing S] (q u y z p : S) :=
  let V := q ^ 2 + u ^ 2 + y ^ 2 + z ^ 2
  20 * u ^ 2 * V ^ 2 + 40 * u ^ 2 * q * V * p +
        4 *
            (7 * u ^ 4 + 9 * u ^ 2 * q ^ 2 + 11 * u ^ 2 * y ^ 2 + 11 * u ^ 2 * z ^ 2 +
                      4 * q ^ 2 * y ^ 2 +
                    4 * q ^ 2 * z ^ 2 +
                  4 * y ^ 4 +
                8 * y ^ 2 * z ^ 2 +
              4 * z ^ 4) *
          p ^ 2 +
      16 * q * (u ^ 2 + y ^ 2 + z ^ 2) * p ^ 3 +
    8 * (u ^ 2 + y ^ 2 + z ^ 2) * p ^ 4

abbrev R_S {S : Type*} [CommRing S] (q u y z p : S) :=
  let V := u ^ 2 + y ^ 2 + z ^ 2
  4 * V * (q ^ 2 + V) * p + 4 * q * V * p ^ 2 + 2 * V * p ^ 3

theorem accountable :
    Musc P q =
      2 * 4 *
          (pingP q L' ((q 1) • I₄ + tie P ann + (-1 : ℝ) • tie ann P)
            ((q 1) • I₄ + tie P ann + (-1 : ℝ) • tie ann P)) -
        4 * (q.sq * q 1) * (Momentum.sq L' * L' 1) := by
  let U : Duo := fun i j => Vtri P q i j
  change 2 * pingP q L' U U - _ = _
  rw [show U = _ from moneyT q k]
  let T := (q 1) • I₄ + tie P ann + (-1 : ℝ) • tie ann P
  change 2 * pingP q L' _ ((_ • T + _ : Duo) + _) - _ = _
  have hx (W : Duo) : pingP q L' (tie L' ann) W = 0 := null_left ..
  have hv (W : Duo) : pingP q L' (tie ann q) W = 0 := null_right ..
  have hy (W : Duo) :
    pingP q L' ((2 : ℝ) • T + (-1 : ℝ) • tie L' ann + (-1 : ℝ) • tie ann q) W = 2 * pingP q L' T W := by
    rw [hinge, hinge, rep, rep, rep, hx, hv]
    ring
  rw [hy, tip _ _ T, hy]
  ring

set_option maxHeartbeats 900000 in
set_option maxRecDepth 10000 in
theorem riser_A : SpurA k q = R_A (q 0) (q 1) (q 2) (q 3) k := by
  unfold SpurA
  rw [accountable]
  simp only [hinge, hingeR, Horn.rep, Horn.repR]
  rw [tip L' q I₄ (tie P ann), tip L' q I₄ (tie ann P)]
  simp_rw [mixed, dyadic, pinned]
  norm_num [R_A, charge, precision, Momentum.sq, Landau.delta, Fin.sum_univ_four, Kproj, ann, Punit,
    Detect.spike, Pi.single_apply]
  simp +decide
  ring

theorem riser_S : SpurK k q = R_S (q 0) (q 1) (q 2) (q 3) k := by
  unfold SpurK
  norm_num [R_S, Momentum.sq, precision, Landau.delta, Fin.sum_univ_four, Kproj, Punit, Detect.spike,
    Pi.single_apply]
  simp +decide
  ring
end YM.WilsonMS.BetaValue.Horn
