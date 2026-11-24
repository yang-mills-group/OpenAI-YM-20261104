import YM.WilsonMS.Beta.Splits
/-!
# Harvesting color slots on a shell line

Use both orientations and support of the pulse in ghost and color label.
This allows later analytic evaluation of traced contributions.
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
variable {G : Gauge} (K : LaneHeat G) (hx : Reverse K parity)
variable (r : ℝ) (F : Law G) (i j : CI G) (p q : QP) (x y : Axis) (w μ : Legs (Lane4 G))

abbrev Aℓ (x : Axis) (i : CI G) : BH G :=
  (Landau.gauge x, i)

abbrev Uℓ (x : Axis) (i : CI G) : BH G :=
  (anti x, i)

abbrev Cℓ (i : CI G) : BH G :=
  (ghost, i)

abbrev Sℓ (i : CI G) : BH G :=
  (gaugeC, i)

local notation "W" => Detect.W

lemma sprint (H : BH G → BH G → ℂ) :
    (∑ a, ∑ b, HeatLine G r a b p * H a b) =
      ∑ i : CI G,
        ((∑ a : Axis, ∑ b : Axis, HeatLine G r (Aℓ a i) (Aℓ b i) p * H (Aℓ a i) (Aℓ b i)) +
          ∑ a : Axis,
            (HeatLine G r (Uℓ a i) (Cℓ i) p * H (Uℓ a i) (Cℓ i) +
              HeatLine G r (Cℓ i) (Uℓ a i) p * H (Cℓ i) (Uℓ a i))) := by
  simp only [HeatLine, LegsK, Landau.choir, Aℓ, Cℓ, Uℓ]
  simp only [↓reduceIte]
  simp only [Fintype.sum_prod_type, Fintype.sum_option, id_eq, ite_mul]
  simp only [Fintype.sum_bool, L0, zero_mul]
  simp only [Landau.gauge, Landau.ghost, Landau.anti]
  simp [Finset.sum_add_distrib]
  simp_rw [Finset.sum_comm (t := Finset.univ (α := G.ColorIndex)) (s := Finset.univ (α := Axis))]
  ring

include hx

lemma hit_light (he : net w = 0) (hp : ∀ i j, K i j 0 = 0) : HitM K F w μ = 0 := by
  rw [HitM, convertR hx]
  simp only [radius, he, neg_zero, hp, mul_zero, zero_mul, Finset.sum_const_zero]

lemma hit_fade (l k : Lane4 G) :
    HitM K F [l, k] μ = (cross (parity l.1) (parity k.1) : ℂ) * HitM K F [k, l] μ := by
  rw [HitM, HitM, convertR hx, convertR hx, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [radius, radius]
  rw [show net [l, k] = net [k, l] from (by simp [net, add_comm]),
    show degree (field parity) [l, k] = degree (field parity) [k, l] from ?_,
    show Cubic G (_ :: [l, k]) = _ from cubic_swap [(i, -net [k, l])] [] l k]
  simp only [List.cons_append, List.nil_append]
  ring
  exact
    (by
      simp only [degree_cons, degree_nil, Bool.xor_false]
      rw [Bool.xor_comm])
omit hx
local notation "℘" => HeatLine G r
local notation "Z" => net w
local notation "Λ(" a "," b ")" => radius (Landau.parity) ℘ a b (Cubic G) F w μ

lemma group_hit :
    HitM ℘ F w μ =
      ∑ i : CI G,
        ((∑ a : Axis, ∑ b : Axis, Λ(Aℓ a i,Aℓ b i)) +
          ∑ a : Axis, (Λ(Uℓ a i,Cℓ i) + Λ(Cℓ i,Uℓ a i))) := by
  rw [HitM, convertR (law_S r)]
  let H (a b : BH G) : ℂ :=
    2 * (cross (parity b) (degree (field parity) w) * Cubic G ((a, -net w) :: w)) *
      F ((b, -(-net w)) :: μ)
  have hp (a b : BH G) : Λ(a,b) = ℘ a b (-net w) * H a b := by
    unfold H radius
    dsimp only
    ring
  simp_rw [hp]
  exact sprint r (-net w) H

local notation "Q(" a "," b ")" => (cross (field parity a) (field parity b) : ℂ)

lemma forward_AC (m : CI G) :
    Cubic G [W x i p, U y j q, C m (-(p + q))] = if y = x then fColor j i m else 0 := by
  rw [show Cubic G [W x i p, U y j q, C m (-(p + q))] = Q(W x i p,U y j q) * _ from
      cubic_swap [] [C m (-(p + q))] _ _]
  rw [List.nil_append, CAplus j i m q p _ y x (by abel)]
  exact one_mul _
end YM.WilsonMS.BetaValue
