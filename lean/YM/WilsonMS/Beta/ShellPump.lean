import YM.WilsonMS.Beta.SquaredCU
/-!
# AA: color/spin weights and polarized charges

Shell derivative with both real and ghost orientations. Remaining integrals
on physical momenta can use `Pill` heat envelope and `Musc` polynomial
on vectors. Not a proof just on the projected A-only part of the interaction!
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
variable {G : Gauge} (i j : CI G) (r : ℝ) (p q : QP) (x y : Axis)
local notation "Uq" => q + p

lemma negVtri : Vtri (-p) (-q) x y = -Vtri p q x y := by
  unfold Vtri
  rw [← trident_flip, neg_add_rev]
  simp [add_comm]

lemma negTile : fullTree r (-p) (-q) x y = fullTree r p q x y := by
  unfold fullTree
  simp only [← neg_add, Lace_neg, negVtri, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]

local notation "λΩ(" b "," c ")" => Lace 1 q b c
local notation "Κ" => HeatLine G 1
local notation "Ε" => Exchange (HeatLine G r)
local notation "B^" => ((2 : ℂ)⁻¹) • Exchange (HeatLine G r)
local notation "Φ" => colorP i j

abbrev subbody (p q : QP) (a b : Axis) (r : ℝ) : ℂ :=
  2 * Lace 1 q a b * fullTree r p q a b

private lemma sums_AA :
    (∑ a : Axis, ∑ b : Axis, Lace 1 q a b * (B^) (W a i q :: W b i (-q) :: AA G j p)) =
      Φ * (∑ a : Axis, ∑ b : Axis, subbody p q a b r) +
        Φ * (∑ a : Axis, ∑ b : Axis, subbody p (-q) a b r) := by
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change _ * ((2 : ℂ)⁻¹ * Ε [_, _, _, _]) = _
  rw [bearing_B, show fullTree r (-p) q a b = fullTree r p (-q) a b from ?_]
  unfold subbody
  rw [Lace_neg]
  ring
  exact
    (show _ from
      (by
        nth_rw 1 [← neg_neg q]
        exact negTile ..))

private def ν_charge (p q : QP) (r : ℝ) : ℂ :=
  2 * SpanH 1 q 1 * SpanH r (q + p) 1

private def Spans (p q : QP) (r : ℝ) : ℂ :=
  ν_charge p q r + ν_charge p (-q) r

private lemma amu_Q :
    (∑ a : Axis, SpanH 1 q a * (B^) (C i q :: U a i (-q) :: AA G j p)) = Φ * Spans p q r := by
  simp_rw [Pi.smul_apply]
  rw [Finset.sum_eq_single (1 : Axis)]
  · change _ * ((2 : ℂ)⁻¹ * Ε [_, _, _, _]) = _
    rw [bearing_K, if_pos rfl]
    unfold Spans ν_charge
    rw [show -q + p = -(q + -p) from (by abel), Span_neg r, Span_neg]
    ring
  · intro b hb ht
    change _ * ((2 : ℂ)⁻¹ * Ε [_, _, _, _]) = _
    rw [bearing_K, if_neg ht, mul_zero]
  simp

lemma crossed_T (w : Legs (Lane4 G)) (s : ℝ) :
    SpanH s q x * (B^) (U x i q :: C i (-q) :: w) =
      SpanH s (-q) x * (B^) (C i (-q) :: U x i (-(-q)) :: w) := by
  rw [neg_neg, Span_neg]
  have ht : Ε (U x i q :: C i (-q) :: w) = (-1 : ℂ) * Ε (C i (-q) :: U x i q :: w) := Ebody r _ _ _
  simp only [Pi.smul_apply, smul_eq_mul, ht]
  ring

private lemma sums_entry :
    (∑ a : Axis,
        ((SpanH 1 q a) * (B^) (C i q :: U a i (-q) :: AA G j p) +
          (SpanH 1 q a) * (B^) (U a i q :: C i (-q) :: AA G j p))) =
      Φ * (2 * ν_charge p q r) + Φ * (2 * ν_charge p (-q) r) := by
  simp_rw [crossed_T, Finset.sum_add_distrib]
  rw [amu_Q, amu_Q]
  unfold Spans
  rw [neg_neg]
  ring

def EAm (r : ℝ) (p q : QP) : ℂ :=
  (∑ a : Axis, ∑ b : Axis, subbody p q a b r) + 2 * ν_charge p q r

abbrev colorScore (j : CI G) :=
  ∑ i : CI G, colorP i j

lemma paidAm :
    trc Κ q ((2 : ℂ)⁻¹ • (Exchange (HeatLine G r))) (AA G j p) =
      colorScore j * (EAm r p q + EAm r p (-q)) := by
  rw [at_trc, sprint 1, colorScore, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [atAA, atCU, atUC]
  let b (a) := SpanH 1 q a * (B^) (C i q :: U a i (-q) :: AA G j p)
  let c (a) := SpanH 1 q a * (B^) (U a i q :: C i (-q) :: AA G j p)
  change
    (∑ a : Axis, ∑ b : Axis, Lace 1 q a b * (B^) (W a i q :: W b i (-q) :: AA G j p)) +
        (∑ a : Axis, (c a + b a)) =
      _
  rw [sums_AA]
  conv_lhs => arg 2; arg 2; ext x; rw [add_comm]
  rw [sums_entry]
  unfold EAm
  ring

/--
All angular cost before inserting scales. Use `Musc` for the polynomial. -/
def Bones (p q : QP) (a b : Axis) : ℝ :=
  ∑ x : Axis, ∑ y : Axis, precision x y (q + p) * Vtri p q x a * Vtri p q y b

def Musc (p q : QP) : ℝ :=
  2 * (∑ a : Axis, ∑ b : Axis, precision a b q * Bones p q a b) -
    4 * (q.sq * q 1) * (Momentum.sq (q + p) * (q + p) 1)

def Pill (r : ℝ) (p q : QP) : ℝ :=
  City.brush 1 q * City.brush r (q + p)

lemma Am_real : EAm r p q = (Pill r p q * Musc p q : ℝ) := by
  have ht : ∀ a b : Axis, fullTree r p q a b = City.brush r (q + p) * (Bones p q a b : ℂ) := by
    intro a b
    unfold Bones fullTree
    simp_rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    unfold Lace
    push_cast
    ring
  let W := Pill r p q
  let Z := (∑ a : Axis, ∑ b : Axis, precision a b q * Bones p q a b)
  have hx : (∑ a : Axis, ∑ b : Axis, subbody p q a b r) = (2 : ℂ) * (W : ℂ) * (Z : ℂ) := by
    unfold Z
    simp_rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    unfold subbody
    rw [ht]
    unfold W Pill Lace
    push_cast
    ring
  rw [EAm, hx]
  unfold Musc ν_charge SpanH
  change _ = ((W * (2 * Z - _) : ℝ) : ℂ)
  unfold W Pill
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring
end YM.WilsonMS.BetaValue
