import YM.WilsonMS.Beta.ShellPump
/-!
# CU measurement as a real kinetic projection

Use color response in the included Landau convention. Leave the Lorentz
weights until doing the shell projection as for AA.
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
variable {G : Gauge} (i j : CI G) (r : ℝ) (p q : QP) (t : ℝ) (x y : Axis)
local notation "Κ" => HeatLine G 1
local notation "Ε" => Exchange (HeatLine G r)
local notation "Θ" => colorP i j
local notation "F" => ((2 : ℂ)⁻¹) • Exchange (HeatLine G r)

def Kg (r : ℝ) (p q : QP) : ℂ :=
  2 * ∑ a : Axis, Lace 1 q a 0 * SpanH r (q + p) a

private lemma Kc (a : Axis) :
    (∑ b : Axis, Lace 1 q a b * (if b = 0 then 2 * SpanH r (q + p) a * Θ else 0)) =
      2 * Θ * (Lace 1 q a 0 * SpanH r (q + p) a) := by
  rw [Finset.sum_eq_single (0 : Axis), if_pos rfl]
  ring
  intro b hb hB
  simp [hB]
  simp

private lemma KP :
    (∑ a : Axis, ∑ b : Axis, Lace 1 q a b * (F) (W a i q :: W b i (-q) :: CU G j p)) =
      Θ * Kg r p q + Θ * Kg r p (-q) := by
  let U (a b : Axis) := W a i q :: W b i (-q) :: CU G j p
  change (∑ a : Axis, ∑ b : Axis, _ * ((2 : ℂ)⁻¹ * Ε (U a b))) = _
  have hx (a b : Axis) :
    (2 : ℂ)⁻¹ * Ε (U a b) =
      (if b = 0 then 2 * SpanH r (q + p) a * Θ else 0) +
        (if a = 0 then 2 * SpanH r (-q + p) b * Θ else 0) :=
    bearing_wu r i j p q a b
  simp_rw [hx, mul_add, Finset.sum_add_distrib, Kc]
  congr 1
  · rw [← Finset.mul_sum, Kg]
    ring
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext x; arg 2; ext y; arg 1; rw [Lace_symm, ← Lace_neg 1]
  simp_rw [Kc]
  rw [← Finset.mul_sum, Kg]
  ring

def Kcst (r : ℝ) (p q : QP) : ℂ :=
  2 * ∑ a : Axis, SpanH 1 q a * Lace r (q - p) 0 a

private lemma Kbody :
    (∑ x : Axis, SpanH 1 q x * (F) (C i q :: U x i (-q) :: CU G j p)) = Θ * Kcst r p q := by
  unfold Kcst
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  change _ * ((2 : ℂ)⁻¹ * Ε [_, _, _, _]) = _
  rw [bearing_pu]
  ring

private lemma Km :
    (∑ a : Axis,
        (SpanH 1 q a * (F) (C i q :: U a i (-q) :: CU G j p) +
          SpanH 1 q a * (F) (U a i q :: C i (-q) :: CU G j p))) =
      Θ * Kcst r p q + Θ * Kcst r p (-q) := by
  simp_rw [crossed_T, Finset.sum_add_distrib]
  rw [Kbody, Kbody]

def Kleg (r : ℝ) (p q : QP) :=
  Kg r p q + Kcst r p (-q)

lemma paid_Km :
    trc Κ q (((2 : ℂ)⁻¹) • Exchange (HeatLine G r)) (CU G j p) =
      colorScore j * (Kleg r p q + Kleg r p (-q)) := by
  rw [at_trc, sprint 1, colorScore, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [atAA, atUC, atCU]
  rw [KP]
  have ht :
    (∑ a : Axis,
        (SpanH 1 q a * (F) (U a i q :: C i (-q) :: CU G j p) +
          SpanH 1 q a * (F) (C i q :: U a i (-q) :: CU G j p))) =
      colorP i j * Kcst r p q + colorP i j * Kcst r p (-q) := by
    conv_lhs => arg 2; ext a; rw [add_comm];
    exact Km i j r p q
  rw [ht]
  unfold Kleg
  rw [neg_neg]
  ring

abbrev Kproj (t : ℝ) :=
  t • Punit

lemma along_one (a : Axis) : Kproj t a = (if a = 0 then t else 0) := by
  unfold Kproj Punit
  by_cases hp : a = 0 <;> simp [hp]

private lemma transverse_c : precision 0 0 (q + Kproj t) = precision 0 0 q := by
  unfold precision Momentum.sq Landau.delta
  simp_rw [Pi.add_apply, along_one]
  nth_rw 1 [←
    Finset.add_sum_erase _ (fun i : Axis => ((q i + _) : ℝ) ^ 2) (Finset.mem_univ (0 : Axis))]
  nth_rw 1 [← Finset.add_sum_erase _ (fun i : Axis => (q i) ^ 2) (Finset.mem_univ (0 : Axis))]
  simp only [↓reduceIte]
  rw [show
      ∑ x ∈ Finset.univ.erase 0, (q x + if x = 0 then t else 0) ^ 2 =
        ∑ x ∈ Finset.univ.erase 0, (q x) ^ 2
      from Finset.sum_congr rfl fun i hi => by rw [if_neg (Finset.mem_erase.mp hi).1, add_zero]]
  ring

private lemma proj_W : ∑ a : Axis, (precision a 0 q) * ((q + Kproj t) a) = precision 0 0 q * t := by
  simp_rw [Pi.add_apply, along_one, mul_add, sum_add_distrib, Mark.kernel_zero, zero_add]
  simp [mul_ite]

private lemma proj_C : ∑ a : Axis, (-q) a * precision 0 a (q + Kproj t) = precision 0 0 q * t := by
  rw [Finset.sum_congr rfl (f := fun a : Axis => (-q) a * precision 0 a (q + Kproj t)) (g := fun a =>
      precision a 0 (q + Kproj t) * (Kproj t a - (q + Kproj t) a))
      (fun i hi => by
        rw [Pi.add_apply]
        rw [realK 0 i, Pi.neg_apply]
        ring)]
  simp_rw [mul_sub, Finset.sum_sub_distrib, Mark.kernel_zero, sub_zero, along_one]
  rw [Finset.sum_eq_single (0 : Axis), if_pos rfl, transverse_c]
  intro i hi he
  simp [he]
  simp

lemma k_real :
    Kleg r (Kproj t) q =
      I * ((Pill r (Kproj t) q * (2 * t * (q.sq + (q + Kproj t).sq) * precision 0 0 q) : ℝ) : ℂ) := by
  let L := q + Kproj t
  let Y := Pill r (Kproj t) q
  have ha : Kg r (Kproj t) q = 2 * I * (Y : ℂ) * (L.sq : ℂ) * (((precision 0 0 q * t : ℝ)) : ℂ) := by
    rw [← proj_W (q := q) (t := t)]
    unfold Kg
    simp_rw [Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold Y L Lace SpanH Pill
    push_cast
    ring
  have hb :
    Kcst r (Kproj t) (-q) = 2 * I * (Y : ℂ) * (q.sq : ℂ) * (((precision 0 0 q * t : ℝ)) : ℂ) := by
    rw [← proj_C (q := q) (t := t)]
    unfold Kcst
    simp_rw [Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show -q - Kproj t = -(q + Kproj t) from (by abel), Lace_neg, Span_neg]
    unfold Y SpanH Lace Pill
    push_cast
    rw [Pi.neg_apply]
    push_cast
    ring
  rw [Kleg, ha, hb]
  change _ = I * ((Y * (2 * t * (q.sq + L.sq) * _) : ℝ) : ℂ)
  push_cast
  ring
end YM.WilsonMS.BetaValue
