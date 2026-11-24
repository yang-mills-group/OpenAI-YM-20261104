import YM.WilsonMS.Beta.ZeroGhost
/-!
# Two-point from joining cubic vertices

Apply the shuffle algebra for those specific contractions, at all momenta
along the relevant axes. This is for the AA part, but includes both gauge
and ghost trident contributions in the derivation.
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
variable (r : ℝ) (P : Law G) (i j k : CI G) (p q : QP) (t : ℝ) (x y a : Axis)
local notation "H" => HeatLine G r
local notation "X" => Cubic G

abbrev Angle (z i j : CI G) : ℂ :=
  fColor z i j * fColor z i j
local notation "u" => p + q

lemma wing_CWU (s : QP) (he : p + (q + s) = 0) :
    Cubic G [C i p, W x j q, U y k s] = -(if y = x then fColor k j i else 0) := by
  let A := C i p
  let v := W x j q
  let z := U y k s
  have hx : X [A, v, z] = 1 * X [A, z, v] := cubic_swap [A] [] v z
  have hy : X [A, z, v] = (-1 : ℂ) * X [z, A, v] := cubic_swap [] [v] A z
  have hh : X [z, A, v] = (1 : ℂ) * X [z, v, A] := cubic_swap [z] [] A v
  rw [hx, hy, hh]
  rw [CAplus k j i s q p y x
      (by
        abel_nf at he ⊢
        exact he)]
  ring

lemma wing_CUW (s : QP) (he : p + (q + s) = 0) :
    Cubic G [C i p, U y k s, W x j q] = -(if y = x then fColor k j i else 0) := by
  have hz := wing_CWU i j k p q x y s he
  rw [← hz]
  exact
    Eq.trans
      (show Cubic G _ = 1 * Cubic G [C i p, W x j q, U y k s] from
        cubic_swap [C i p] [] (U y k s) (W x j q))
      (one_mul _)

lemma trident_flip (s : QP) : trident (-p) (-q) (-s) x y a = -trident p q s x y a := by
  unfold trident polar0 delta
  simp only [Pi.neg_apply]
  split_ifs <;> ring

def Vtri (p q : QP) (x y : Axis) : ℝ :=
  trident (-(q + p)) q p x y 1

def fullTree (r : ℝ) (p q : QP) (a b : Axis) : ℂ :=
  ∑ x : Axis, ∑ y : Axis, Lace r (q + p) x y * (Vtri p q x a : ℂ) * (Vtri p q y b : ℂ)

def colorP (i j : CI G) :=
  ∑ s : CI G, Angle s i j

lemma spin_WW :
    HitM H X [W x i q, W 1 j p] [W y i (-q), W 1 j (-p)] = 2 * colorP i j * fullTree r p q x y := by
  rw [clickWW, colorP, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold fullTree
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [field_W z i j (-(q + p)) q p, field_W z i j (q + p) (-q) (-p), Lace_neg,
    show trident (q + p) (-q) (-p) b y 1 = -(trident (-(q + p)) q p b y 1) from ?_]
  swap
  · nth_rw 1 [← neg_neg (q + p)]
    exact trident_flip ..
  push_cast
  unfold Angle Vtri
  ring_nf
  rw [Complex.I_sq]
  ring

lemma Ebody (μ : ℝ) (w : List (Lane4 G)) (i j : Lane4 G) :
    Exchange (HeatLine G μ) (i :: j :: w) =
      cross (parity i.1) (parity j.1) * Exchange (HeatLine G μ) (j :: i :: w) := by
  have h :=
    tree_sym (F := Cubic G) («H» := Cubic G) (p := parity)
      (closure (id : Momentum Axis → Momentum Axis) (L_cl μ)) (fund_one G 0).sym (fund_one G 0).sym
  exact h [] i j w

lemma bearing_B :
    (2 : ℂ)⁻¹ * Exchange (HeatLine G r) [W x i q, W y i (-q), W 1 j p, W 1 j (-p)] =
      2 * colorP i j * (fullTree r p q x y + fullTree r (-p) q x y) := by
  let P := Cubic G
  let A := W x i q
  let v := W y i (-q)
  let Xq := W 1 j p
  let b := W 1 j (-p)
  rw [book_exchange _ _ _ _ (law_S r) (by simp [net, W, qnote]),
    hit_light _ (law_S r) P [A, v] _ (by simp [net, A, v, W, qnote]) (line_zero r), spin_WW,
    show HitM H P [A, b] [v, Xq] = _ from
      (show HitM H P [A, b] [v, Xq] = 2 * colorP i j * fullTree r (-p) q x y from ?_)]
  · norm_num [field, parity, Landau.p, W, Landau.gauge, cross]
    ring
  have h := spin_WW r i j (-p) q x y
  rw [neg_neg] at h
  exact h

lemma angle_flip : fColor i j k = -fColor k j i := by rw [f_orient k j i, f_swap i j k]

lemma spin_cw :
    HitM H X [C i q, W 1 j p] [U x i (-q), W 1 j (-p)] =
      if x = 1 then 2 * SpanH r (q + p) 1 * colorP i j else 0 := by
  let A := C i q
  let v := W 1 j p
  have he := hit_fade H (law_S r) X [U x i (-q), W 1 j (-p)] A v
  rw [he, clickWC]
  change (1 : ℂ) * ∑ k : CI G, _ = _
  rw [one_mul]
  simp_rw [add_comm p q, Span_neg]
  simp_rw [wing_CUW _ _ _ (q + p) (-p) 1 x (-q) (by abel)]
  split_ifs with he'
  · subst x
    unfold colorP
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold Angle
    rw [angle_flip i j k, f_orient k j i, f_swap j i k, ← f_orient k i j]
    ring
  simp only [neg_zero, mul_zero, Finset.sum_const_zero]

lemma bearing_K :
    (2 : ℂ)⁻¹ * Exchange (HeatLine G r) [C i q, U x i (-q), W 1 j p, W 1 j (-p)] =
      if x = 1 then 2 * colorP i j * (SpanH r (q + p) 1 + SpanH r (q + -p) 1) else 0 := by
  let P := Cubic G
  let A := C i q
  let v := U x i (-q)
  let X' := W 1 j p
  let k := W 1 j (-p)
  have Hh := spin_cw r i j (-p) q x
  rw [neg_neg] at Hh
  rw [book_exchange _ _ _ _ (law_S r) (by simp [net, C, U, W, qnote]),
    hit_light _ (law_S r) P [A, v] _ (by simp [net, A, v, C, U, qnote]) (line_zero r), spin_cw, Hh]
  split_ifs <;> (norm_num [field, parity, Landau.p, W, U, C, Landau.gauge, cross] <;> ring)
end YM.WilsonMS.BetaValue
