import YM.WilsonMS.Beta.TaylorGhost
/-!
# Longitudinal resolution at the S ghost token

Exterior Scc response — budget from rank five leading derivative, UV tail
vanishes on these words. On open scale before zero projection, using this
MS_book, not pretending gauge-contact deletion on all modes.
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
variable {G : Gauge} {B : Local.Physical.Deck G} {M : Booked B}
variable (r : ℝ) (X : Law G) (i j k s : CI G) (p : QP) (x y : Axis) (w μ : List (Lane4 G))
variable (F : MS_Data G M) (hG : G.Simple) (v t u : ℝ)
local notation "H" => Reach F

include hG in
lemma tall_star (h : w.length = 5) (hh : net w = 0) :
    HasDerivAt (fun t : ℝ => Reach F 3 v t w)
      (exp t • tree parity (HeatLine G (exp t)) (Cubic G) (Reach F 2 v t) w) t := by
  obtain he := η F v t w (show 0 < 3 from by decide) (fun _ => hh) (by omega)
  have hs : cycle (Ribbon G t) (covMeasure Axis) (Reach F 3 v t) w = 0 := by
    unfold cycle
    simp only [at_trc]
    simp_rw [show ∀ i j : BH G, ∀ q : QP, Reach F 3 v t ((i, q) :: (j, -q) :: w) = 0 from fun i j q =>
        action_archive F 3 _ _
          (fun t => by
            have he := t.smaller
            simp [h] at he),
      mul_zero, Finset.sum_const_zero]
    simp
  rw [show
      ledgerR F 3 (v, t) w =
        cycle (Ribbon G t) (covMeasure Axis) (Reach F 3 v t) w +
          (2 : ℂ)⁻¹ *
            (∑ k ∈ Domain.paths 3 1, tree parity (Ribbon G t) (Reach F (3 - k) v t) (Reach F k v t) w)
      from ?_,
    hs, zero_add, show Domain.paths 3 1 = { 1, 2 } from ?_, Finset.sum_insert (by decide),
    Finset.sum_singleton] at he
  swap
  · ext i
    simp [Domain.paths]
    omega
  swap
  · unfold ledgerR Domain.recu Domain.using_tree
    simp_rw [Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
    rfl
  rw [swap_tree (K := Ribbon G t) (law_V t) ((archive_disc F).master.trueC 2 (v, t))
      ((archive_disc F).master.trueC 1 (v, t)) w hh] at he
  rw [show
      (tree parity (Ribbon G t) (Reach F 1 v t) (H 2 v t) w) =
        exp t • tree parity (HeatLine G (exp t)) (Cubic G) (H 2 v t) w
      from ?_] at he
  · convert he using 1
    ring
  rw [agrees_tree _ _ _ _ (cubic_reach F v t hG) (show Agrees (H 2 v t) _ from fun _ _ => rfl) w hh,
    log_line]
  exact
    congr_fun (lineT (F := Cubic G) («H» := H 2 v t) (K := HeatLine G (exp t)) ((exp t : ℝ) : ℂ)) w
section body
variable (Q : Law G)
local notation "𝒜" x => W x s p

lemma off_AC (a : List (Lane4 G)) (h : ‖(net a)‖ = 0) : HitM (HeatLine G r) X a w = 0 :=
  hit_light _ (law_S _) X a w (norm_eq_zero.mp h) (line_zero r)

private lemma off_g (m : ℤ) (h : fieldDim ghostNo μ = m) (hv : m > 1 ∨ m < -1) :
    HitM (HeatLine G r) X μ w = 0 :=
  empty_hit r X w μ (by omega) (by omega) (by omega)

def Switch (a b c d e : Lane4 G) (r : ℝ) (Z : Law G) :=
  tree parity (HeatLine G r) (Cubic G) Z [a, b, c, d, e]

lemma key_AA (a b : Axis) (w' : ℝ) :
    Switch (W a s p) (W b s (-p)) (S i 0) (C j 0) (C k 0) w' Q =
      HitM (HeatLine G w') Q [W a s p, C j 0] [W b s (-p), S i 0, C k 0] -
            HitM (HeatLine G w') Q [W a s p, C k 0] [W b s (-p), S i 0, C j 0] +
          HitM (HeatLine G w') Q [W b s (-p), C j 0] [W a s p, S i 0, C k 0] -
        HitM (HeatLine G w') Q [W b s (-p), C k 0] [W a s p, S i 0, C j 0] := by
  let A := W a s p
  let J := W b s (-p)
  let D := S i 0
  let e := C j 0
  let f := C k 0
  let Z := HeatLine G w'
  rw [Switch, grant_five _ _ _ _ _ (law_S w')]
  rw [off_AC w' Q _ [A, J] (by simp [net, A, J, W, qnote]),
    off_AC w' Q _ [D, e] (by simp [net, D, e, S, C, qnote]),
    off_AC w' Q _ [D, f] (by simp [net, D, f, S, C, qnote]),
    off_AC w' Q _ [e, f] (by simp [net, e, f, C, qnote]), off_g w' Q _ [A, D] (-2) rfl (by decide),
    off_g w' Q _ [J, D] (-2) rfl (by decide)]
  norm_num [field, Landau.p, parity, S, W, C, Landau.gauge, gaugeC, ghost, cross]
  abel

lemma key_CP (b : Axis) (z : ℝ) :
    Switch (C s p) (U b s (-p)) (S i 0) (C j 0) (C k 0) z Q =
      HitM (HeatLine G z) Q [C s p, S i 0] [U b s (-p), C j 0, C k 0] +
          HitM (HeatLine G z) Q [U b s (-p), C j 0] [C s p, S i 0, C k 0] -
        HitM (HeatLine G z) Q [U b s (-p), C k 0] [C s p, S i 0, C j 0] := by
  let A := C s p
  let J := U b s (-p)
  let D := S i 0
  let e := C j 0
  let f := C k 0
  rw [Switch, grant_five _ _ _ _ _ (law_S z)]
  rw [off_AC z Q _ [A, J] (by simp [net, A, J, U, C, qnote]),
    off_AC z Q _ [D, e] (by simp [net, D, e, S, C, qnote]),
    off_AC z Q _ [D, f] (by simp [net, D, f, S, C, qnote]),
    off_AC z Q _ [e, f] (by simp [net, e, f, C, qnote]), off_g z Q _ [A, e] 2 rfl (by decide),
    off_g z Q _ [A, f] 2 rfl (by decide), off_g z Q _ [J, D] (-3) rfl (by decide)]
  norm_num [field, Landau.p, parity, S, U, C, anti, gaugeC, ghost, cross]
  abel

lemma parts_AA (u : ℝ) :
    (∑ a : Axis,
        ∑ b : Axis,
          Lace r p a b *
            tree parity (HeatLine G u) (Cubic G) Q [W a s p, W b s (-p), S i 0, C j 0, C k 0]) =
      0 := by
  let P (a b : Axis) := Switch (W a s p) (W b s (-p)) (S i 0) (C j 0) (C k 0) u Q
  change ∑ a : Axis, ∑ b : Axis, Lace r p a b * P a b = 0
  let F (a b : Axis) (j k : CI G) := HitM (HeatLine G u) Q [W a s p, C j 0] [W b s (-p), S i 0, C k 0]
  let V (a b : Axis) (j k : CI G) := HitM (HeatLine G u) Q [W b s (-p), C j 0] [W a s p, S i 0, C k 0]
  have hx (a b) : P a b = F a b j k - F a b k j + V a b j k - V a b k j := key_AA i j k s p Q a b u
  have hv (j k : CI G) (a) : ∑ b : Axis, Lace r p a b * V a b j k = 0 := by
    unfold V
    refine Eq.trans ?_ (seal_WC u s j (-p) a r Q [W a s p, S i 0, C k 0])
    apply Finset.sum_congr rfl
    intro b _
    rw [Lace_neg r p]
    rw [Lace_symm r p a b]
  have hF (j k : CI G) : ∑ a : Axis, ∑ b : Axis, Lace r p a b * F a b j k = 0 := by
    rw [Finset.sum_comm]
    simp_rw [F, seal_WC]
    simp
  simp only [hx, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hF, hF, sub_self]
  simp_rw [hv, Finset.sum_const_zero]
  abel

include hG

lemma parts_C (u : ℝ) :
    (∑ b : Axis,
        SpanH r p b *
          tree parity (HeatLine G u) (Cubic G) (Reach F 2 v t)
            [C s p, U b s (-p), S i 0, C j 0, C k 0]) =
      0 := by
  let P := Reach F 2 v t
  let K := HeatLine G u
  let A' := C s p
  let B (b : Axis) := U b s (-p)
  let D := S i 0
  let e := C j 0
  let f := C k 0
  change ∑ b : Axis, SpanH r p b * Switch A' (B b) D e f u P = 0
  have hx (b : Axis) : HitM K P [A', D] [B b, e, f] = 0 := by
    rw [hit_fade K (law_S u) P _ _ _, clickSC]
    simp only [zero_add, Span_neg]
    have hl (k' : CI G) :
      ∑ x : Axis, 2 * (-SpanH u p x) * (-fColor i k' s) * P (U x k' p :: [B b, e, f]) = 0 := by
      calc
        _ = 2 * fColor i k' s * (∑ x : Axis, SpanH u p x * P (U x k' p :: [B b, e, f])) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun _ _ => by ring)
        _ = 0 := by
          rw [show (∑ x : Axis, SpanH u p x * P (U x k' p :: [B b, e, f])) = 0 from
              seal_four_p u s j k k' p b F hG v t,
            mul_zero]
    simp_rw [hl]
    simp
  have hv (b : Axis) :
    Switch A' (B b) D e f u P =
      HitM K P [A', D] [B b, e, f] + HitM K P [B b, e] [A', D, f] - HitM K P [B b, f] [A', D, e] :=
    key_CP i j k s p P b u
  have he (j k : Lane4 G) (x : CI G) (hq : j = C x 0) :
    ∑ b : Axis, SpanH r p b * HitM K P [B b, j] [A', D, k] = 0 := by
    have ht (b : Axis) : SpanH r p b = -SpanH r (-p) b := by rw [Span_neg, neg_neg]
    rw [hq]
    conv_lhs => arg 2; ext b; arg 1; rw [ht b]
    simp_rw [neg_mul, Finset.sum_neg_distrib, B, K, seal_UC u s]
    simp
  simp_rw [hv, hx, zero_add, mul_sub, Finset.sum_sub_distrib, he e f j rfl, he f e k rfl, sub_self]
end body
end YM.WilsonMS.BetaValue
