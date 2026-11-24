import YM.WilsonMS.Beta.GhostStar
/-!
# SCC cost doesn't move the log

After summing C, U, etc. orientations. Based on the actual shell
projections (no assumption of nonrenormalization in the input package).
`final_notice`: rank-3 log derivative in ledgerR is zero on this token.
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
variable (F : MS_Data G M) (g : G.Simple) (s i j k : CI G) (p : QP) (t u r : ℝ)
local notation "w₀" => SCC G i j k
local notation "Y" => Reach F
local notation "Φ_A(" a "," b ")" => W a s p :: W b s (-p) :: SCC G i j k
local notation "Φ_C(" b ")" => C s p :: U b s (-p) :: SCC G i j k
local notation "℘" => HeatLine G r
include g

private lemma paid_AA : ∑ a : Axis, ∑ b : Axis, Lace r p a b * Reach F 3 u t Φ_A(a,b) = 0 := by
  let W (a b : Axis) := Φ_A(a,b)
  let P (t : ℝ) (w : List (Lane4 G)) := tree parity (HeatLine G (exp t)) (Cubic G) (Reach F 2 u t) w
  let T (t : ℝ) := ∑ a : Axis, ∑ b : Axis, Lace r p a b * Reach F 3 u t (W a b)
  suffices ht : Tendsto T atBot (𝓝 0) ∧ ∀ v : ℝ, T v = T t
    by
    have hp := ht.1
    rw [funext ht.2] at hp
    exact tendsto_nhds_unique tendsto_const_nhds hp
  have hs t : HasDerivAt T 0 t := by
    have he (a b : Axis) :
      HasDerivAt (fun t => Lace r p a b * Reach F 3 u t (W a b))
        (Lace r p a b * (exp t • P t (W a b))) t :=
      (tall_star (W a b) F g u t rfl (by simp [W, SCC, Detect.W, C, S, qnote, net])).const_mul _
    have hx : ∑ a : Axis, ∑ b : Axis, Lace r p a b * (exp t • P t (W a b)) = 0 := by
      simp_rw [Complex.real_smul, mul_left_comm (Lace r p _ _), ← Finset.mul_sum]
      unfold P W
      rw [show (∑ a : Axis, ∑ b : Axis, (Lace r p a b) * tree parity _ _ _ Φ_A(a,b)) = 0 from
          parts_AA r i j k s p (Reach F 2 u t) (exp t),
        mul_zero]
    rw [← hx]
    exact HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => he a b
  have hz (a b : Axis) : Tendsto (fun t => Lace r p a b * Reach F 3 u t (W a b)) atBot (𝓝 0) := by
    simpa only [mul_zero] using
      (UV_boundary F u (W a b) (n := 3)
            (by
              norm_num [W, SCC, C, S, Detect.W, qnote, crown, fieldDim, wfield, dim, gaugeC, ghost,
                Landau.gauge])).const_mul
        (Lace r p a b)
  have he (a : Axis) :
    Tendsto (fun t => ∑ b : Axis, Lace r p a b * Reach F 3 u t (W a b)) atBot (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ fun b _ => hz a b
  exact
    ⟨by simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ fun i _ => he i,
      fun i => (constancy hs i).trans (constancy hs t).symm⟩

private lemma paid_CU : ∑ a : Axis, SpanH r p a * Reach F 3 u t Φ_C(a) = 0 := by
  let W (a : Axis) := Φ_C(a)
  let T (t : ℝ) := ∑ a : Axis, SpanH r p a * Reach F 3 u t (W a)
  let P (t : ℝ) (w : List (Lane4 G)) := tree parity (HeatLine G (exp t)) (Cubic G) (Reach F 2 u t) w
  have h (t : ℝ) : HasDerivAt T 0 t := by
    have hs (a : Axis) : HasDerivAt (fun t => Reach F 3 u t (W a)) (exp t • (P t (W a))) t :=
      tall_star _ F g u t rfl (by simp [W, SCC, C, S, U, qnote, net])
    have he : ∑ a : Axis, SpanH r p a * (exp t • P t (W a)) = 0 := by
      simp_rw [Complex.real_smul, mul_left_comm (SpanH ..), ← Finset.mul_sum]
      rw [show ∑ a : Axis, SpanH r p a * P t (W a) = 0 from parts_C r i j k s p F g u t (exp t),
        mul_zero]
    convert!
      HasDerivAt.fun_sum (u := Finset.univ)
        (fun a (_ : a ∈ (Finset.univ : Finset Axis)) => (hs a).const_mul (SpanH r p a)) using
      1
    exact he.symm
  have ht (t) : T t = T 0 := constancy h t
  have hz : Tendsto T atBot (𝓝 0) := by
    have hK (a : Axis) : Tendsto (fun t => SpanH r p a * Reach F 3 u t (W a)) atBot (𝓝 0) := by
      simpa only [mul_zero] using
        (UV_boundary F u (W a) (n := 3)
              (by
                norm_num [W, SCC, C, S, U, Detect.W, qnote, crown, fieldDim, wfield, dim, anti,
                  Landau.gauge, gaugeC, ghost])).const_mul
          (SpanH r p a)
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ fun i _ => hK i
  change T t = 0
  rw [ht]
  exact tendsto_nhds_unique tendsto_const_nhds ((funext ht) ▸ hz)

private lemma seal_U : ∑ a : Axis, SpanH r p a * Reach F 3 u t (U a s p :: C s (-p) :: w₀) = 0 := by
  refine Eq.trans ?_ (paid_CU F g s i j k (-p) t u r)
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Span_neg]
  have ht := (archive_disc F).master.trueC 3 (u, t)
  rw [show Reach F 3 u t (U a s p :: C s (-p) :: w₀) = -1 * Reach F 3 u t (C s (-p) :: U a s p :: w₀)
      from ht.symm [] (U a s p) (C s (-p)) w₀ (fun _ => by simp [SCC, C, S, U, qnote, net]),
    neg_neg p]
  ring

lemma saved (w : ℝ) : trc ℘ p (Y 3 u w) w₀ = 0 := by
  rw [at_trc, sprint]
  refine Finset.sum_eq_zero fun i' _ => ?_
  simp_rw [atAA, atCU, atUC, Finset.sum_add_distrib]
  rw [show (∑ a : Axis, ∑ b : Axis, (Lace r p a b) * _) = _ from paid_AA F g i' i j k p w u r]
  change _ + ((∑ a : Axis, _) + _) = _
  rw [show (∑ a, _) = _ from
      (show ∑ a : Axis, SpanH r p a * Y 3 u w (U a i' p :: C i' (-p) :: w₀) = _ from
        seal_U F g i' i j k p w u r),
    show ∑ a : Axis, SpanH r p a * Y 3 u w (C i' p :: U a i' (-p) :: w₀) = _ from
      paid_CU F g i' i j k p w u r]
  ring

lemma final_notice : ledgerR F 3 (u, t) (SCC G i j k) = 0 := by
  unfold ledgerR Domain.recu Domain.using_tree
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
  rw [show cycle _ _ _ w₀ = 0 from ?_,
    Finset.sum_eq_zero (fun m _ => tree_spike _ ?_ (K := Ribbon G t) (ribbon_nil t)), smul_zero,
    add_zero]
  swap
  · unfold cycle
    change ∫ (q : QP), trc (Ribbon G t) q _ _ ∂(covMeasure Axis) = 0
    simp_rw [log_line]
    have hs (q : QP) : trc (exp t • HeatLine G (exp t)) q (Y 3 u t) w₀ = 0 := by
      rw [at_trc]
      simp_rw [Pi.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum]
      rw [← at_trc, saved F g, mul_zero]
    simp_rw [hs]
    simp
  intro k' hk
  simp [SCC] at hk
  rcases hk with rfl | rfl | rfl <;> rfl
end YM.WilsonMS.BetaValue
