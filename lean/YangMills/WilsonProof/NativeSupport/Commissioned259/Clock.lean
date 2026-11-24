import YangMills.WilsonProof.NativeSupport.Commissioned259.Matched
import Mathlib.Analysis.Asymptotics.Lemmas
/-! # Extract also an unsigned upper t(r) guarantee from just another of the
advertised hypotheses: G.1 on the real clock (only its compact-ratio statement at order 2 and
3, not any field statement).

Although M.1 already has the usual *calibrated* coupling hypotheses, this shows that
our formal M.2 indeed consumes no additional analytic bound on t hidden in the work
with the cropped series. It can be applied under QScale/RoundMeter without even invoking
their separate input/earlier lemma about signed PoseFit equivalence. A useful check that
the two hypotheses are on the same t.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} (N : WilsonPrescription G) {sim : G.Simple} (ν : ℝ)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "ψ" => GroupS.ψ N.criterion M ν
local notation "trail" => 𝓝[>] (0:ℝ)
include H

lemma beta_price : ∃ η : ℝ, coeff 3 (ψ η) ≠ 0 := by
  have h0 := (H.details.normative ν).check.beta0
  by_contra! no
  simp_rw [Scale.Beta.beta, coeff_mk,no,deriv_const] at h0
  have H := Lambda.VertexSlope.eq_b (G:=G)
  have hc : 0<Lambda.VertexSlope.b G := by linarith [Gauge.slopeConstant_pos sim]
  exact Complex.ofReal_ne_zero.mpr hc.ne' ((by simpa using h0.symm) : (Lambda.VertexSlope.b G:ℂ)=0)

/-- Only two orders of G.1 (each at its fixed-η instance). No `T`-growing assertion. -/
def clockCost (k : ℕ) (t : ℝ→ℝ) : Prop := ∀ η : ℝ,
    (fun r=> ↑(t (r*Real.exp (-η))) - crop k (t r) (ψ η)) =O[trail] (fun r=> (g0 G r)^(k+1))

lemma measured_cost {t : ℝ→ℝ} (h2 : clockCost N ν M 2 t) (h3 : clockCost N ν M 3 t) :
    t=O[trail] g0 G := by
  obtain ⟨η,hη⟩ := beta_price N ν M H
  let c := coeff 3 (ψ η)
  have e (r:ℝ) : crop 3 (t r) (ψ η) = crop 2 (t r) (ψ η) + c * ↑(t r ^ 3) := by
    unfold c; rw [crop_apply,crop_apply,Finset.sum_range_succ,Complex.ofReal_pow]; ring
  have lower : (g0 G ^ 4) =O[trail] (g0 G ^ 3) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [(g0_zero sim).abs.eventually_lt_const (show |(0:ℝ)| < 1 by simp)] with r h
    rw [Pi.pow_apply,Pi.pow_apply,norm_pow,norm_pow,one_mul, pow_succ,Real.norm_eq_abs]
    exact mul_le_of_le_one_right (by positivity) h.le
  have X : (fun r => (↑(t r ^ 3) : ℂ)) =O[trail] (g0 G ^ 3) := by
    apply (isBigO_const_mul_left_iff (show c≠0 from hη)).mp; apply ((h2 η).sub ((h3 η).trans lower)).congr_left; intro r
    rw [e]; abel
  apply IsBigO.of_pow (n:=3) (by norm_num)
  exact isBigO_norm_left.mp (by simpa only [Pi.pow_apply, Complex.norm_real] using isBigO_norm_left.mpr X)

variable {n m H0 h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ H0)
    (he : ∀ i, e i ≤ H0) (hh : h ≤ H0)
    {U : ℝ} {K : Set (Points n)} {S : Set (Points m)}
    (hU : 0 ≤ U) (hK : IsCompact K) (hc : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
    {W : ℝ} (hW : 1 ≤ W) (ha : clears W K S)
local notation "V" => Scale.Measure.outlook N.scheme N.criterion
local notation "B" => GroupS.gaugeN N.scheme N.criterion M ν
include hU hK hc hS hy hW ha
variable {t : ℝ→ℝ}

lemma unsigned_price (paid : t=O[trail] g0 G) (p : ℕ) : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
    ∀ᶠ r in trail, ∀ T ≥ W, ∀ x ∈ K, ∀ y ∈ S, ∀ u ∈ Balls U G d, ∀ v ∈ Balls U G e,
      ‖crop p (t r) (measurement V B hd he x (T • y) (-Real.log T) u v) -
        crop p (t r) (center V B he (T • y) hh (-Real.log T) (purchased V u x h p (t r)) v)‖ ≤
        C*((T⁻¹)^(h+1)+(g0 G r)^(p+1))*(1+Real.log T)^a := by
  obtain ⟨C,hC,a,E⟩ := all_T hd he hh ((H.dilation ν).check) (H.separatedOPE ν).wilson hU hK hc hS hy hW ha p
  obtain ⟨L,hL,budget⟩ := paid.exists_pos
  refine ⟨C*(1+L^(p+1)),by positivity,a,?_⟩
  filter_upwards [g0_pos sim, budget.bound, (paid.trans_tendsto (g0_zero sim)).abs.eventually_lt_const
    (show |(0:ℝ)| < 1 by simp)] with r hr br tr T ht x hx y hy u hu v hv
  rw [Real.norm_of_nonneg hr.le,Real.norm_eq_abs] at br
  have hlog := Real.log_nonneg (hW.trans ht)
  have tpos := zero_lt_one.trans_le (hW.trans ht)
  have hh : |t r| ≤ 2*(L*g0 G r) := br.trans (by linarith [mul_pos hL hr])
  apply (E T ht x hx y hy u hu v hv (t r) _ tr.le hh).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  rw [mul_assoc, mul_pow]; apply mul_le_mul_of_nonneg_left _ hC.le; nlinarith [show 0 ≤ L^(p+1) * (T⁻¹)^(h+1) by positivity, show 0 ≤ g0 G r ^ (p+1) by positivity]
end YM.FVA2.GradedFar259
