import YangMills.WilsonProof.NativeSupport.Commissioned259.Local
import YM.WiderProfiles.Application
import Mathlib.MeasureTheory.VectorMeasure.Integral
/-!
# Graded formal M.2 for the *independent* prescription

The signed calibration **hypotheses** are the ones this calculation consumes at M.1;
we isolate exactly what comes from the earlier PoseFit receipt of the NL proof and what
is then true regardless of the upper limit on T. The exact physical measured frame/coupling
call on a Run is in a separate application file (much larger import cone than the formal
Match and this result). This result doesn't require the comparison on the real
physical reads (G.1,G.6,G.9). Don't use `Measure.chi` or a formal calibration in place
of the true t(r).
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

/-- Positive unit for comparing the two coupling sizes. `2 b₀ = slopeConstant` convention. -/
def g0 (G : Gauge) (r : ℝ) : ℝ := (Real.sqrt (G.slopeConstant * Real.log r⁻¹))⁻¹
lemma g0_pos (h : G.Simple) : ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < g0 G r := by
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).eventually_gt_atTop 0] with r hr
  exact inv_pos.mpr (Real.sqrt_pos.mpr (mul_pos (Gauge.slopeConstant_pos h) hr))
lemma g0_zero (h : G.Simple) : Tendsto (g0 G) (𝓝[>] 0) (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
    ((Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).const_mul_atTop (Gauge.slopeConstant_pos h)))

/-- Calibration input of M.1, not a claim to have obtained positive calibration on the real
hierarchy. For instance follows from **these hypotheses previously used in the proof**:
PoseFit's t'ℓ equivalence & that comparison with the measured t(r) (F.3). -/
def Calibrated (G : Gauge) (t : ℝ→ℝ) : Prop := Tendsto (fun r => t r / g0 G r) (𝓝[>] 0) (𝓝 1)

lemma poseFit_calibrates (h : G.Simple) {t t' : ℝ→ℝ} (M : ℕ)
    (h1 : Calibrated G t')
    (h2 : (fun r => t r - t' r)=O[𝓝[>] 0] (fun r => (g0 G r)^(M+2))) : Calibrated G t := by
  have hl : Tendsto (fun r => (t r-t' r)/g0 G r) (𝓝[>] 0) (𝓝 0) := by
    obtain ⟨C,hC,H⟩ := h2.exists_pos
    have fee : Tendsto (fun r:ℝ=> C*(g0 G r)^(M+1)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((g0_zero h).pow (M+1)).const_mul C
    apply squeeze_zero_norm' _ fee
    filter_upwards [H.bound,g0_pos h] with r hr pr
    rw [norm_div]; refine (div_le_iff₀ (Real.norm_of_nonneg pr.le |>.symm ▸ pr)).mpr (hr.trans_eq ?_)
    simp [norm_pow,Real.norm_of_nonneg pr.le, pow_succ, mul_assoc]
  have h' := hl.add h1; rw [zero_add] at h'
  exact h'.congr fun r => by rw [sub_div,sub_add_cancel]

lemma coupling_payment (h : G.Simple) {t : ℝ→ℝ} (paid : Calibrated G t) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < t r ∧ |t r| ≤ 1 ∧ |t r| ≤ 2*g0 G r := by
  filter_upwards [g0_zero h|>.eventually_lt_const (show (0:ℝ)<1/2 by norm_num),
    (show Tendsto _ _ _ from paid).eventually_const_lt (show (0:ℝ)<1 from zero_lt_one),
    (show Tendsto _ _ _ from paid).eventually_lt_const (show (1:ℝ)<2 by norm_num), g0_pos h]
    with r hr lo hi hp
  change _ < t r/g0 G r at lo
  rw [lt_div_iff₀ hp,zero_mul] at lo
  rw [abs_of_pos lo]; replace hi:= (div_lt_iff₀ hp).mp hi; exact ⟨lo,by linarith,hi.le⟩

variable {n m H0 h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ H0)
    (he : ∀ i, e i ≤ H0) (hh : h ≤ H0)
    {U : ℝ} {K : Set (Points n)} {S : Set (Points m)}
    (hU : 0 ≤ U) (hK : IsCompact K) (hc : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
    {W : ℝ} (hW : 1 ≤ W) (ha : clears W K S)
local notation "V" => Scale.Measure.outlook N.scheme N.criterion
local notation "B" => GroupS.gaugeN N.scheme N.criterion M ν
variable {t : ℝ→ℝ}
include H hU hK hc hS hy hW ha

/-- This applies at EVERY T in the moving range of M.1; no need to impose the upper limit
on Far scale for this second bound. `always_clear` shows the geometry predicate for all large W.
No viewer/phase in this formal bound, applies using these predictions at every one of the viewers
in the comparison. All the labels can vary, lower weights and unit included. Use e.g. `U=1`
for the unit balls (sup alphabet coefficient norm). Includes arbitrary proper-subarray purchases
at those arities and position geometries. -/
theorem M2 (paid : Calibrated G t) (p : ℕ) : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
    ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ W, ∀ x ∈ K, ∀ y ∈ S, ∀ u ∈ Balls U G d, ∀ v ∈ Balls U G e,
      ‖crop p (t r) (measurement V B hd he x (T • y) (-Real.log T) u v) -
        crop p (t r) (center V B he (T • y) hh (-Real.log T) (purchased V u x h p (t r)) v)‖ ≤
        C*((T⁻¹)^(h+1)+(g0 G r)^(p+1))*(1+Real.log T)^a := by
  obtain ⟨C,hC,a,h⟩ := all_T hd he hh ((H.dilation ν).check) (H.separatedOPE ν).wilson hU hK hc hS hy hW ha p
  exact ⟨ C,hC,a,(coupling_payment sim paid).mono
    fun r ⟨_,H,K⟩ T hT x hx y hy u hu v hv => h T hT x hx y hy u hu v hv (t r) _ H K⟩

/-- Pair the *same* measurement by any finite signed (even complex-weighted) joint test
on these profiles. T fixed; c is still computed pointwise in the true Near shape. Integrate in
x,y always (thus no change of variables; don't drop the T^(-4m) Jacobian if instead changing y).
Combine before products: no separate sup-cost for first leg in a rectangle test. -/
theorem jointTest (paid : Calibrated G t) (p : ℕ) : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
    ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ W, ∀ u ∈ Balls U G d, ∀ v ∈ Balls U G e,
    ∀ μ : VectorMeasure (↥K × ↥S) ℂ, IsFiniteMeasure μ.variation →
      let Y := fun i : ↥K × ↥S => crop p (t r) (measurement V B hd he i.1.val (T • i.2.val) (-Real.log T) u v)
      let D := fun i : ↥K × ↥S => crop p (t r) (center V B he (T • i.2.val) hh (-Real.log T)
        (purchased V u i.1.val h p (t r)) v)
      μ.Integrable Y ∧ μ.Integrable D ∧
        ‖μ.integral Y (ContinuousLinearMap.mul ℝ ℂ) - μ.integral D (ContinuousLinearMap.mul ℝ ℂ)‖ ≤
          C*((T⁻¹)^(h+1)+(g0 G r)^(p+1))*(1+Real.log T)^a * μ.variation.real univ := by
  obtain ⟨C,hC,a,h⟩ := M2 N ν M H hd he hh hU hK hc hS hy hW ha paid p
  haveI := isCompact_iff_compactSpace.mp hK; haveI := isCompact_iff_compactSpace.mp hS
  refine ⟨C,hC,a,?_⟩
  filter_upwards [h] with r h T ht u hu v hv μ hf Y D
  have cont : Continuous Y ∧ Continuous D := rows_cont hd he hh ((H.dilation ν).check) (H.separatedOPE ν).wilson
    continuous_const (continuous_subtype_val.comp continuous_fst) (continuous_subtype_val.comp continuous_snd)
    (fun _=> zero_lt_one.trans_le (hW.trans ht)) (fun _ _=>continuous_const) (fun _ _=>continuous_const)
    (fun i=> ha T ht _ i.1.property _ i.2.property) (fun i=> hy i.2.property) (fun i => hc i.1.property)
    p (fun _ => t r) continuous_const
  have y : μ.Integrable Y := cont.1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have z : μ.Integrable D := cont.2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨y,z,?_⟩
  change ‖(∫ᵛ i, Y i ∂[ContinuousLinearMap.mul ℝ ℂ;μ])-(∫ᵛ i, D i ∂[ContinuousLinearMap.mul ℝ ℂ;μ])‖≤_
  rw [← VectorMeasure.integral_sub y z]
  exact (VectorMeasure.norm_integral_le_of_norm_le_const (Eventually.of_forall
    fun i : ↥K × ↥S=> h T ht _ i.1.property _ i.2.property _ hu _ hv)).trans_eq
    (by rw [ContinuousLinearMap.opNorm_mul, mul_one])
end YM.FVA2.GradedFar259
