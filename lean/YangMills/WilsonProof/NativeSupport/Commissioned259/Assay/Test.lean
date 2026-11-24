import YangMills.WilsonProof.NativeSupport.Commissioned259.Matched
/-!
# General pairing for the M.2 theorem (including copy for finite signed Real-weighted measures)

Versions with o also varying, joint measure weights arbitrary. Accrue total
variation of the **measure in (o,x,y)**; we do not change variables. In particular same density
argument as in statement of `Matched`. General bilinear use, for measure values E=ℂ/E=ℝ;
use `complexPair`, `realPair` so B of norm 1.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Assay
open Function Filter Set PowerSeries MeasureTheory Maxwell XSpace XSpace.Normalize XSpace.Structure1
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open FVA2.Scale O.Score O.Enh O.Canon Dframe
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {n m h z : ℕ} {d:Fin n→ℕ}{e:Fin m→ℕ}(hd:∀ i,d i≤z)(he:∀ i,e i≤z)(hh:h≤z)
variable {X I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace X] (μ : VectorMeasure X E) (B : ℂ→L[ℝ] E→L[ℝ] ℂ) (hB: ‖B‖ ≤ 1)
    [IsFiniteMeasure μ.variation]
-- general norm cost. if pass to operation LB cost instead multiply C by it.
def compares (μ:VectorMeasure X E) (B:ℂ→L[ℝ] E→L[ℝ] ℂ)(a b:X→ℂ)(C:ℝ) : Prop := μ.Integrable a ∧ μ.Integrable b ∧ ‖μ.integral a B-μ.integral b B‖ ≤ C*μ.variation.real univ
include hB
variable [TopologicalSpace X] [OpensMeasurableSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
lemma owes {a b:X→ℂ}{C:ℝ}(ha:Continuous a)(hb:Continuous b)(hc:0≤C)(H:∀ x,‖a x-b x‖ ≤ C):compares μ B a b C := by
  have y: μ.Integrable a:= ha.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have z: μ.Integrable b:= hb.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨y,z,?_⟩; rw [← VectorMeasure.integral_sub y z]; exact (VectorMeasure.norm_integral_le_of_norm_le_const (f:=fun x=> a x-b x) (Eventually.of_forall H)).trans (by gcongr; exact mul_le_of_le_one_right hc hB)
omit hB
abbrev realPair := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ→L[ℝ] ℂ).flip
abbrev complexPair := ContinuousLinearMap.mul ℝ ℂ
lemma real_pair (x:ℂ)(y:ℝ) : realPair x y=y • x:= rfl
lemma real_budget : ‖realPair‖ ≤ 1:= (ContinuousLinearMap.opNorm_flip _).trans_le ContinuousLinearMap.opNorm_lsmul_le
lemma complex_pair (x y:ℂ) : complexPair x y=x*y:= rfl
lemma complex_budget : ‖complexPair‖ ≤ 1:= (ContinuousLinearMap.opNorm_mul ..).le
section World
variable (N : WilsonPrescription G) {sim : G.Simple}(ν:ℝ)(M: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ: Prescription (Press.portDeck G)} {dial:Bool}(H: Main.Match N sim M σ dial)
variable {K:Set (Points n)}{S:Set (Points m)}{C:Set E4}{W L:ℝ}
    (hW:1≤W)(hk:IsCompact K)(hx:K⊆conf n)(hs:IsCompact S)(hy:S⊆ Outside m)(ha:clears W K S)(hL:0≤L)
local notation "VK" => Scale.Measure.outlook N.scheme N.criterion
local notation "Y" => GroupS.gaugeN N.scheme N.criterion M ν
-- E=ℂ (or ℝ for real signed), use e.g. `real_budget` or `complex_budget`.
-- Include common center (both positions relative to its frame; no estimator changes of variables).
include H hd he hh hk hx hs hy hW ha hL hB
lemma profile {t:ℝ→ℝ} (p:ℕ) (paid:Calibrated G t) : ∃ C':ℝ,0<C' ∧ ∃ a:ℕ, ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T≥W,
    ∀ u∈Balls L G d, ∀ v∈ Balls L G e, ∀ C:Set E4, IsCompact C → ∀ μ: VectorMeasure (↥C × ↥K × ↥S) E, IsFiniteMeasure μ.variation →
      compares μ B (fun i=> crop p (t r) (measurement VK Y hd he i.2.1.val (T • i.2.2.val) (-Real.log T) u v))
        (fun i=> crop p (t r) (center VK Y he (T • i.2.2.val) hh (-Real.log T) (purchased VK u i.2.1.val h p (t r)) v))
        (C'*((T⁻¹)^(h+1)+g0 G r^(p+1))*(1+Real.log T)^a) := by
  obtain ⟨F,hF,k,L'⟩:= M2 N ν M H hd he hh hL hk hx hs hy hW ha paid p
  refine ⟨F,hF,k,?_⟩; filter_upwards [L',g0_pos sim] with r H' hp' T ht u hu v hv C hC μ h'
  haveI:= isCompact_iff_compactSpace.mp hk; haveI:= isCompact_iff_compactSpace.mp hs; haveI:= isCompact_iff_compactSpace.mp hC
  let Z:= ↥C × ↥K × ↥S; let x(i:Z):=i.2.1.val; let y(i:Z):=i.2.2.val
  have hZ(i):=ha T ht (x i) i.2.1.property (y i) i.2.2.property; have he':= Real.log_nonneg (hW.trans ht); have hp:=zero_lt_one.trans_le (hW.trans ht)
  obtain ⟨s,S⟩:= rows_cont hd he hh ((H.dilation ν).check) ((H.separatedOPE ν).wilson) continuous_const (x:=x) (by unfold Z x; fun_prop) (y:=y) (by unfold Z y; fun_prop) (fun _=> hp) (u:=fun _=>u) (v:= fun _=>v) (fun _ _=> continuous_const) (fun _ _=> continuous_const) hZ (fun i=> hy i.2.2.property) (fun i=>hx i.2.1.property) p (fun _=>t r) continuous_const
  exact owes μ B hB s S (by positivity) (fun i=> H' T ht (x i) i.2.1.property (y i) i.2.2.property u hu v hv)
end World
end YM.FVA2.GradedFar259.Assay
