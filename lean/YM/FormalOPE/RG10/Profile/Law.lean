import YM.FormalOPE.RG10.Profile.Gather
import YM.FormalOPE.RG10.Position.Columns
/-!
# Arbitrary-horizon/test **continuum unit insertion law** for the WilsonX formal system
Given the supplier inputs in `Patience`; no extra interchange, tunable support rate, factorized
test family or pointwise-kernel hypothesis. Note the limits needed (this does NOT give the analogous
claim for an actual spectrum/correlation family). Approach: pick one sufficiently late
controller, but *also in a Baire frequent set* such that changing the tested profile with epoch
costs $o(1)$. This disposes of the exact mesh-dependent `ε^4`-sum marginal. Export also after
constant triangular change. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Profile
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
    Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle
    InversionTop LatticePT Lattice Grid FlatFeed RG10.Position RG10.Position.Grade
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{n d:ℕ}{P : Plan F}{Y: Drivers}(Z:Patience P Y)
variable (t: Test (n+1))(u: Fin n → Deck F d)
local notation "τ" => TestFunction.ofSupportedInCLM ℝ (safe t)
local notation "X" => task (marginal t) u
local notation "X'" => task t (Fin.cons (Deck.start F d) u)

/-- Test on unit: margin before the fixed length-one mass independence adjustment. -/
theorem forwards : Z.Yield X'= Z.Yield X := by
 ext k:1
 let E:= ContDiffMapSupportedIn (Points n) ℂ ⊤ (loose t)
 haveI : BaireSpace E := toll ..
 let A (q:ℕ+)(m):= (counted P q m k u).comp (τ)
 have hv : ∃ᶠ q in Y.ages, Calm A q := by
    apply bargaining _ (T:=fun a:E=> coeff k (Z.Yield (task (τ a) u))) (L:=Y.ages) (fun a=>?_ )
    unfold A; simp_rw [ContinuousLinearMap.comp_apply, close]; exact Z.collected _ k
 obtain ⟨q,hc,hq,h₁,h₂⟩:= (hv.and_eventually (Y.big.and ((Z.collected X k).and (Z.collected X' k)))).exists
 apply tendsto_nhds_unique h₂
 let μ:= fleece t
 have hm : Tendsto (fun i=> purse (q:=q) (wool t) i - μ) atTop (𝓝 0):= by simpa only [μ,sub_self] using (dried t hq).sub (tendsto_const_nhds (x:=fleece t))
 have H := hc _ hm
 simp_rw [_root_.map_sub, A, ContinuousLinearMap.comp_apply, close] at H
 change Tendsto (fun i=> coeff k (Plan.collect F P q i d (task (takings t q i) u))-coeff k (Plan.collect F P q i d X)) atTop (𝓝 0) at H
 simpa only [sub_add_cancel, zero_add, ← collect_unit P q _ t u Z.certified]
    using! (H.add h₁)

lemma zero_fields (t: Test 0)(u: Fin 0→ Deck F d) : Z.Yield (task t u)= C (t 0).re := by
 apply (Z.collected (task t u)).accepts; simp_rw [collect_vac]; exact Drivers.Credit.permanent _
variable (R:Rails F)

lemma graded : R.adjust Z d X'=R.adjust Z d X := by
 exact without t (Z.Yield (d:=d)) _ _ u _ (fun i=> by rw [R.leaves_unit, Matrix.one_apply]; by_cases h:i=Deck.start F d <;> simp [h,eq_comm]) (fun i=> forwards Z t i)
lemma dim_zero (u:Test 0)(v:Fin 0→ Deck F d): R.adjust Z d (task u v)= C (u 0).re := by rw [Grade.Rails.adjust, empty, zero_fields]
end YM.FormalOPE.RG10.Profile
