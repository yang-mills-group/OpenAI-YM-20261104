import YM.Integration.WilsonPositionScaleLawGuardPhysical

/-! Real kinetic running controls both actual physical homes on the common
half panel, in advance of the independent finite polynomial comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardAges
open Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace
open OPE OPE.Orbits PhysicalNext.Repeat.Legato XSpace.Normalize
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedBudget (home)
open scoped Topology Classical
local instance half:WilsonPositionScaleLawWindow.RangeSpec:=⟨1/2,by norm_num⟩

theorem original {G:Gauge}{g:ℝ→ℝ}(hG:G.Simple)(funded:Coupling G g)(K:ℝ):
    ∀ᶠz:ℝ×Ratio in sweep,0<g z.1 ∧ 0<g (z.2.val*z.1) ∧ g (z.2.val*z.1)≤2*g z.1 ∧
      g z.1≤1 ∧ g (z.2.val*z.1)≤1 ∧ K*g z.1≤1:=by
  have zero:=funded.conforms hG
  have live:Tendsto (fun z:ℝ×Ratio=>g z.1) sweep (𝓝 0):=zero.comp tendsto_fst
  have newHome:Tendsto (fun z:ℝ×Ratio=>g (z.2.val*z.1)) sweep (𝓝 0):=zero.comp WilsonPositionScaleLawCompactNative.bothHomes
  have con:Tendsto (fun _:ℝ×Ratio=>K) sweep (𝓝 K):=tendsto_const_nhds
  have scaled:Tendsto (fun z:ℝ×Ratio=>K*g z.1) sweep (𝓝 0):=by simpa only [mul_zero] using con.mul live
  have ratio:=WilsonPositionScaleLawKineticRatio.signed hG funded
  filter_upwards [tendsto_fst.eventually funded.positive,WilsonPositionScaleLawCompactNative.bothHomes.eventually funded.positive,
    (tendsto_order.mp ratio).2 _ (by norm_num : (1:ℝ)<2),(tendsto_order.mp live).2 _ zero_lt_one,
    (tendsto_order.mp newHome).2 _ zero_lt_one,(tendsto_order.mp scaled).2 _ zero_lt_one] with z a b c f h j
  exact ⟨a,b,((div_lt_iff₀ a).mp c).le,f.le,h.le,j.le⟩

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    (Z:FVA2.Register.WilsonPrescription G)(hG:G.Simple)(lead:Leading F J)
    {Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)

include hG lead paid in
theorem operator (d:ℕ):∀ᶠz:ℝ×Ratio in sweep,‖home F J Z d (z.2.val*z.1)‖≤2:=
  (WilsonPositionScaleLawCompactNative.bothHomes.eventually
    (WilsonPositionScaleLawDressedBudget.two F J Z hG lead paid d)).mono
    (fun _ hi=>ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun v=>(hi v).2))

end YM.Integration.WilsonPositionScaleLawGuardAges
