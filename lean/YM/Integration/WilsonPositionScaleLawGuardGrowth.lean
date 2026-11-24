import YM.Integration.WilsonPositionScaleLawGuardQuadratic
import YM.Integration.WilsonPositionScaleLawGuardOrbit

/-! Every homogeneous grade advances at its genuine engineering speed on the same two-home interval. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardGrowth
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedTransport (dressed)
open WilsonPositionScaleLawWholeHome (physical)
open WilsonPositionScaleLawGuardOrbit (size charge)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Classical Asymptotics

theorem allRatios {p:ℝ×Ratio→Prop}(h:∀ᶠz in sweep,p z):∀ᶠr in trail,∀t:Ratio,p (r,t):=by
  obtain ⟨u,hu,v,hv,joined⟩:=Filter.eventually_prod_iff.mp h
  exact hu.mono fun r hr t=>joined hr (Filter.eventually_top.mp hv t)

variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field
local notation "gθ"=>kinetic Z F J
include H in
theorem original (d:ℕ)(funded:Coupling G (kinetic Z F J))(law:WilsonPositionScaleLawGuardLittle.scale F J Z M ν d 2):
    ∃A:ℝ,0≤A ∧ ∀ᶠr in trail,∀t:Ratio,∀O:S.Field d,
      size R.family (physical F J Z d (t.val*r) O)≤(1+A*(gθ r)^2)*size R.family (physical F J Z d r O):=by
  let I:=ContinuousLinearMap.id ℂ (E d)
  letI :NormedAddCommGroup (E d→L[ℂ]E d):=ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨K,hK,fit⟩:=WilsonPositionScaleLawGuardQuadratic.original Z M H ν F J d law
  let p:=charge R.family d
  have hp:0≤p:=WilsonPositionScaleLawGuardOrbit.chargePos R.family d
  let C:=p*K
  have hc:0≤C:=mul_nonneg hp hK
  have zero:Tendsto (fun z:ℝ×Ratio=>gθ z.1) sweep (𝓝 0):=(funded.conforms hG).comp tendsto_fst
  have limit:Tendsto (fun z:ℝ×Ratio=>C*(gθ z.1)^2) sweep (𝓝 0):=by simpa only [zero_pow (by decide : 2≠0),mul_zero] using (tendsto_const_nhds (x:=C)).mul (zero.pow 2)
  have cap:∀ᶠz:ℝ×Ratio in sweep,C*(gθ z.1)^2<1/2:=(tendsto_order.mp limit).2 _ (by norm_num)
  refine ⟨2*C,mul_nonneg (by norm_num) hc,allRatios (p:=fun z=>∀O:S.Field d,
    size R.family (physical F J Z d (z.2.val*z.1) O)≤(1+(2*C)*(gθ z.1)^2)*size R.family (physical F J Z d z.1 O)) ?_⟩
  filter_upwards [fit,cap] with z fee small O
  let U:=dressed Z F J d z.1 z.2
  let y:=physical F J Z d (z.2.val*z.1) O
  let x:=physical F J Z d z.1 O
  have bound:p*‖U-I‖≤C*(gθ z.1)^2:=(mul_le_mul_of_nonneg_left fee hp).trans_eq (mul_assoc _ _ _).symm
  have paid:size R.family y≤(1+2*(p*‖U-I‖))*size R.family x:=WilsonPositionScaleLawGuardOrbit.absorb
    (WilsonPositionScaleLawGuardOrbit.sizePos R.family y) (mul_nonneg hp (norm_nonneg _)) (bound.trans small.le)
    (WilsonPositionScaleLawGuardOrbit.original F J Z z.1 z.2 O)
  calc _≤(1+2*(p*‖U-I‖))*size R.family x:=paid
       _≤(1+2*(C*(gθ z.1)^2))*size R.family x:=mul_le_mul_of_nonneg_right
         (add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left bound (by norm_num : (0:ℝ)≤2))) (WilsonPositionScaleLawGuardOrbit.sizePos R.family x)
       _=_:=by ring

end YM.Integration.WilsonPositionScaleLawGuardGrowth
