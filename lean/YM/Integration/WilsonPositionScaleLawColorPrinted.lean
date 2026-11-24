import YM.Integration.WilsonPositionScaleLawColorChart
import YM.Integration.WilsonPositionPrescribedStability

/-! The independent finite MS fit on the actual, possibly asymmetric, position bank.
All trial coordinates range over a genuine neighborhood before the tests are read. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorPrinted
open Function Filter Set Asymptotics Spec Table Extraction OPE Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize MS MS.Land FVA2 FVA2.Arrival
open WilsonPositionPrescribedFormalTest (raw turn)
open WilsonPhysicalPositionDiscreteBranches (field)
open WilsonPositionScaleLawColorChart (conjugate)
open scoped Topology Classical BigOperators
variable {G:Gauge}{d:ℕ}
local notation "N" => MoveSpace G d

def painted (b:N)(P:Prediction G d):Prediction G d:=recruit (field b) P

theorem unpaint (a b:N)(back:field b ∘ₗ field a=1)(P:Prediction G d):recruit (field a) (painted b P)=P:=by
  rw [painted,recruits_comp,back];rfl

theorem rebase (a b:N)(inv:field a ∘ₗ field b=1)(back:field b ∘ₗ field a=1)(x:N)(P:Prediction G d):
    recruit (field x ∘ₗ field a) (painted b P)=recruit (field (conjugate a b x)) P:=by
  rw [WilsonPositionScaleLawColorChart.allArms a b inv,unpaint a b back]

def diagnostic (V:Store G)(P:Prediction G d):N:=guide G d ((V.measure d).D P)

theorem ground (V:Store G):(V.survey d).itinerary (V.survey d).opening=diagnostic V (reference G d):=by
  rw [Fray.opening,Fray.way,Fray.box,map_zero,stand0];rfl

variable (V:Store G)(ν:ℝ)(T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(q:ℕ)

theorem invariant (b:N)(same:∀k≤q,painted b (Reg.State.kernel ν T d k)=Reg.State.kernel ν T d k)(u:ℝ):
    painted b (raw ν T d q u)=raw ν T d q u:=by
  unfold painted WilsonPositionPrescribedFormalTest.raw
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul]
  exact congrArg (fun P=>(u:ℂ)^k.val • P) (same k.val (by omega))

theorem bill (a b:N)(inv:field a ∘ₗ field b=1)(back:field b ∘ₗ field a=1):
    ∃ L A:ℝ,0≤L ∧ 0≤A ∧ ∀ᶠz:ℝ×N in 𝓝 (0,0),
    ‖conjugate a b z.2-guide G d (turn V ν T d q z.1)‖≤
      L*‖diagnostic V (recruit (field z.2 ∘ₗ field a) (painted b (raw ν T d q z.1)))-diagnostic V (reference G d)‖+
      A*|z.1|^(q+1):=by
  let D:=V.survey d
  let u:=𝓝 ((0,0):ℝ×N)
  let target:=WilsonPositionPrescribedTariff.target V ν T d q
  have h0:target 0=D.opening.1:=WilsonPositionPrescribedTariff.anchored ..
  have hP:Tendsto (fun z:ℝ×N=>target z.1) u (𝓝 D.opening.1):=by
    rw [←h0];exact ((WilsonPositionPrescribedTariff.smooth V ν T d q).continuous.tendsto 0).comp continuous_fst.continuousAt
  have hx:Tendsto (fun z:ℝ×N=>conjugate a b z.2) u (𝓝 0):=
    WilsonPositionScaleLawColorChart.small a b continuous_snd.continuousAt
  have ht:Tendsto (fun z:ℝ×N=>guide G d (turn V ν T d q z.1)) u (𝓝 0):=by
    have hc:Continuous (fun z:ℝ×N=>guide G d (turn V ν T d q z.1)):=by
      simp only [turn,map_sum,map_smul];fun_prop
    have hzero:guide G d (turn V ν T d q 0)=0:=by simp [turn]
    rw [←hzero];exact hc.continuousAt
  obtain ⟨L,hL,hl⟩:=WilsonPositionPrescribedStability.residual D (V.prepared d) hP hx
  obtain ⟨K,hK,hk⟩:=WilsonPositionPrescribedStability.residual D (V.prepared d) hP ht
  obtain ⟨C,hC,book⟩:=WilsonPositionPrescribedFormalResidual.paid V ν T d q
  have small:∀ᶠz:ℝ×N in u,|z.1|≤1:=by
    have h:=((continuous_abs.comp continuous_fst).continuousAt (x:=((0,0):ℝ×N))).eventually_lt (g:=fun _=>1) (by fun_prop) (by simp)
    exact h.mono fun _ hz=>hz.le
  refine ⟨L,K*C,hL,mul_nonneg hK hC,?_⟩
  filter_upwards [hl,hk,small] with z hz kt room
  calc
    _≤‖D.route (V.prepared d) (target z.1)-conjugate a b z.2‖+
        ‖D.route (V.prepared d) (target z.1)-guide G d (turn V ν T d q z.1)‖:=by
      rw [norm_sub_rev (D.route (V.prepared d) (target z.1)) (conjugate a b z.2)]
      simpa only [dist_eq_norm] using dist_triangle (conjugate a b z.2) (D.route (V.prepared d) (target z.1)) (guide G d (turn V ν T d q z.1)) 
    _≤L*‖D.itinerary (target z.1,conjugate a b z.2)-D.itinerary D.opening‖+
        K*(C*|z.1|^(q+1)):=add_le_add hz (kt.trans (mul_le_mul_of_nonneg_left (book _ room) hK))
    _=_:=by
      rw [rebase a b inv back,ground,show target z.1=(V.survey d).purse (WilsonPositionPrescribedFormalTest.raw ν T d q z.1) from (WilsonPositionPrescribedFormalTest.menu ..).symm,Fray.way]
      simp only [←mul_assoc];rfl

end YM.Integration.WilsonPositionScaleLawColorPrinted
end
