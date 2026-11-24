import YM.QuadraticLocal.Vacuum.Invoice
import YM.AllOrder.Burn.Camp
import YM.AllOrder.Carillon.Cargo
/-!
# Price the general old-E before the step by a weighted captain

Fuel uses a *real* multiplier, to preserve the relative factor; if the
incoming budget is exactly zero we can take another (large) multiplier.
The retired tilt is not a step or a vacuum change; only the rendezvous.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Burn
open Filter Function Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open PhysicalNext Repeat ConnectedActivityE6 Blaze Height Raw
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure Presented Oriented Till Floe
open AnalyticBridge VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {δ a b C ε t:ℝ}
set_option quotPrecheck false
local notation "v₁"=> fun (R:Rep G f) i=> R.activities.reg i|>.site
local notation "p₁"=> fun (R:Rep G f) i=> R.activities.reg i|>.support
local notation "E"=> fun(R:Rep G f) i=> R.activities.E i
variable {M:Set ℕ}{R:Rep G f}

abbrev fund (M:Set ℕ) (w:ℝ)(hw:1≤w): Multiplier:=⟨fun i=> if i∈M then 1 else w, fun i=> by split<;> first| rfl|exact hw⟩
private lemma stronger_license (h:Candor R.p R.activities M C δ) (ha:R.activities.Valid R.p a b) (w:ℝ)(hw:1≤w): (Raw.activist (fund M w hw) R).activities.Valid R.p (C+w*δ) b:= by
 obtain ⟨v,H,hv⟩:=h.sale; let g := (fund M w hw).weight; have hp i: 0≤ g i:= zero_le_one.trans ((fund M w hw).upkeep _); let v' i:=g i*v i; let p:=R.p; let T:= R.activities; let A:=activist (fund M w hw) R; have hf i : Fairness R.p (v₁ R i) (p₁ R i) (A.activities.E i) (v' i):= by
   have hP : Fairness p (v₁ R i) (p₁ R i) (R.activities.E i) (v i):= ⟨ha.regular.smooth i, H i, ha.regular.at_flat i, fun ht f=> ha.regular.vanish i ht _ _ ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩) ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩)⟩
   unfold v'; rw (occs:=.pos [1]) [← abs_of_nonneg (hp i)]; exact hP.scale _
 refine ⟨⟨fun i=> (hf i).ready,fun i=> (hf i).one,fun i hi=> (hf i).nth hi⟩,⟨ha.forced.sym,ha.forced.symtest,ha.forced.meas,ha.forced.meas_test,ha.forced.reads,ha.forced.reads_test,ha.forced.permit⟩, fun s b=> ?_, ⟨v',fun i=>(hf i).cap,?_⟩, ha.boundK ⟩
 · obtain ⟨Y,hY⟩:= h.town s b; refine ⟨⟨Y.ep,Y.kp,Y.reg_site,Y.reg_support,Y.forced_support,Y.forced_inventory,Y.forced_tests,fun i U=>?_,Y.valuesK⟩⟩; change g (Y.ep i)*E R (Y.ep i) U= g i*E R i _; rw [show g _ = _ from (show g (Y.ep i)=g i from (by unfold g fund; simp [hY i]))]; exact congr_arg _ (Y.valuesE i U)
 intro x; let T':=wallet p T v x; let f i:= if i∈M then T' i else 0; let h i:= if i∈ M then 0 else T' i; let F i:=f i+w * h i; have H: wallet p T v' x=F:= by
     ext i; unfold F wallet v' f g h T' fund; unfold wallet BudgetPoint.mass; dsimp only; split_ifs <;> simp [*,mul_left_comm]
 change SumBudget (wallet p T v' x) _; rw [H]; exact budget_plus (hv x|>.1) (budget_scale (zero_le_one.trans hw) (hv x|>.2))
-- apply the activation, as a majorant on the common signed calculation only
lemma steward {S:StepData c f}{T:Tube G S}{P:Teller G}(w:ℝ)(hw:1≤w) (hp:Intake P T t R) (h:Candor R.p R.activities M C δ)
    (he:C+w*δ≤ (Real.sqrt (betaF G t S.patch.L))⁻¹ ^ (11/5:ℝ)): Tollable (fund M w hw) P T t R:= by
 have hx:= stronger_license h hp.cap.labels w hw
 exact ⟨hp.ready,⟨hp.received.path,hp.received.clip,hp.received.temp⟩,⟨hp.cap.paths,{hx with boundE:=VerifiedReset.Time.E_rises hx.boundE he}⟩,hp.exponent,hp.height,hp.sizes,hp.window⟩
end YM.AllOrder.Burn
