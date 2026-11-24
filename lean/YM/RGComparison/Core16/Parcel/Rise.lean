import YM.RGComparison.Core16.Lumen.Project
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Affine
import YM.Push.PRICE_COMPILER.Compiler
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
/-!
# Construct actual Planet: fixed-count catalogue BEFORE period
Uses larger-torus encoding to supply analytic estimates (prices AFTER ratio & patch). Hypothesis
not that larger torus actual kinetic path agrees; the parent is a true Wilson top seam and only its
bare stencil costs are used here. Observer stencils charged afterward. Analytic completion arbitrary
off germ, not assigned or affecting actual β.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Parcel
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Matrix
open Lumen Lumen.Planet PertExtension PertExtension.Series Tested Radial Therm
open Forge Forge.Hut AnalyticNext.ConnectedActivity Precision Exterior Push Push.BetaTransport Push.GridApprox Finset
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {ι:Type} {H:Patch}{K:KernelChoices}

-- Any such WORKSHOP chosen after P,K, before scale clocks p. Keep one through calibration proof.
structure Oven (P:Patch) where
    roof : Side
    floor : Side
    tiles : floor.val=roof.val*P.L.val
    odd_width : 1<roof.val
    house : 2*Hut.width P<floor.val
namespace Oven
lemma builtafter (P:Patch): Nonempty (Oven P) := by
    let r : Side:=⟨2+2*Hut.width P,(by omega)⟩; refine ⟨⟨r,r*P.L,rfl,(by change _<2+2*Hut.width P; omega),?_⟩⟩; exact lt_of_lt_of_le (show _<r.val by change _<2+2*Hut.width P; omega) (le_mul_of_one_le_right (Nat.zero_le r.val) P.L.property)

variable (P: Oven H)
def stance (K : KernelChoices): StepData P.roof P.floor:= ⟨H,K,P.tiles⟩
abbrev Xways := Edge (Site P.floor) -- actual encoding stencil to be supplied before period
abbrev Form (G:Gauge):= Shelf G (PlaqAxes ⊕ Axis) P.Xways

local notation "S"=> P.stance K
variable {V: PathData G}
def logs (u:Point G P.Xways) : Push.In G P.floor := Aff.form (fun b=> Lumen.axis.symm (u.2 b))
def lamp (u:Point G P.Xways): Config G P.floor:= fun b=> launch (u.2 b)
lemma lamp_eq u: P.lamp (G:=G) u= represent (P.logs u):=by unfold lamp logs represent; rw [Aff.collect_form]; funext i; unfold increment; rw [Pi.one_apply,mul_one]; rfl
lemma logs_zero : P.logs (0:Point G P.Xways) = 0:= funext fun _=> axis_zero
@[simp] lemma lamp_zero : P.lamp (0:Point G P.Xways)=1:= funext fun _=> launch_zero
lemma logs_hot : ContDiffAt ℝ ω (P.logs (G:=G)) 0:=by apply contDiffAt_pi.mpr; intro i; exact (axis_hot (G:=G)).comp (f:=fun u : Point G P.Xways=> u.2 (i.1,axisEquiv.symm i.2)) _ ((contDiff_apply ℝ _ _).contDiffAt.comp _ contDiffAt_snd)

def boom (a:PlaqAxes)(x:Point G P.Xways):= G.price (faceValue (P.lamp x) ((hold S 0 : Site P.floor),a)) -- use stance K in def? K implicit
-- big tag Book (before covering). Anchor ℓ depending K but hold S ratio independent
-- classical.arbitrary ok after postL

def tor (p:Axis)(t:(P.stance K).Choices)(x:Point G P.Xways):= linkEnergy S (G.lieExp x.1*((S).prediction (P.lamp x) t (0,p))⁻¹)
def actual (P:Oven H)(K:KernelChoices) : PlaqAxes ⊕ Axis→ Point G P.Xways→ℝ:= Sum.elim (boom (K:=K) P) (fun p=>tor P p (Classical.arbitrary (P.stance K).Choices))
lemma boom_hot (a:PlaqAxes): ContDiffAt ℝ ω (boom (G:=G) (K:=K) P a) 0:=by
    unfold boom; apply Work.F03.price_smooth; simp_rw [lamp_eq]
    exact ((P.logs_zero.symm ▸ Push.writes (G:=G) ..)).comp (f:=P.logs) _ (P.logs_hot)
variable (h:H.Branches K G)
include h
lemma tor_hot (p:Axis)(t:(P.stance K).Choices): ContDiffAt ℝ ω (P.tor p t (G:=G)) 0:=by
    apply ContDiffAt.mul contDiffAt_const
    apply Work.F03.price_smooth (A:= fun u:Point G _ => G.lieExp u.1*(StepData.prediction S (P.lamp u) t (0,p))⁻¹)
    simp_rw [G.mat_mul,G.mat_inv,P.lamp_eq]
    have hx:= (Push.prediction_cont S h (0,p) t)
    exact (G.exp_jet.contDiffAt.comp (f:=Prod.fst) (0:Point G P.Xways) contDiffAt_fst).mul ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp (f:=fun i=>_) _ ((P.logs_zero.symm ▸ hx).comp (f:=P.logs) _ P.logs_hot))
lemma actual_hot i: ContDiffAt ℝ ω (P.actual (G:=G) K i) 0:=Sum.rec (motive:=fun i=>ContDiffAt ℝ ω (P.actual (G:=G) K i) 0) (fun k=> boom_hot P k) (fun k=> tor_hot P h k _) i
lemma zero (i): P.actual (G:=G) K i 0=0:=by cases i; exact (by simp [actual,boom,Progress.DirectedRecipe.face1]); next => simp [actual,tor,linkEnergy,Push.settled S h]
omit h in
lemma nn (x:Point G P.Xways)i:0≤P.actual K i x:=by cases i; exact (G.price_range _).1; exact (link_estimate S).nonneg _

-- budget window to charge ALL uses, incl siteMass(t) over ANY s0. Also syntax for the joint
-- analytic value of bond cost in arbitrary t (put SAME near-min t). Works germ relative P.floor
-- then project locally to real query. Room occupancy K untouched.
structure Bright (x:Point G P.Xways):Prop where
    stores (i:Site P.roof) u: H.frameMass K (expandAt (hold S i) (P.lamp x)) u=((Fintype.card H.FrameTag:ℝ))⁻¹
    conn (e:Edge (Site P.roof))(t:(S).SitesChoice) u : H.predictorMass K ((S).connector (P.lamp x) t e) u=((Fintype.card H.Points:ℝ))⁻¹
    same (t u:(S).Choices): (S).prediction (P.lamp x) t=(S).prediction (P.lamp x) u

lemma brighter : ∀ᶠ x:Point G P.Xways in 𝓝 0,Bright (K:=K) P x:=by
    let F:=Progress.StationaryScenes.frameField («S»:= S) h
    have ht:Tendsto (P.logs (G:=G)) (𝓝 0) (𝓝 0):= P.logs_zero ▸ P.logs_hot.continuousAt.tendsto
    filter_upwards [ht.eventually F.roots] with t ht
    refine ⟨fun i u=> ?_,fun i v t'=>?_,fun v w=>?_⟩
    · rw [lamp_eq]; exact if_pos (ht.1 i).1
    · rw [lamp_eq]; exact if_pos ((ht.2 (v,Classical.arbitrary _)).2.2 i)
    rw [lamp_eq]; funext i; let U:=represent (P.logs t)
    have hw : (S).connector U v.1 i= (S).connector U w.1 i:=by
       funext p; unfold StepData.connector; rw [(ht.2 v).1, (ht.2 w).1,(ht.2 v).1, (ht.2 w).1]
    change StepData.prediction S U _ i=StepData.prediction S U _ i
    unfold StepData.prediction Patch.predict; rw [if_pos ((ht.2 v).2.2 i),if_pos ((ht.2 w).2.2 i),hw]
end Oven
end YM.RGComparison.Core16.Parcel
