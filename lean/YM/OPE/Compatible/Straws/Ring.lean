import YM.OPE.Compatible.Straws.Yu
/-!
# Jet calculus along small paths of coarse parameters
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
local notation "Lf" => Tested.germ
open Radial ScriptJ JetS
namespace Adhesion
open Radial Arc Gael
variable [FiniteDimensional ℝ E]
lemma retire {q:E→ℝ}(h:Continuous q){a:ℝ→E→ℝ}{p:ScriptJ E}(hp:Bears q a p){x:ℝ→E}(ht:Gael x): Reads (fun i=> a i (x i)) (mine (p ∘ x)):=by
     apply ((Fitted.arose x p ht hp.toll).take).clash; obtain ⟨ε,c,r,he,hc,hk⟩:= hp.slope.cost; rw [← neg_sub]; apply IsBigO.neg_left; let u:=(trill x).s; let z:=(Radial.zone (E:=E)).w; let B:= z u+1; let W:= q u+1; have H:Tendsto x Lf (𝓝 u):= (Gael.oath ht).limit; have hb: z u<B:= lt_add_one _; have hB : 0<B:=lt_of_le_of_lt (zero_le_one.trans (Radial.zone.high u)) hb; have hz:Continuous z:= continuous_const.add continuous_norm; have hw:0≤W:=le_trans (zero_le_one.trans (hp.slope.envelope u)) (lt_add_one _).le
     rw [Reads.isTariff]; refine ⟨c*B^r*W,mul_nonneg (mul_nonneg hc (by positivity)) hw,?_⟩; filter_upwards [Tested.eventually_small (show 0<ε/B by positivity), (hz.continuousAt.tendsto.comp H).eventually (gt_mem_nhds hb),(h.continuousAt.tendsto.comp H).eventually (gt_mem_nhds (lt_add_one _))] with i hi (hi': z (x i)< B) (hl:q (x i)<W)
     apply (hk (x i) i hi.1 ((mul_le_mul_of_nonneg_left hi'.le hi.1.le).trans ((le_div_iff₀ hB).mp hi.2.le))).trans; apply mul_le_mul_of_nonneg_right _ (pow_nonneg hi.1.le _); apply mul_le_mul _ hl.le (zero_le_one.trans (hp.slope.envelope _)) (by positivity); gcongr; exact zero_le_one.trans (Radial.zone.high _)
abbrev GateT (f w:E→ℝ):ScriptJ E:=(Pawn.mold w 0)*wheel (Pawn.mold f 2)
def Curling (f w:E→ℝ)(x:E):Token:= plainJ (w 0)⁻¹ * GateT f w x
lemma gearE {f w:E→ℝ}(h: Radial.Stationary f)(hy:ContDiffAt ℝ ∞ w 0): ScriptJ.B (GateT f w):= height (Pawn.calm hy).toll (heightens _ (Pawn.trio h).toll)
lemma curlingB {f w:E→ℝ}(h:Radial.Stationary f)(hy:ContDiffAt ℝ ∞ w 0): ScriptJ.B (Curling f w):= height (p:=fun _:E=> plainJ (w 0)⁻¹) (Stranded.Bfray _) (gearE h hy)
omit [FiniteDimensional ℝ E] in
lemma curT {f w:E→ℝ}(h:0<w 0)(x:E):(Curling f w x).s=1:=by unfold Curling GateT; rw [JetS.ml_s,plain_s,Pi.mul_apply, JetS.ml_s]; change _*(jet _ 0 x*1)=_; rw [jet_zero,mul_one]; exact inv_mul_cancel₀ h.ne'
def Flame (f w:E→ℝ)(t:ℝ)(x:E):= (w 0)⁻¹ *insertion f w t x
lemma cooking {f w:E→ℝ}(h:Radial.Stationary f)(hy: ContDiffAt ℝ ∞ w 0){x:ℝ→E}(hx:Gael x): Reads (fun i=> Flame f w i (x i)) (mine (Curling f w ∘ x)) :=by
     have hp: ContDiffAt ℝ ∞ w 0:= hy; have hb : Bears (shade 1) (insertion f w) (GateT f w):=by simpa only [one_mul] using! (Pawn.calm hp).ascent (spender one_pos h)
     let q:E→Token:= fun _=> plainJ (w 0)⁻¹
     rw [show Curling f w ∘ x=(q∘x)*(GateT f w ∘ x) from rfl, Fitted.slopes (p:=q∘x) (q:=GateT f w ∘ x) ( Fitted.arose x q hx (Stranded.Bfray _)) (Fitted.arose x _ hx hb.toll),show mine (q∘x)=q 0 from Gael.chooses (Reads.selves _)]
     apply (Reads.constants _).pile; exact (retire (by unfold shade;fun_prop) hb hx)
-- Lid
variable {I:Type}[Fintype I]{G:Gauge}(L:Lid G I)(u:Keys G I){P:ChartRatio G}(R:LocalRatio P)
abbrev Gτ(_:ℝ):Keys G I:=u
include R
lemma Waterfall : Reads (fun x:ℝ=> Flame L.f (warmer P L.w) x u) (L.hat P u):=by
     let A:=Gτ u; let a:= Curling L.f (warmer P L.w); have h := cooking L.F (L.winds P R) (x:=A) (show Gael A from Exists.intro _ (Reads.constants _)); change Reads _ (mine (a∘A)) at h; rw [show mine (a∘A)=a u from Gael.chooses (Reads.selves (a u))] at h; exact h
end Adhesion
end YM.OPE.Libra
