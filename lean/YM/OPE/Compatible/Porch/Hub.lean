import YM.OPE.Compatible.Porch.Savoy
/-! # Prime and lamp -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Zeph
open Function Filter Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Matrix Bloch Precision Exterior Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra GaussianScore Metric Push Push.AbsoluteSums
variable {G:Gauge}{c f:Side}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Model
open Woody Next.Free Finset Work.F03 Progress.StationaryScenes AnalyticNext.QuarticMatch.Local
variable {t r R B b:ℝ}{m:ℕ}
variable {S:StepData c f} {F: Forest S.ratio} {k:S.Choices}
local notation "Q" =>(Bid.Dir G c × AxisChart G F)
namespace Dew
section
-- implicit here
variable {Y E:(Bid.Dir G c × AxisChart G F)→ℝ}{f' g:Site f→ (Bid.Dir G c × AxisChart G F)→ℝ}
lemma Pile.sumW (h:Pile S F r R t m Y f')(he:Pile S F r b t m E g): Pile S F r (R+b) t m (Y+E) (f'+g) :=by
        refine ⟨fun {x} hx=>?_,fun j x hx=> (h.meter j x hx).add (he.meter j x hx),fun i x hx k hy=>?_⟩
        · simp_rw[Pi.add_apply,h.pays hx,he.pays hx,sum_add_distrib]
        intro d c hh; simp only[Pi.add_apply]; rw [iteratedFDeriv_add_apply ((h.meter i x hx).of_le le_top) ((he.meter i x hx).of_le le_top),_root_.add_apply,add_mul]; exact (norm_add_le ..).trans (add_le_add (h.voice i x hx k hy d c hh) (he.voice i x hx k hy d c hh))
lemma Pile.up (h:Pile S F r R t m Y f')(he:R ≤ b)(ht:B ≤ r):Pile S F B b t m Y f':= ⟨fun {_} hv=>h.pays (hv.trans_le ht),fun i x hv=>h.meter i x (hv.trans_le ht),fun i x hv k hx=>(h.voice i x (hv.trans_le ht) k hx)|>.less he⟩
lemma Pile.humid (h:Pile S F r R t m Y f') {x:Q}(hx:‖x‖<r): Y =ᶠ[𝓝 x] ∑ j, f' j:=by
       filter_upwards [continuous_norm.continuousAt.tendsto.eventually (gt_mem_nhds hx)] with i hi; rw [h.pays hi,Finset.sum_apply]
lemma Pile.smokes (h:Pile S F r R t m Y f') {x:Q}(hx:‖x‖<r):ContDiffAt ℝ ω Y x := ContDiffAt.congr_of_eventuallyEq (by rw [show ∑ i,f' i=(fun x=>∑ i,f' i x) from funext fun _=> Finset.sum_apply ..]; exact ContDiffAt.sum (fun i _=> h.meter i x hx)) (h.humid hx)
lemma Pile.dunk (h:Pile S F r R t m Y f') {x:Q}(hx:‖x‖<r)(k:ℕ):iteratedFDeriv ℝ k Y x=∑ i, iteratedFDeriv ℝ k (f' i) x:=by rw [(h.humid hx).iteratedFDeriv ℝ k|>.eq_of_nhds,iteratedFDeriv_sum_apply (fun i _=>(h.meter i x hx).of_le le_top)]
end
variable (P:Rep G f)(S F k)
section all
variable {p:Clip}{A:PathData G}(hk:S.patch.Branches S.kernel G) {s w u:ℝ}
variable (H:Sheds G S.patch S.kernel)
noncomputable def BoneC (A:PathData G) (p:Clip): Site f→ Q→ℝ:= (fun j=> Rotate.byStage p A j ∘ PinW S F G)+bandsP S F H
noncomputable def BoneL (A:PathData G):Site f→ Q→ℝ:= fun j=> byLoop A j ∘ PinW S F G
noncomputable def crownC {p:Patch}{K:KernelChoices}(Y:Sheds G p K)(s w:ℝ) (u:Clip)(m:ℕ):ℝ:=max 0 (dues G s w u m + ∑ i: Axis, fieldCost Y i (down s m) m)
noncomputable def leafC (G:Gauge)(s:ℝ)(i:ℕ):ℝ:=max 0 (Real.exp (2* down s i)^i*nearCost G i s 1)
lemma leafPay (h:A.Bounds p s w u): Pile S F H.b (leafC G s m*u) (down s m) m (fun x:Q=> springF F A x.2) (BoneL S F A):=by
        have hx:0≤u:=(tsum_nonneg h.two.1).trans h.two.2.2; apply Pile.up (got S F p A h).2 _ H.cap.le; exact (show _≤ Real.exp (2* down s m)^m*nearCost G m s 1*u from le_of_eq (by unfold nearCost;ring)).trans (mul_le_mul_of_nonneg_right (le_max_right ..) hx)
include hk
lemma crownPay (h:A.Bounds p s w u):
    Pile S F H.b (crownC H s w p m) (down s m) m (pane F k p A) (BoneC S F H A p):=by
        have hp := Bandage S F H hk (down_pos m h.width) k (m:=m); exact (((got S F p A h).1.up le_rfl H.cap.le).sumW hp).up (le_max_right ..) le_rfl
end all
end Dew
end YM.OPE.Zeph
