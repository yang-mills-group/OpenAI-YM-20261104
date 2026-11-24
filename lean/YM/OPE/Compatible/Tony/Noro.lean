import YM.OPE.Compatible.Tony.Merk
/-!
# Root override analytic chart. Motion.Cartographer. v external preserve
in very deliberately (do not take plog of δU when no wrap wanted)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Ibis Merchant.SiteL Flume.Page StepsL Wool
variable {i j d k m r l b:ℕ}{n:Side}
local notation "D!"=> Bid.Dir G n
variable (h:Board n b)
lemma stemEye (x:Site n) (g:Gauge):stemL h (1:Config g n) x=1:=by
       unfold stemL; split;swap;· rfl
       rw [travel_at]; let A:Walk:=[]; have hz(p:Walk)(x:Site n): travel (1:Config g n) x p=1:=by rw[← Precision.link_one]; exact Push.stroll_zero ..
       apply hz
lemma herm_eye (G:Gauge): hermM h (1:Config G n)=1:=by funext x; unfold hermM; split; rfl; rw[stemEye,stemEye]; simp
variable (G)
noncomputable def Λace (x: Bid.Dir G n)(i:Body 1 n):G.Color:= if Trim b ((driftB n).symm i) then x i else G.plog (G.mat (hermM h (represent x) ((driftB n).symm i)))
variable {G}
lemma vane_i (x:D!)(i:Edge (Site n)):Λace G h x (arkE i)= if Trim b i then x (arkE i) else G.plog (G.mat (hermM h (represent x) i)):=by unfold Λace; rw [show (driftB n).symm (arkE i)=i from (driftB n).symm_apply_apply i]
-- note parameter order.
lemma eΛ (G:Gauge): Λace G h 0=0:=by funext i; obtain ⟨i,rfl⟩:=arkSur i; rw [vane_i]; split; rfl; rw [link_one, herm_eye]; simp
lemma litV (x:D!)(i:Body 1 n)(he:pdist i.1 < b): Λace G h x i=x i:=by
       obtain ⟨q,hz⟩:=arkSur i; rw[←hz,vane_i,if_pos]; rw[← hz] at he; change pdist q.1 < b at he; exact ⟨he.le,(boulder q.2 q.1).2.trans he⟩ -- trans he is Nat succ
lemma sillSave (x:D!): sillM G n b (Λace G h x)=sillM G n b x:=by funext i; by_cases ht:pdist i.1 < b; rw[reveal _ _ ht, reveal _ _ ht,litV h x _ ht]; rw [fade _ _ (not_lt.mp ht),fade _ _ (not_lt.mp ht)]
section
-- paths on tor.
private lemma RepA (e:Edge (Site n))(g:Gauge): ContDiff ℝ ω (fun x:Bid.Dir g n=> g.mat (represent x e)):=by simp_rw[arkL]; exact g.exp_jet.comp (contDiff_apply ..)
private lemma rigAA (w:Walk)(x:Site n)(G:Gauge): ContDiff ℝ ω (fun y:Bid.Dir G n=> G.mat (travel (represent y) x w)):=by -- G potential binder
      induction w generalizing x with
      | nil=>exact contDiff_const
      | cons a w ih=>simp only[travel,G.mat_mul]; refine ContDiff.mul ?_ (ih _); unfold Step.read; split; exact (show ContDiff ℝ _ (fun x:Bid.Dir G n=> star (G.mat (represent x (a.used _)))) from (starL' ℝ:G.Mat≃L[ℝ] G.Mat).contDiff.comp (RepA _ G)); exact RepA _ G
lemma hubT (U:Site n)(g:Gauge): ContDiff ℝ ω (fun x:Bid.Dir g n=> g.mat (stemL h (represent x) U)):=by unfold stemL; split; simp_rw [travel_at]; exact rigAA _ _ g; exact contDiff_const
lemma Wheat (i:Edge (Site n))(g:Gauge): ContDiff ℝ ω (fun x:Bid.Dir g n=> g.mat (hermM h (represent x) i)):=by unfold hermM; split; exact RepA i g; simp only[g.mat_mul,g.mat_inv]; exact ((starL' ℝ: g.Mat≃L[ℝ] g.Mat).contDiff.comp (hubT h i.1 g)).mul (hubT h _ g)
lemma haloStage (G: Gauge):ContDiffAt ℝ ω (Λace G h) 0:=by
       refine contDiffAt_pi.mpr (fun i=>?_); unfold Λace; split; exact (contDiff_apply ℝ G.Color i|>.contDiffAt)
       next hp => exact (show ContDiffAt ℝ ω G.plog _ from (show ContDiffAt ℝ ω G.plog (G.mat (hermM h (represent (0:Bid.Dir G n)) ((driftB n).symm i))) from by rw [link_one,herm_eye];exact G.plog_diff)).comp (f:=fun x=> G.mat (hermM h (represent x) _)) 0 (Wheat h _ _).contDiffAt
lemma Sphere (G:Gauge):represent ∘ Λace G h=ᶠ[𝓝 0] hermM h ∘ represent:=by
       let p(v:Bid.Dir G n):= hermM h (represent v); have hv:p 0=1:=by unfold p;rw [link_one,herm_eye]
       have he(e:Edge (Site n)):∀ᶠ i in 𝓝 (0:Bid.Dir G n),represent (Λace G h i) e=p i e:=by
            have ht' : ContinuousAt (fun x=>p x e) (0:Bid.Dir G n):= ((G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff).2 (Wheat h e G).continuous.continuousAt
            have ht : Tendsto (fun x=>p x e) (𝓝 0) (𝓝 1):= by simpa only[hv] using! ht'.tendsto
            by_cases he : Trim b e
            · filter_upwards with i; rw [arkL,vane_i,if_pos he]; exact (arkL G i e).symm.trans (if_pos he|>.symm) -- G param?
            filter_upwards [ht.eventually G.plog_right] with i hi; rw[arkL,vane_i,if_neg he]; exact hi
       filter_upwards [eventually_all.mpr he] with i hi; exact funext fun j=> hi j
end
end YM.OPE.Merchant
