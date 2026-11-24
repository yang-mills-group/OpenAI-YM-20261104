import YM.OPE.Compatible.Glim.Dirt
/-! # On orbit edges. payout. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint
variable {n:Side}(H:Even n.val)(T:Plot H)(p:T.Free)(b:Bool)
local notation "E!"=> Keys G T.Free
local notation "L" => offZ H T
noncomputable abbrev tourH (s:Signed)(u:Site n):Body 1 n≃Body 1 n:= (driftB n).symm.trans ((StepData.sendBonds s u).trans (driftB n))
abbrev δH (s:Signed)(i:Body 1 n):Bool:= s.flip (axisEquiv.symm i.2)
lemma Yew (s:Signed)(u:Site n)(e:edgeV n): tourH s u (whiz e)=whiz (sendEdge s u e):=by change driftB n (StepData.sendBonds s u ((driftB n).symm (driftB n e)))=_; rw [Equiv.symm_apply_apply];rfl
lemma Yea (s:Signed)(i:edgeV n): δH s (whiz i) =s.flip i.2:= congr_arg _ (axisEquiv.symm_apply_apply i.2)
lemma tread (G:Gauge)(s:Signed)(u:Site n): shifts (G:=G) s u= Flick (tourH s u) (δH s) :=by
     ext1 v; ext1 i; obtain ⟨e,rfl⟩:= (driftB n).surjective i; rw [show (driftB n) e=whiz e from rfl,FlickP,Yew,Yea]; unfold shifts; rw [ContinuousLinearMap.pi_apply]; simp only [show axisEquiv.symm (whiz e).2=e.2 from axisEquiv.symm_apply_apply e.2]; split <;> rename_i h
     · rw [if_pos (by simpa only [Step.rotate,posDir,Bool.false_xor] using h)];rfl
     rw [if_neg (by simpa only [Step.rotate,posDir,Bool.false_xor] using h)]; rfl
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F]{f:Bid.Dir G n→F}
-- equivalent of bore. any compass
lemma StageP (h:ContDiffAt ℝ ω f 0) (hs:∀ s u,f∘ shifts s u=f)(z:Kv): ∀ᶠ x:E! in 𝓝 0,DColor (b.xor (dir H (Plate H T p z))) (whiz (Plate H T p z)) f (L x)=DColor b (whiz p.val.val) f (L x):=by
      let s:=axisK z; let u:=offset z n; have he:= Pmp (tourH s u) (δH s) b (whiz p.val.val) h; rw [Yew,Yea, ← tread, hs] at he; rw [show dir H (Plate H T p z)= _ from (show dir H _=s.flip p.val.val.2 from (by rw [Plate,stood H,dir_here]; simp [s]))]; filter_upwards [(show Tendsto (offZ H T (G:=G)) (𝓝 0) (𝓝 0) from (offZ H T).map_zero ▸ (offZ H T).continuous.tendsto _).eventually he] with x hx; rw [show shifts s u (L x) = L x from spins H z _] at hx; exact hx
lemma carried (h:ContDiffAt ℝ ω f 0) (hs:∀ s u,f ∘ shifts s u=f)(k:Kv):
    let V: Keys G T.Free→F:= (4:ℝ)⁻¹ • (f ∘ offZ H T);
    ∀ᶠ x in 𝓝 (0:Keys G T.Free),DColor b p V x=DColor (b.xor (dir H (Plate H T p k))) (whiz (Plate H T p k)) f (L x):=by
         intro V; let Y:= DColor b (whiz p.val.val) f; have he:(∀ᶠ x:Keys G T.Free in 𝓝 0,∀ z:Kv,DColor (b.xor (dir H (Plate H T p z))) (whiz (Plate H T p z)) f (L x)=Y (L x)):=eventually_all.mpr (fun z=>StageP H T p b h hs z)
         filter_upwards [he,dualX (G:=G) H T p b,(show Tendsto (offZ H T (G:=G)) (𝓝 0) (𝓝 0) from (offZ H T (G:=G)).map_zero ▸ (offZ H T (G:=G)).continuous.tendsto _).eventually (h.eventually (by simp))] with x hx ht hp
         have hv:= hp.differentiableAt (by simp); rw [hx]; ext1 v; change fderiv ℝ V x (lunge p b x v)=_; unfold V; rw [fderiv_const_smul (hv.comp x (offZ H T (G:=G)).differentiableAt), fderiv_comp x hv (offZ H T (G:=G)).differentiableAt, (offZ H T (G:=G)).fderiv]; change (4:ℝ)⁻¹ • (fderiv ℝ f (L x) (L (lunge p b x v)))=_; rw [ht,map_sum]; have he':∀ i:Kv,fderiv ℝ f (L x) (planet H T p b i x v)= Y (L x) v:= fun i=> DFunLike.congr_fun (hx i) v; simp_rw [he']; rw [Finset.sum_const,card_univ,kvCard,←Nat.cast_smul_eq_nsmul ℝ,smul_smul]; norm_num
end YM.OPE.Variance
