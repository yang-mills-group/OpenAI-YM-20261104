import YM.OPE.Compatible.Parch.Bills
import YM.OPE.Compatible.Melon.Stud
import YM.Next.STATIONARY.Joint.Gauge
import YM.OPE.Compatible.Frog.Gall
/-!
# Leading linear action. Surface currents
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Claw
open Function Filter Set Lattice Laurent Wilson RG Matrix Precision Cascade
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance Merchant Stand
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
variable {D V:Type}
local notation "E!"=>Libra.Keys G D
variable (R:Cascade.Score D V)
noncomputable def gillS : (V→G.Color) →ₗ[ℝ] E!:={
       toFun v i := v (R.inn i)-v (R.out i)
       map_add' x y := by funext i; simp only[Pi.add_apply]; abel
       map_smul' x y:=by funext i; simp only [Pi.smul_apply,smul_sub,RingHom.id_apply]
}
variable [Fintype D]
structure LevelA (p:E!→ℝ) :Prop where
       tilts :∀ x v,p (x+gillS R v)=p x
       inherits :∀ y g,p (glint D g y)=p y
section tracks

lemma gTrack (R:Cascade.Score D V) (x:Libra.Keys G D) (v:V → G.Color) : ∃ (y:ℝ→ E!) (s:ℝ→ Libra.Tile G V), R.Track (fun t:ℝ=> t • x) y s ∧ HasDerivAt y (x+gillS R v) 0:=by
       let f(t:ℝ)(i:V):= G.lieExp (t • v i); let u(t:ℝ):= put (t • x:E!); let z(t:ℝ):= R.dress (f t) (u t)
       have he(i:V): f 0 i=1:=by simp [f]
       have hz:z 0=1:=by funext i; unfold z Cascade.Score.dress u; rw [he,he,zero_smul,put_zero];simp
       have hs(i:V):Continuous (fun x=>f x i):= G.lieExp_cont.comp (show Continuous (fun x:ℝ=>x • v i) by fun_prop)
       have hC:Continuous z:= continuous_pi fun i=> (((hs _).mul ((continuous_apply i).comp (putC.comp (show Continuous (fun t:ℝ=>t • x) from continuous_id.smul continuous_const)))).mul (hs _|>.inv))
       have ht(i:V):ContDiff ℝ ω (fun t=> G.mat (f t i)):=G.exp_jet.comp (contDiff_id.smul contDiff_const)
       have hZ(i:D):ContDiffAt ℝ ω (fun t=> G.mat (z t i)) 0:=by
          unfold z Cascade.Score.dress; simp only [G.mat_mul,G.mat_inv]; have hx:ContDiffAt ℝ ω (fun t:ℝ=>G.mat (u t i)) 0:= G.exp_jet.contDiffAt.comp (f:=fun t:ℝ=>t • x i) 0 (by fun_prop); exact (((ht _).contDiffAt).mul hx).mul ((starL' ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ (ht _|>.contDiffAt))
       let y:=fun i=>unput (z i); refine ⟨y,f,⟨contDiffAt_id.smul contDiffAt_const,contDiffAt_pi.mpr fun i=>?_,zero_smul ..,by rw [show y 0=unput (z 0) from rfl,hz,unput_one],?_ ,fun i=>(ht i).contDiffAt.of_le le_top⟩,hasDerivAt_pi.mpr fun i=>?_ ⟩
       · exact ((show ContDiffAt ℝ ω G.plog (G.mat (z 0 i)) from (by rw[hz];exact G.plog_diff)).comp (f:=fun t=> G.mat (z t i)) 0 (hZ i)).of_le le_top
       · exact ((show Tendsto z (𝓝 0) (𝓝 1) from hz ▸ hC.tendsto 0).eventually Stand.sphere).mono fun i hi=>hi.symm
       have ht:HasDerivAt (fun t:ℝ=> G.mat (z t i)) (G.colorMat (x i+gillS R v i)) 0:=by
           unfold z Cascade.Score.dress; simp only[G.mat_mul,G.mat_inv]
           have h(a:V):HasDerivAt (fun t=> G.mat (f t a)) (G.colorMat (v a)) 0:=Stationary.exp_ray (v a)
           convert! ((h (R.inn i)).mul (show HasDerivAt (fun t=> G.mat (u t i)) (G.colorMat (x i)) 0 from Stationary.exp_ray ..)).mul ((h (R.out i)).star) using 1
           have hu: u 0 i=1:=by unfold u;simp
           simp only[hu,he,G.mat_one,mul_one,one_mul,Pi.mul_apply,G.colorMat_skew, star_one,map_add]; change _+ G.colorMat (_-_)=_; rw[map_sub]; abel
       exact YM.Stationary.ray_recall (by rw[hz];rfl) ht
-- germ ξ
private lemma Aux {f:ℝ→ E!}{b:E!}(hx:f 0=0)(he:HasDerivAt f b 0): Tendsto (fun i:ℝ=> i⁻¹ • f i) Tested.germ (𝓝 b):=by
       have hh:=hasDerivAt_iff_tendsto_slope.mp he; rw [show slope f 0=(fun i:ℝ=> i⁻¹ • f i) from funext (fun i=> by rw [_root_.slope_def_module,hx,sub_zero,sub_zero])] at hh; exact hh.mono_left (nhdsWithin_mono _ (by simp))

lemma LinearBell {p:ScriptJ E!}(h:R.Marbles p)(i:Phase)(he:∀ j < i,∀ x,(p x).seq j.val=0): LevelA R (fun x=>(p x).seq i.val):=by
        constructor
        · intro x v; obtain ⟨y,s,hp,hx⟩:=gTrack R x v; exact (Cascade.Grid.landP h hp (Cascade.Grid.slopeX _) (Aux hp.gy hx) i he).symm
        intro y g; let Y:= glint _ g y; have ht:R.Track (fun t:ℝ=>t • y) (fun t:ℝ=>t • Y) (fun _ _=>g):=by
             refine ⟨contDiffAt_id.smul contDiffAt_const,contDiffAt_id.smul contDiffAt_const,zero_smul ..,zero_smul ..,?_ , fun _=>contDiffAt_const⟩
             exact Eventually.of_forall (fun t=>by rw[show t • Y=glint _ g (t • y) from (map_smul ..).symm,Glass.patchZ];rfl)
        exact (Cascade.Grid.landP h ht (Cascade.Grid.slopeX _) (Cascade.Grid.slopeX _) i he).symm
end tracks
lemma LevelA.rankY {p:E!→ℝ}(h:LevelA R p)(ht:ContDiffAt ℝ ω p 0)(k:ℕ): LevelA R (rank p k):=by
       let x(z:E!) : rank p k z= WardBin.leading k (fun t:ℝ=> p (t • z)):= (WardBin.leading_tensor z p (ht.of_le le_top)).symm; refine ⟨fun y v=>?_,fun y g=>?_⟩
       · rw[x,x]; apply congr_arg; funext t; rw [smul_add,←map_smul,h.tilts]
       rw [x,x]; apply congr_arg; funext t; rw[←map_smul,h.inherits]
end YM.OPE.Claw
