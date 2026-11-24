import YM.MSbar.Lis.Aspire
import YM.MSbar.Rolling.Stays
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Aqua
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
local notation "A"=>G.Color
-- uniform chart in base angle. all real link inputs.
def Beam (G:Gauge)(D:ℝ): Prop:= ∀ x:G.Color, ‖x‖<D → ∀ b:Native.Chart.Rail G,
        ContDiffAt ℝ ω (Native.Chart.head G b) (0,x) ∧ (∀ᶠ u:ℝ×G.Color in 𝓝 (0,x), G.lieExp (Native.Chart.head G b u)=hit G b u.1 u.2)∧ Native.Chart.head G b (0,x)=x ∧ Injective (fderiv ℝ (Up G) x)
lemma beeps (G:Gauge) : ∃ D:ℝ,0<D∧ Beam G D:=by
   let F(b : Native.Chart.Rail G)(u:ℝ×G.Color):=hit G b u.1 u.2
   have he(b:Native.Chart.Rail G):Continuous (F b):=by
       unfold F Native.Chart.hit; apply Continuous.mul
       · exact (G.lieExp_cont.comp (continuous_fst.smul continuous_const)).mul (G.lieExp_cont.comp continuous_snd)
       exact G.lieExp_cont.comp (continuous_fst.smul continuous_const)
   have hk(b:Native.Chart.Rail G):ContDiff ℝ ω (fun u=>G.mat (F b u)):=by
       let L:=Up G; rw [show (fun u=> G.mat (F b u))=fun u=> L (u.1 • (-b.1))*L u.2*L (u.1 • b.2) from funext fun x=>by simp only [F,Native.Chart.hit,G.mat_mul];rfl]; exact ContDiff.mul (ContDiff.mul (G.exp_jet.comp (contDiff_fst.smul contDiff_const)) (G.exp_jet.comp contDiff_snd)) (G.exp_jet.comp (contDiff_fst.smul contDiff_const))
   have hp : Tendsto (fun i:G.Color=> G.lieExp i) (𝓝 0) (𝓝 1):=by simpa using G.lieExp_cont.tendsto 0 -- conversion
   have hx := G.plog_left.and ((armed G).and ((hp.eventually (eventually_eventually_nhds.mpr G.plog_right)).and (hp.eventually ((G.continuous_mat.tendsto 1).eventually ((G.plog_diff.eventually (by simp)))))))
   obtain ⟨r,hr,he'⟩:= Metric.mem_nhds_iff.mp hx
   refine ⟨r,hr,fun x hv b=>?_⟩; obtain ⟨hd,hy,hB,hA⟩:= he' (Metric.mem_ball.mpr (show dist x 0 < r from (dist_zero_right _).trans_lt hv)); have hs: F b (0,x)=G.lieExp x:=Native.Chart.still ..; have hA' : ContDiffAt ℝ ω G.plog (G.mat (F b (0,x))):=by rw [hs]; exact hA
   exact ⟨hA'.comp (f:=fun u=>G.mat (F b u)) (0,x) ((hk b).contDiffAt), ((show Tendsto (F b) (𝓝 (0,x)) (𝓝 (G.lieExp x)) from (by rw [←hs]; exact (he b).tendsto (0,x))).eventually hB),by simpa only [Native.Chart.head,F,hs,Native.Chart.still] using hd,hy⟩ -- fix
local notation "E"=>Positions (Primary n G)
local notation "Λ"=>Native.Chart.Rail G
variable (z:Site n→G.Color)(x:Positions (Primary n G)){d:ℝ} (h:Beam G d) (he: ∀ i:Body 1 n, ‖tint G _ x i‖<d)
local notation "X"=>tint G (Body 1 n)
local notation "b"=> coneT z
include h he
lemma year : cones z (0,x)=x∧HasDerivAt (fun t:ℝ=> cones z (t,x)) (speedsK z x) 0∧ ∀ᶠ t:ℝ in 𝓝 0,palace (cones z (t,x))=gauge (fun y=> G.lieExp (t • (-z y))) (palace x):=by
    let V(t:ℝ):= coneT z (t,X x); have hx : V 0=X x:= funext (fun i=>h _ (he i) _|>.2.2.1); have hv(i:Body 1 n):= h _ (he i) (ran z i)
    have hp: HasDerivAt V (fun i=>Native.Chart.speed G (ran z i) (X x i)) 0:=hasDerivAt_pi.mpr fun i=> Native.Chart.breeze G _ _ (hv i).1
    refine ⟨ (congr_arg (X).symm hx).trans ((X).symm_apply_apply x), (X).symm.hasFDerivAt.comp_hasDerivAt _ hp,?_⟩
    filter_upwards [eventually_all.mpr fun i=> ((continuous_id.prodMk (continuous_const (y:=X x i))).tendsto (0:ℝ)).eventually ((hv i).2.1)] with t ht; funext i; change represent (tint _ _ _) _= Lattice.gauge _ (represent ((X) x)) i
    rw [cones,ContinuousLinearEquiv.apply_symm_apply,Work.F03.represent_link]
    apply (ht (i.1,Exterior.coord i.2)).trans; unfold Lattice.gauge; rw [Work.F03.represent_link]; unfold Native.Chart.hit ran; rw [show axisEquiv.symm (Exterior.coord i.2)=i.2 from axisEquiv.symm_apply_apply _]; dsimp only [id]; rw [smul_neg t (z (i.1+step i.2)), Work.F03.exp_neg_color,inv_inv]
end YM.MSbar.Aqua
