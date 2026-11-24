import YM.OPE.Compatible.Glyph.Ivory
import YM.OPE.Compatible.Birch.Calm
/-! # Switch to vertical forest coordinates. Confirm Newton and Jacobian via Haar saver. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Asymptotics Work.F05
open Stationary
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type*} {G:Gauge}{c f:Side}{S:StepData c f} {p q:Clip}{R T:PathData G} (F:Tree.Forest S.ratio)
namespace Virgin
local notation "C" => (Bid.Dir G c)
local notation "P"=>AxisChart G F
abbrev expF (x:P): F.Slice G:=fun i=> G.lieExp (x i)
abbrev fieldF (x:P): Config G f:= F.drape (expF F x)
def score (t:S.Choices)(p:Clip)(R:PathData G)(x:C)(y:P):=mainTerm p R (fieldF F y)+noiseTaylor S (represent x) (fieldF F y) t
def slog (x:C)(y:P):P:= fun i=> plogC G (exposure F x y i)
def bare (x:C)(y:P):F.Slice G:= fun i=> expF F y i * (replica S.ratio (represent x) i)⁻¹
def bog (x:C)(y:P):P:= fun i=> plogC G (bare F x y i)
lemma slog_zero : slog F (0:C) 0=0:= by ext i : 1; unfold slog;rw [exposure_zero];exact plogC_one
lemma bare_zero : bare F (0:C) 0=1:= by funext i; simp [bare,expF]
lemma bog_zero : bog F (0:C) 0=0:=by ext i : 1;unfold bog;rw [bare_zero];exact plogC_one
lemma slogmooth : ContDiffAt ℝ ω (uncurry (slog F (G:=G))) 0:=by
   apply contDiffAt_pi.mpr; intro i; apply ContDiffAt.comp (g:=G.plog) (f:=fun z:C×P=>G.mat (exposure F z.1 z.2 i)) 0 _ (exposure_jet F i)
   change ContDiffAt ℝ ω G.plog (G.mat (exposure F 0 0 i));rw [exposure_zero];exact G.mat_one.symm ▸ G.plog_diff
lemma bareSmooth : Army (uncurry (bare F (G:=G))) 0:=by
   apply Army.mul (u:=fun (z:C×P)=> expF F z.2) (v:=fun (z:C×P)(i:F.Free)=>(replica S.ratio (represent z.1) i)⁻¹)
   · intro i; exact G.exp_jet.contDiffAt.comp (f:=fun z : C × P => z.2 i) _ ((contDiffAt_apply ..).comp _ contDiffAt_snd)
   apply Army.inv (u:=fun (z:C×P)(i:F.Free)=>replica S.ratio (represent z.1) i); intro i
   simp_rw [show ∀ u:C,replica S.ratio (represent u) i=exposure F u 0 i from fun i=>by simp [exposure]]; exact (exposure_jet F i).comp (f:=fun z:C×P=>(z.1,(0:P))) (0:C×P) (contDiffAt_fst.prodMk contDiffAt_const)
lemma bogmooth : ContDiffAt ℝ ω (uncurry (bog F (G:=G))) 0:= by
    refine contDiffAt_pi.mpr fun i=>?_ ; refine ContDiffAt.comp (g:=G.plog) _ ?_ (bareSmooth F i); change ContDiffAt ℝ ω G.plog (G.mat (bare F 0 0 i));rw [bare_zero]; exact G.mat_one.symm ▸ G.plog_diff
set_option maxHeartbeats 200000 in
lemma expSlog : ∀ᶠ z:C × P in 𝓝 0, expF F (slog F z.1 z.2)=exposure F z.1 z.2:=by
   refine (eventually_all.mpr ?_).mono (p:=fun z:C×P=>∀ i,expF F (slog F z.1 z.2) i=exposure F z.1 z.2 i) (fun _ h=>funext h)
   intro i; have hx:Tendsto (fun z:C × P=>exposure F z.1 z.2 i) (𝓝 0) (𝓝 1):=by
       have he:= ((continuous_apply i).comp (exposure_continuous (G:=G) F)).tendsto (0:C × P); change Tendsto _ _ (𝓝 (exposure F 0 0 i)) at he; rw [exposure_zero] at he; exact he
   exact hx.eventually G.plog_right
lemma packBog : ∀ᶠ z:C × P in 𝓝 0, exposure F z.1 (bog F z.1 z.2)=expF F z.2:=by
   have ht:Tendsto (uncurry (bare F (G:=G))) (𝓝 0) (𝓝 1):=by
       have he: uncurry (bare F (G:=G)) 0=1:= bare_zero F; rw [← he]; exact (bareSmooth F).cont.tendsto
   have h(i:F.Free): ∀ᶠ z:C×P in 𝓝 0,G.lieExp (bog F z.1 z.2 i)=bare F z.1 z.2 i:= (tendsto_pi_nhds.mp ht i).eventually G.plog_right
   filter_upwards [eventually_all.mpr h] with z hz; funext i; rw [exposure,hz,bare,inv_mul_cancel_right]
lemma slogRev : ∀ᶠ z:C×P in 𝓝 0,bog F z.1 (slog F z.1 z.2)=z.2:=by
   have h(i:F.Free): ∀ᶠ z:C×P in 𝓝 0,G.plog (G.mat (G.lieExp (z.2 i)))=z.2 i:= (((continuous_apply i).comp continuous_snd).tendsto (0:C×P)).eventually G.plog_left
   filter_upwards [eventually_all.mpr h,expSlog F] with z hz he; ext i : 1; change plogC G _=z.2 i;rw [bare,he,exposure,mul_inv_cancel_right];exact hz i
lemma scoreS (t:S.Choices)(p:Clip)(R:PathData G): ∀ᶠ z:C×P in 𝓝 0,tested F t p R z.1 z.2=score F t p R z.1 (slog F z.1 z.2):=by
    filter_upwards [expSlog F] with z he; unfold score fieldF; rw [he]; rfl
lemma scoreB (t:S.Choices)(p:Clip)(R: PathData G): ∀ᶠ z:C×P in 𝓝 0,score F t p R z.1 z.2=tested F t p R z.1 (bog F z.1 z.2):=by
    filter_upwards [packBog F] with z he; unfold score fieldF; rw [←he];rfl
end Virgin
end YM.OPE.Flume
