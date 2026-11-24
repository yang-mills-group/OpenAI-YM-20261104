import YM.MS.Wilson.ColorLinks
import YM.MS.Wilson.Signed
/-!
# Reflecting a stencil at links. Uses Maurer two-ended reversal. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Orient
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Bare Focus Landau Draft Sew Chart
open scoped Topology ContDiff
variable {R:Type}[AddCommGroup R][One R]{G:Gauge}(k:Signed)
local notation "P"=>Four R
lemma pose_name (i:LightMode G P): pose k (single i)= σ k i • single (turn k i):= by unfold pose; rw [LinearMap.comp_apply,sign_letter,map_smul,escort]
lemma pose_GH (x:P)(i:G.ColorIndex): pose k (GH i x)=GH i (k.act x):=by unfold GH; rw [pose_name]; simp only [ghostAt,σ,ghost,fee,turn,Complex.ofReal_one,one_smul]
lemma pose_GHP (x:P)(i:G.ColorIndex): pose k (GHplus i x)=GHplus i (k.act x):=by unfold GHplus; rw [pose_name]; simp only [σ,gaugeC,fee,turn,Complex.ofReal_one,one_smul]
lemma pose_AH (x:Edge P)(i:G.ColorIndex): pose k (AHplus i x)=(fee k (some x.2):ℂ) • AHplus i (purse k x):=by unfold AHplus; rw [pose_name]; rfl

omit [AddCommGroup R] [One R] in
lemma σ_edge (i:G.ColorIndex)(x:Edge P): σ k (formAt x.2 i x.1)=(fee k (some x.2):ℂ):= rfl
lemma onedge_pose (x:Edge P)(F:G.Color→ℝ)(h:germ F): pose k (onedge x F)=onedge (purse k x) (fun a=> F (fee k (some x.2) • a)):= by
   let c:= fee k (some x.2); let r:= knot (fun _:Unit=> x) (G:=G)
   let f (v: Lot G Unit) := F (v ())
   let T := c • ContinuousLinearMap.id ℝ (Lot G Unit)
   have hh : germ f:= tiny h
   unfold pose onedge Sew.art; rw [LinearMap.comp_apply, ← ferry_rent, ferry_trans]; congr! 1
   apply Subtype.ext; rw [landc]; change Cylinder.rent (σ k∘ r) (ink priv f)= ink priv (f ∘ T)
   rw [ink_ctrl_one,show (σ k ∘ r)= fun _ => (c:ℂ) from rfl,tagged_scale f (c:=fun _=>c) _ hh]; rfl; exact hh
lemma rem0 (x:Axis)(he:k.flip x=false): fee k (some x)=1:= by simp [fee,he]
lemma rem1 (x:Axis)(he:k.flip x=true): fee k (some x)= -1:=by simp [fee,he]
lemma edgeH (x:Edge P): pose k (onedge x (Maurer.lac (G:=G)))= onedge (purse k x) Maurer.lac:= by
   rw [onedge_pose k x _ (Maurer.hlog G)]; apply edge_swap; cases h:k.flip x.2
   · exact Eventually.of_forall fun y=> by dsimp only; rw [rem0 k x.2 h,one_smul] -- check beta
   · filter_upwards [Maurer.opposite (G:=G)] with y hy; rw [rem1 k x.2 h,neg_smul,one_smul, hy]
lemma pose_stay (i:Conn G)(x:Edge P)(hf:k.flip x.2=false)(y:P)(V:Conn G→ Maurer.Ends G): pose k (steerA y i x V)=steerA (k.act y) i (purse k x) V:= by
   simp only [steerA,map_sum,pose_s,pose_GH]; simp_rw [onedge_pose k x _ (vel_germ _ i), rem0 k x.2 hf,one_smul]
lemma pose_vel (i:Conn G)(x:Edge P)(hf:k.flip x.2=true)(y:Maurer.Ends G) : pose k (onedge x (vel y i))= -onedge (purse k x) (vel y.swap i):= by
   rw [onedge_pose _ _ _ (vel_germ _ i), show -onedge (purse k x) (vel y.swap i)=((-1:ℝ):ℂ) • onedge (purse k x) (vel y.swap i) by push_cast; exact (neg_one_smul ℂ _).symm, ← edge_scale _ _ (vel_germ _ i)]
   apply edge_swap; filter_upwards [Maurer.volt_back y.swap] with t ht; simp only [rem1 k x.2 hf,neg_smul,one_smul,vel, Pi.smul_apply,smul_eq_mul]; -- adjust
   rw [show Maurer.volts y (-t)= _ from ht]; simp
lemma pose_rev (i:Conn G)(x: Edge P)(hf:k.flip x.2=true)(y:P)(V:Conn G→Maurer.Ends G): pose k (steerA y i x V)= - steerA (k.act y) i (purse k x) (Prod.swap ∘ V):= by
    simp only [steerA,map_sum,pose_s,pose_GH,pose_vel _ i x hf,map_neg,Function.comp_apply, Finset.sum_neg_distrib]
lemma pose_throat (i:Conn G)(x:Edge P): pose k (throat idRail x i)= (fee k (some x.2):ℂ) • throat idRail (purse k x) i:= by
    simp only [throat,map_add]; cases he:k.flip x.2
    · rw [rem0 k x.2 he]; simp only [Complex.ofReal_one, one_smul]; rw [pose_stay k i x he,pose_stay k i x he,purse_base, purse_d] -- orientation rewrite may rewrite inside
      simp [he]
    · rw [rem1 k x.2 he]; simp only [Complex.ofReal_neg,Complex.ofReal_one]; rw [pose_rev k i x he,pose_rev k i x he,purse_base,purse_d]; simp only [he, if_true];
      rw [← neg_add_rev]; exact (neg_one_smul ℂ _).symm
lemma pose_cog (i:Conn G)(x:P): pose k (cog x i) = cog (k.act x) i:= by simp only [cog,map_sum,map_smul,pose_s,pose_GH]
lemma pose_Aterm (i:Conn G)(x:Edge P): pose k (couple DotFlip (AHplus i x) (throat idRail x i)) = couple DotFlip (AHplus i (purse k x)) (throat idRail (purse k x) i):= by
   rw [pose_s,pose_AH,pose_throat]; cases he:k.flip x.2 <;> simp [he,fee]
lemma pose_Cterm (i:Conn G)(x:P): pose k (couple DotFlip (GHplus i x) (cog x i))=couple DotFlip (GHplus i (k.act x)) (cog (k.act x) i):= by simp_rw [pose_s,pose_GHP,pose_cog]
end YM.MS.Native.Orient
