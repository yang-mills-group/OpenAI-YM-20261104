import YM.X.Chir.Avenue
/-!
# L < 0 on all Zone with ‖z‖ large. ∃ smooth compact of course; high arity economics independent.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity Imprint
open Maxwell (Green normal)
open scoped Topology BigOperators Classical
variable {m k:ℕ} {V:Type*} {q:ℕ+}{r R e c:ℝ}
local notation "L"=>(atTop:Filter ℕ)
variable (hq:1<q.val){x y z:ℕ→E4}
lemma froth_h (h:z k ≠ 0): ‖froth z k‖=1:= by unfold froth ambition; have he:=norm_pos_iff.mpr h; rw [norm_smul,Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ he.ne']
lemma fertile (X:ℕ→E4)(h:∀i,‖X i‖≤ r): ∃ Y:E4,∃ φ:ℕ→ℕ, StrictMono φ ∧ Tendsto (X ∘ φ) L (𝓝 Y):= by
    obtain ⟨Y,hY,φ,hφ,hp⟩:= (isCompact_closedBall (0:E4) r).tendsto_subseq (fun i=>show X i∈ Metric.closedBall (0:E4) r from (by rw [Metric.mem_closedBall,dist_zero_right]; apply h)); exact ⟨Y,φ,hφ,hp⟩
include hq
lemma wholesome (h:Tendsto (ambition z) L atTop) (J:ℕ→Ter)(H:∀ i:ℕ,Crowd q (x i) (y i) (z i) (J i)): ∃ k:ℕ,SpinLimit (J k) (x k) (y k) (z k)<0:= by
     obtain ⟨X,f,hf,hX⟩:= fertile x (fun i=> H i|>.openWide.x0); obtain ⟨Y,g,hg,hY⟩:= fertile (y ∘ f) (fun i=> (H (f i)|>.openWide.y1)); let F:= f ∘ g; have hx : ∀ i:ℕ, ‖(froth z) i‖=1:= fun i=> froth_h (norm_pos_iff.mp (H i|>.openWide.z0))
     obtain ⟨Z,t,ht,hZ⟩:= fertile (froth z ∘ F) (fun i=> (hx (F i)).le); have he:‖Z‖=1:= tendsto_nhds_unique hZ.norm ((show Tendsto (fun _:ℕ=>(1:ℝ)) atTop (𝓝 1) from tendsto_const_nhds).congr fun i=> (hx _).symm)
     let U:=F ∘ t; let a:= x ∘ U; let b:=y∘U; let c:=z∘U; have hh:= (hf.comp (hg.comp ht)).tendsto_atTop; have hh': ∀ i:ℕ,Crowd q (a i) (b i) (c i) ((J ∘ U) i):=fun i=> H _; have ha:Tendsto a L (𝓝 X):= hX.comp (hg.comp ht|>.tendsto_atTop); have hb:Tendsto b L (𝓝 Y):= hY.comp ht.tendsto_atTop;
     have hS:=spin_far hq hh' (show Tendsto (ambition c) _ _ from h.comp hh) hZ he ha hb; have hG: Green (X-Y)>0:= by rw [Maxwell.normalization]; have hz:=norm_pos_iff.mpr (sub_ne_zero.mpr (duel (fun i=> (hh' i).openWide.wide_xy.1) ha hb)); positivity
     unfold goalM at hS; obtain ⟨k,hk⟩:= (hS.eventually (gt_mem_nhds (show (-6)*(8*normal)^3* Green (X-Y) <0 from by have h:=Maxwell.normal_pos; exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (pow_pos (by positivity) _)) hG))).exists
     exact ⟨U k, neg_of_mul_neg_right hk (pow_nonneg (norm_nonneg _) _)⟩
lemma region_power : ∃ R:ℝ,R≥4096 ∧ ∀ (x y z:E4)(J:Ter), Crowd q x y z J→ R≤‖z‖→ SpinLimit J x y z < 0:= by
    by_contra! h; choose x y z J H hx hz using fun i:ℕ => h (i+4096:ℝ) (by simp); have hy:Tendsto (ambition z) atTop atTop := by
       apply tendsto_atTop_mono _ (tendsto_natCast_atTop_atTop (R:=ℝ));intro b; exact le_trans (show (b:ℝ)≤ b+4096 from by norm_num) (hx b)
    obtain ⟨k,hk⟩:= wholesome hq hy J H; exact hk.not_ge (hz k)
lemma region_tag : ∃ (c:ℝ), c≥4096 ∧ ∀ x y z:E4,∀ (X Y Z:Fielding.Walk), plot q X x→plot q Y y→plot q Z z→∀ J:Ter, RootJ q X Y Z J→ Zone x y z→c≤‖z‖→SpinLimit J x y z<0:= by obtain ⟨r,hr,h⟩:= region_power hq; exact ⟨r,hr,fun x y z X Y Z h1 h2 h3 J hj hz he=> h x y z J ⟨hz,X,Y,Z,h1,h2,h3,hj⟩ he⟩
end YM.PositionX.Chir
