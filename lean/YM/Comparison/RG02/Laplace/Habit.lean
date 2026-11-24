import YM.Comparison.RG02.Laplace.Fields
/-!
# Common shrinking chart at finite volume, no uniform comparison

Use root-link neighborhood *fixed* independent of g for prescribed geometry/order. With
D frozen, supports depend on same t, all θ have Min & mask. This aperture doesn't estimate
 cost of future mask-failure tails. Build interior model & asympt after disintegration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Laplace
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Actual
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices) (g c₀:ℝ)
  (W : Bulk.Colors R G f) (x : fieldDir G c 1)
local notation "L"=> Precision.Key F G → ℝ
local notation "μ"=> Gaussian.cloud (K.covariance F t)
local notation "ζ"=> Bulk.translated K F x
local notation "T"=> Bulk.Joint S F (G:=G)

-- Outside lower on gamut: excludes small `g•ξ` by continuity of release
include K in
private lemma mouth_hot : mouth O (ι:=F.Free)∈𝓝 (0:AxisChart G F) := (isOpen_set_pi Set.finite_univ (fun _ _=>Metric.isOpen_ball)).mem_nhds (fun _ _=>Metric.mem_ball_self K.ratio.patch)

lemma earns (A : Set (F.Slice G)) (h : A∈𝓝 1) : Earned K F x (fun _=>A) := by
   let m (u:T) := Work.F05.exposure F u.2.1 u.2.2
   have hc : Continuous m := (Work.F05.exposure_continuous F).comp continuous_snd
   have hv : ∀ᶠ u : T in 𝓝 0, m u∈A ∧ u.2.2∈mouth O := by
       have he:= hc.tendsto 0; rw [show m 0=1 from Work.F05.exposure_zero _] at he
       exact (he.eventually h).and (((continuous_snd.comp continuous_snd).tendsto (0:T)).eventually (mouth_hot K F))
   obtain ⟨r,hr,H⟩:= Metric.eventually_nhds_iff.mp hv
   refine ⟨r,hr,eventually_pos.mono fun g hg v hv=>?_⟩
   by_contra! he
   have ht : dist (g • ζ v) 0 < r := by rw [dist_zero_right,norm_smul, Real.norm_of_nonneg hg.le]; rw [room_cost] at he; nlinarith only [he,hg]
   have hx:=H ht; rw [Integral.ribbon_eq] at hx
   exact hv ⟨hx.2,hx.1⟩

-- inverse chart (uniform at (0,1)). Keep real scope with mouth in the argument.
private def backNews (u : ℝ × F.Slice G) : F.Slice G := u.2 * (repSample F u.1 x)⁻¹
private def caught (u : ℝ × F.Slice G) : AxisChart G F := fun i=> G.plog (G.mat (backNews F x u i))
private lemma back_origin : Tendsto (backNews F x) (𝓝 (0,1)) (𝓝 1) := by
   -- `repSample` from exposure relative at a=0
   have hh (t:ℝ) : repSample F t x=Work.F05.exposure F (t • x) 0 := by unfold Work.F05.exposure repSample; ext1 y; simp; rfl
   have ht : Continuous (fun t:ℝ=> repSample F t x) := by
      simp_rw [hh]; exact (Work.F05.exposure_continuous (G:=G) F).comp (f:=fun z:ℝ=> (z • x,(0:AxisChart G F))) ((continuous_id.smul continuous_const).prodMk continuous_const)
   have hc:Continuous (backNews F x) := continuous_snd.mul ((ht.comp continuous_fst).inv)
   have h:=hc.tendsto (0,1)
   rwa [show backNews F x (0,1)=1 by simp [backNews,hh,Work.F05.exposure_zero F]] at h
private lemma wears (F : Forest S.ratio) (K : Bulk.Kernel S p P O) :
    Tendsto (caught F x) (𝓝 (0,1)) (𝓝 0) ∧
       ∀ᶠ z in 𝓝 (0,1), ∀ v : AxisChart G F, v∈mouth O → release (repSample F z.1 x) v=z.2 → caught F x z=v := by
   have h (y : F.Free) : Tendsto (fun p=>backNews F x p y) (𝓝 (0,1)) (𝓝 1) := ((continuous_apply y).tendsto (1:F.Slice G)).comp (back_origin F x)
   have ht : Tendsto (caught F x) (𝓝 (0,1)) (𝓝 0) := by
      apply tendsto_pi_nhds.mpr; intro i
      have ht : ContinuousAt G.plog 1 := G.plog_diff.continuousAt
      exact (G.plog_one ▸ ht.tendsto).comp ((G.mat_one ▸ G.continuous_mat.tendsto 1).comp (h i))
   refine ⟨ht,?_⟩; filter_upwards [eventually_all.mpr (fun i=> (h i).eventually G.plog_right), ht.eventually (mouth_hot K F)] with u hu hl v hv he
   funext i; have he' : G.lieExp (v i)=backNews F x u i := (eq_mul_inv_of_mul_eq (congrFun he i))
   apply K.ratio.inject (hl i (Set.mem_univ _)) (hv i (Set.mem_univ _)) ((hu i).trans he'.symm)

private lemma travel_near {δ : ℝ} (hδ : 0<δ) : ∀ᶠ u : ℝ × F.Slice G in 𝓝 (0,1),
    ∀ v : Precision.Key F G→ℝ, offset K F u.1 x v∈mouth O → walk K F u.1 x v=u.2 → |u.1| * room K F x v<δ := by
   obtain ⟨hb,he⟩ := wears x F K
   have hp : Tendsto (Prod.fst:ℝ × F.Slice G →ℝ) (𝓝 (0,1)) (𝓝 0) := continuous_fst.tendsto (0,1)
   let f (u : ℝ × F.Slice G) : T := (u.1,u.1 • x, caught F x u)
   have hv : Tendsto f (𝓝 (0,1)) (𝓝 0) := hp.prodMk_nhds ( (show Tendsto (fun v : ℝ × F.Slice G=> v.1 • x) (𝓝 (0,1)) (𝓝 0) from zero_smul ℝ x ▸ hp.smul tendsto_const_nhds) |>.prodMk_nhds hb)
   have hc : Tendsto (fun u=> ‖u.1‖ + ‖f u‖) (𝓝 (0,1)) (𝓝 0) := by simpa using (hp.norm.add hv.norm)
   filter_upwards [hc.eventually (gt_mem_nhds hδ),he] with u hy hu v hh hl
   rw [room_cost,mul_add,mul_one, ← Real.norm_eq_abs u.1,← norm_smul]; unfold f at hy
   have hr : u.1 • (ζ v)= f u := by unfold f; rw [Integral.ribbon_eq, hu _ hh hl]
   rw [hr]; exact hy

lemma aperture (D : BudgetPoint) {δ:ℝ} (hδ :0 < δ) : ∃ A∈𝓝 (1:F.Slice G), IsOpen A ∧ ∀ B : Set (F.Slice G),
       B⊆A → MeasurableSet B → Small K F x (fun _=>B) δ ∧ (∀ᶠ g in along, B⊆Integral.zone K D F g x) := by
   obtain ⟨a,b,ha,ha',hb,hb',H⟩:= mem_nhds_prod_iff'.mp ((travel_near K F x hδ).and (Integral.feasible K F D x))
   refine ⟨b, hb.mem_nhds hb',hb,fun B h hm=>?_⟩
   have ht : a ∈ along:= nhdsWithin_le_nhds (ha.mem_nhds ha')
   constructor
   · filter_upwards [Tested.eventually_pos,ht] with g hg hu v hv
     let x' := walk K F g x v
     have he := (H (a:=(g,x')) ⟨hu,h hv.2⟩).1 v hv.1 rfl
     change |g| * _< δ at he; rw [abs_of_nonneg hg.le] at he; exact he.le
   exact (show ∀ᶠ g in along, g∈a from ht).mono (fun t ht=> fun y hy=> (H (a:=(t,y)) ⟨ht,h hy⟩).2)
end YM.Comparison.RG02.Laplace
