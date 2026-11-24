import YM.Comparison.RG02.Valence.Parity
import YM.Comparison.RG02.Laplace.Facing
/-!
# Approach to flat along moving coarse fields and MW apertures

 At each fixed geometry. Expose uniformity when `x(g)→x₀`, used to compare moving gauge
 transforms. Apertures as persistent inside & outside supplies; covers/charge-support logarithm
 probes NOT assumed. Proof uses metric inverse-chart germ as in Habit, here mixed (g,x) inputs,
 real, quantifiers over any budget threshold.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symmetry
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Actual Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (D : BudgetPoint) (F : Forest S.ratio) (x : fieldDir G c 1)
local notation "X"=>fieldDir G c 1
local notation "Y"=> AxisChart G F
local notation "T"=> Bulk.Joint S F (G:=G)
local notation "J"=> Precision.Key F G→ℝ
local notation "E"=> F.Slice G
local notation "M"=> (ℝ × X)
local notation "L"=> (M×E)
local notation "U"=> 𝓝 (((0,x),1) : L)

include K in private lemma hot : mouth O (ι:=F.Free)∈𝓝 (0:Y):= (isOpen_set_pi Set.finite_univ (fun _ _=>Metric.isOpen_ball)).mem_nhds (fun _ _=>Metric.mem_ball_self K.ratio.patch)

private def badge (w:M): E:= repSample F w.1 w.2
private lemma shard (w:M): badge F w=Work.F05.exposure F (w.1 • w.2) (0:Y):= by
   unfold badge repSample Work.F05.exposure; ext1 y; simp; rfl
private lemma badge0 : badge F (0,x)=1:= by rw [shard,zero_smul]; exact Work.F05.exposure_zero _
private lemma arr_cont: Continuous (badge (G:=G) F):= by simp_rw [_root_.funext (shard F (G:=G))]; exact (Work.F05.exposure_continuous (G:=G) F).comp (f:=fun z:M=> (z.1 • z.2, (0:Y))) (by fun_prop)

-- unrelease via local plog after rep sample any path
private def news (v:L) : E:= v.2 * (badge F v.1)⁻¹
private lemma arrives : Tendsto (news F (G:=G)) U (𝓝 1):= by
   have hh: Continuous (news F (G:=G)):= continuous_snd.mul (((arr_cont F).comp continuous_fst).inv); have hp:=hh.tendsto ((((0:ℝ),x),1):L)
   rwa [show news F ((0,x),1)=1 from (by simp [news,badge0])] at hp
private def tell (v:L) : Y:= fun i=> G.plog (G.mat (news F v i))
include K in
private lemma informs : Tendsto (tell F (G:=G)) U (𝓝 0) ∧
    ∀ᶠ z in U, ∀ v:Y, v∈mouth O→ release (badge F z.1) v=z.2→ tell F z=v:= by
    have h(y:F.Free): Tendsto (fun z:L=> news F z y) U (𝓝 1):= ((continuous_apply y).tendsto (1:E)).comp (arrives F x)
    have ht: Tendsto (tell F (G:=G)) U (𝓝 0):= by
       apply tendsto_pi_nhds.mpr; intro i; exact (G.plog_one ▸ G.plog_diff.continuousAt.tendsto).comp ((G.mat_one ▸ G.continuous_mat.tendsto 1).comp (h i))
    refine ⟨ht,?_⟩; filter_upwards [eventually_all.mpr (fun i=> (h i).eventually G.plog_right), ht.eventually (hot K F)] with v hv hq w hw he
    funext i; have he' : G.lieExp (w i)=news F v i:= (eq_mul_inv_of_mul_eq (congrFun he i))
    exact K.ratio.inject (hq i (Set.mem_univ _)) (hw i (Set.mem_univ _)) ((hv i).trans he'.symm)

private lemma delays {δ:ℝ} (h : 0<δ): ∀ᶠ v in U, ∀ z:J, offset K F v.1.1 v.1.2 z∈mouth O→ walk K F v.1.1 v.1.2 z=v.2 → |v.1.1| * room K F v.1.2 z<δ:= by
    obtain ⟨hb,he⟩:= informs K F x
    have ht: Tendsto (fun v:L=>v.1.1) U (𝓝 0):= (continuous_fst.comp continuous_fst).tendsto _
    have hq: Tendsto (fun v:L=>v.1.2) U (𝓝 x):= (continuous_snd.comp continuous_fst).tendsto _
    let f(v:L):T:= (v.1.1,v.1.1 • v.1.2,tell F v); have hf: Tendsto f U (𝓝 0):= ht.prodMk_nhds ((show Tendsto (fun v:L=>v.1.1 • v.1.2) U (𝓝 0) from zero_smul ℝ x ▸ ht.smul hq).prodMk_nhds hb)
    have hp: Tendsto (fun v:L=> |v.1.1|+ ‖f v‖) U (𝓝 0):= by simpa using ht.norm.add hf.norm
    filter_upwards [he,hp.eventually (gt_mem_nhds h)] with v hv H z hz hu
    rw [room_cost, mul_add,mul_one,← Real.norm_eq_abs v.1.1,← norm_smul]
    rw [show v.1.1 • (Bulk.translated K F v.1.2 z)= f v from (by unfold f; rw [hv _ hz hu]; exact Integral.ribbon_eq K F v.1.1 v.1.2 z)]
    exact H
private lemma accepts : ∀ᶠ v in U,v.2∈ Integral.zone K D F v.1.1 v.1.2:= by
    have h0 := mem_of_mem_nhds (Integral.feasible K F D x); change (1:E)∈ Integral.zone K D F 0 x at h0
    have hs: repSample F 0 x=1:=badge0 F x
    have hl: (1:E)∈covered O (repSample F 0 x):= h0.1
    rw [hs] at hl
    have hh:= (F.continuous_drape.comp (f:=(Prod.snd : L→E)) continuous_snd).tendsto (((0,x),1):L)
    have ht: F.drape (1:E)=1:= by
       funext i; by_cases h:i∈F.trunks
       · exact F.on_tree _ ⟨i,h⟩
       exact F.off_tree _ ⟨i,h⟩
    rw [Function.comp_apply,ht] at hh
    filter_upwards [hh.eventually ((calm_germ D).and (min_group K.branches)), (arrives F x).eventually ((covered_isOpen K.ratio 1).mem_nhds hl)] with v hv hm
    refine ⟨?_,hv⟩; intro i _; obtain ⟨a,b,he⟩:= hm i (Set.mem_univ _); refine ⟨a,b,?_⟩; apply mul_right_cancel (b:=(repSample F v.1.1 v.1.2 i)⁻¹); rw [mul_inv_cancel_right]; simpa [news,badge] using he

variable (u : ℝ→fieldDir G c 1)
-- fixed top window eventually, with charges. no indicator differentiation.
private lemma preMeet (h : Tendsto u along (𝓝 x)) {δ : ℝ} (hp:0<δ) : ∃ A∈𝓝 (1:E), IsOpen A ∧ ∀ᶠ t in along,
   A⊆Integral.zone K D F t (u t) ∧ ∀ v∈ scope K F t (u t) A, t*room K F (u t) v≤δ:= by
   obtain ⟨a,b,ha,ha',hb,hb',H⟩:= mem_nhds_prod_iff'.mp ((accepts K D F x).and (delays K F x hp)); refine ⟨b,hb.mem_nhds hb',hb,?_⟩
   have hY:= (show Tendsto (fun t:ℝ=> (t,u t)) along (𝓝 (0,x)) from (tendsto_id.mono_left (show along≤𝓝 0 from nhdsWithin_le_nhds)).prodMk_nhds h).eventually (ha.mem_nhds ha')
   filter_upwards [hY,eventually_pos] with t ht hu
   refine ⟨fun i hi=> (H (a:=((t,u t),i)) ⟨ht,hi⟩).1,fun v hv=>?_⟩; nth_rw 1 [← abs_of_nonneg hu.le];
   exact ((H (a:=((t,u t),walk K F t (u t) v)) ⟨ht,hv.2⟩).2 v hv.1 rfl).le

variable (A:ℝ→Set (F.Slice G))

def Liberty (B : Set E) := ∃ Z∈𝓝 (1:E), ∀ᶠ t in along,A t⊆B ∧ MeasurableSet (A t) ∧ Z⊆A t

def Wins (δ :ℝ) : Prop := ∀ᶠ g in along, A g ⊆ Integral.zone K D F g (u g) ∧ ∀ v∈ scope K F g (u g) (A g), g*room K F (u g) v ≤ δ
lemma agree (h : Tendsto u along (𝓝 x)) {δ : ℝ} (hp:0<δ) : ∃ B∈𝓝 (1:E), IsOpen B ∧ ∀ A : ℝ→Set E, Liberty F A B→ Wins K D F u A δ:= by
   obtain ⟨B,b,he,H⟩:= preMeet K D F x u h hp; refine ⟨B,b,he,?_⟩; rintro a ⟨Z,hZ,hV⟩
   filter_upwards [H,hV] with g hg ha; exact ⟨ha.1.trans hg.1,fun v hv=> hg.2 v ⟨hv.1,ha.1 hv.2⟩⟩

lemma earned {B : Set E} (h : Liberty F A B): ∃ ε:ℝ,0<ε ∧ ∀ᶠ g in along, ∀ v : J, v∉ scope K F g (u g) (A g) → ε ≤ g*room K F (u g) v:= by
   obtain ⟨Z,hZ,H⟩:=h
   -- all escaped fields pay price from any persistent core Z
   let z(u:T):=Work.F05.exposure F u.2.1 u.2.2
   have hz: Tendsto z (𝓝 0) (𝓝 1):= (show z 0=1 from Work.F05.exposure_zero _) ▸ ((Work.F05.exposure_continuous F).comp continuous_snd).tendsto 0
   have hm: Tendsto (fun u:T=>u.2.2) (𝓝 0) (𝓝 0):= (continuous_snd.comp continuous_snd).tendsto (0:T)
   obtain ⟨r,hr,He⟩:= Metric.eventually_nhds_iff.mp ((hz.eventually hZ).and (hm.eventually (hot K F)))
   refine ⟨r,hr,?_⟩; filter_upwards [eventually_pos,H] with g hg h v he
   by_contra! ht; have hp : dist (g • (Bulk.translated K F (u g) v)) 0 < r:= by rw [dist_zero_right,norm_smul,Real.norm_of_nonneg hg.le]; rw [room_cost] at ht; nlinarith only [ht,hg]
   have hx:=He hp; rw [Integral.ribbon_eq] at hx; exact he ⟨hx.2,h.2.2 hx.1⟩
end YM.Comparison.RG02.Symmetry
