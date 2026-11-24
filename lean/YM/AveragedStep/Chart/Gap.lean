import YM.AveragedStep.Parcel.Sail
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
/-! Collar for ALL local primitives. Because detector derivative demands and
coupling order are fixed before the transfer, can use qualitative local
analyticity for each attained post-L Patch. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open RG Lattice Filter Function Precision Set Metric MeasureTheory
open scoped Topology Matrix.Norms.Frobenius ENNReal BigOperators Classical ContDiff
variable {G:Gauge}{P:Patch}{K:KernelChoices}{A: ChartRatio G}
attribute [local instance] Gauge.frobInner

abbrev canon (P:Patch):Leash P:= ((P.center,1),(P.center,1),P.center) -- Leash grouping FrameTag × ...
structure Cuff (P:Patch)(K:KernelChoices)(A:ChartRatio G) where
 width: ℝ
 active : 0 < width
 within : 3*width < A.radius
 chart_eq : ∀ u:G.Color, ‖u‖ ≤ 3*width → G.plog (G.mat (G.lieExp u))=u
 chart_ok : ∀ u:G.Color, ‖u‖ ≤ 3*width → ContinuousAt G.plog (G.mat (G.lieExp u))
 analytic : ∀ a,∀ v:Vectors P G,‖v‖≤3*width→ ContDiffAt ℝ ω (chip P K a (canon P)) v
 agree: ∀ (a:Mold)(l:Leash P)(v:Vectors P G), ‖v‖≤ 3*width →
   chip P K a l v=chip P K a (canon P) v ∧ numberChip P K a l v=numberChip P K a l (0:Vectors P G)
theorem allocated (hp:P.Branches K G)(hA: LocalRatio A):Nonempty (Cuff P K A):=by
  have h:∀ᶠ u:G.Color in 𝓝 0, G.plog (G.mat (G.lieExp u))=u ∧ ContinuousAt G.plog (G.mat (G.lieExp u)):=by
    apply G.plog_left.and
    have he₀:=G.exp_jet.continuous.tendsto (0:G.Color); have he:Tendsto (fun u:G.Color=>G.mat (G.lieExp u)) (𝓝 0) (𝓝 1):=by convert! he₀ using 1; rw [G.mat_lieExp_zero,G.mat_one]; rfl
    exact (he.eventually (G.plog_diff.eventually (by simp))).mono (fun _ h=> h.continuousAt)
  obtain ⟨C,hC,H⟩:=Metric.nhds_basis_closedBall.eventually_iff.mp h
  have ht : ∀ᶠ v:Vectors P G in 𝓝 0,∀ (a:Mold), ContDiffAt ℝ ω (chip P K a (canon P)) v ∧∀ l:Leash P,
       chip P K a l v=chip P K a (canon P) v∧ numberChip P K a l v=numberChip P K a l (0:Vectors P G):=
    eventually_all.mpr fun a=>((smooth_chip P K hp a (canon P)).1.eventually (by simp)).and
      (eventually_all.mpr fun l=> (common_chip P K hp a l _).and (still_chip P K hp a l))
  obtain ⟨D,hD,T⟩:=Metric.nhds_basis_closedBall.eventually_iff.mp ht
  let R:=min (min C D) A.radius/4
  have h0: 0<A.radius:=hA.patch; have hε: 0<R:= by unfold R; positivity
  have heq : 3*R < min (min C D) A.radius := by unfold R at *; linarith only [hε]
  have hb : 3*R < C:=heq.trans_le ((min_le_left ..).trans (min_le_left ..))
  have hd : 3*R < D:=heq.trans_le ((min_le_left ..).trans (min_le_right ..))
  have hx(u:G.Color)(h:‖u‖ ≤ 3*R):=H (show u∈closedBall 0 C by simpa using h.trans hb.le)
  have hy(v:Vectors P G)(h:‖v‖ ≤3*R):=T (show v∈closedBall 0 D by simpa using h.trans hd.le)
  exact ⟨R,hε,heq.trans_le (min_le_right ..),fun u h=>(hx u h).1,fun u h=>(hx u h).2,
    fun a v h=> (hy v h a).1, fun a l v h=>(hy v h a).2 l⟩ -- Nonempty constructor notation
namespace Cuff
variable (Q:Cuff P K A)(hL:LocalRatio A)
/- cut coordinates globally measurable. Use full measure equivalence only
via the actual `LocalRatio` pinned all-chart premise. Use closed core to
avoid any claim about openness of smaller exp subsets. -/
def core := G.lieExp '' (closedBall (0:G.Color) (2*Q.width))
lemma core_meas:MeasurableSet Q.core:=((isCompact_closedBall _ _).image G.lieExp_cont).measurableSet

def logC:=Q.core.piecewise (G.plog ∘ G.mat) (0:G.El→G.Color)
lemma log_meas : Measurable Q.logC:=by
 apply ContinuousOn.measurable_piecewise _ continuous_const.continuousOn Q.core_meas
 rintro x ⟨u,hu,h⟩; have he := Q.chart_ok u (by rw [mem_closedBall,dist_zero_right] at hu; linarith only [Q.active,hu]); rw [h] at he; exact (he.comp G.continuous_mat.continuousAt).continuousWithinAt
lemma wind_id {u:G.Color}(he: ‖u‖≤2*Q.width):Q.logC (G.lieExp u)=u:=by
 unfold logC; rw [piecewise_eq_of_mem Q.core _ _ (show G.lieExp u∈Q.core from ⟨u,by simpa using he,rfl⟩),comp_apply,Q.chart_eq u (by linarith only [he,Q.active])]
lemma log_max (u:G.El): ‖Q.logC u‖≤ 2*Q.width:=by
 by_cases h:u∈Q.core
 · rcases h with ⟨z,hz,rfl⟩
   have hv:‖z‖≤2*Q.width:=by simpa using hz
   rw [Q.wind_id hv]; exact hv
 unfold logC; rw [piecewise_eq_of_notMem Q.core _ _ h]; change ‖(0:G.Color)‖ ≤ _; rw [norm_zero]; linarith only [Q.active]
lemma log_bought:∃ E δ:ℝ,0<E∧0<δ∧(∀ u:G.El,G.chord u ≤ δ → u∈Q.core ∧ ‖Q.logC u‖ ≤ Q.width/8) ∧ ∀ u:G.El,‖Q.logC u‖ ≤ E*G.chord u:=by
 obtain ⟨D,d,hD,hd,H⟩:=Next.Fluctuations.log_chart_cost G
 let r:=min d (Q.width/(8*D))
 have hr:0<r:=lt_min hd (by have :=Q.active; positivity)
 have he(u:G.El)(hu:G.chord u≤r): u∈Q.core∧‖Q.logC u‖≤Q.width/8∧ ‖Q.logC u‖≤ D*G.chord u:=by
   obtain ⟨hz,hK⟩:=H u (hu.trans (min_le_left ..))
   let v:=G.plog (G.mat u)
   have hv:‖v‖ ≤ Q.width/8:=hK.trans ((mul_le_mul_of_nonneg_left (hu.trans (min_le_right ..)) hD.le).trans_eq (by field_simp))
   have hf:‖v‖ ≤ 2*Q.width:=by linarith only [hv,Q.active]
   have hi:Q.logC u=v:= hz ▸ Q.wind_id hf
   exact ⟨⟨v,by simpa using hf,hz⟩,hi ▸ hv,hi ▸ hK⟩ -- direction?
 refine ⟨max D (2*Q.width/r),r,hD.trans_le (le_max_left ..),hr,fun u hu=> ⟨(he u hu).1,(he u hu).2.1⟩,fun u=>?_⟩
 by_cases h:G.chord u ≤r
 · exact (he u h).2.2.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (G.chord_nonneg _))
 have hq:0<2*Q.width/r:=by have :=Q.active; positivity
 apply (Q.log_max _).trans
 rw [show 2*Q.width= (2*Q.width/r)*r from (div_mul_cancel₀ _ hr.ne').symm] -- rw RHS too
 exact mul_le_mul (by rw [div_mul_cancel₀ _ hr.ne']; exact le_max_right ..) (not_le.mp h).le hr.le (hD.trans_le (le_max_left ..)).le
end Cuff
end YM.AveragedStep
