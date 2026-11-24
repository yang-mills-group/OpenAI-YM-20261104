import YM.Comparison.RG02.Integral.Window
import YM.Progress.STATIONARY_SCENES.Frames
import YM.UVNext.COUPLING_RESET.Precision
/-!
# The real no-flag comparison plaque

Export a maximal no-seam access candidate on the gauge slice, actual numerical admission.
Use best predictor branch in all frames, not a statement of uniform path bounds from K.
At arbitrary actual `V'` in the report one may restrict further to impose halo/cutoff criteria.
Prove no flags+branch AND likelihood equality for all tags throughout; method valid even for a
 sheet empty at that V'. At weak coupling limit (*fixed space*) prove a true
 vicinity of vacuum persists at each fixed x near g=0. `β` not varied by this
 choice. Quantifying costs of that vicinity is not done here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Integral
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree YM.Push.SectorMeasure
open YM.Marker YM.Multi Order YM.Next.SectorChange Actual
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}

-- all real group definitions permit use even away from the chart. No statement about
-- its projection-cover norm.
def Min (S : StepData c f) : Set (Config G f) := {y | (∀ z, S.patch.usesMin S.kernel (expandAt (S.ratio.embed z) y)) ∧ ∀ t : S.Choices, ∀ e,S.patch.usesBest S.kernel (S.connector y t.1 e)}

def Calm (P : BudgetPoint) : Set (Config G f):= {y| flags P.threshold y=∅}
lemma min_meas (h : S.patch.Branches S.kernel G) : MeasurableSet (Min S (G:=G)) := by
   let A : Set (Config G f):={U| ∀ z, S.patch.usesMin S.kernel (expandAt (S.ratio.embed z) U)}
   let B : Set (Config G f):={U| ∀ t : S.Choices,∀ e,S.patch.usesBest S.kernel (S.connector U t.1 e)}
   change MeasurableSet (A ∩ B)
   have hA : MeasurableSet A:=by
      unfold A; simp only [Set.setOf_forall]; apply MeasurableSet.iInter; intro i
      have ht z : Continuous fun U : Config G f=>expandAt (S.ratio.embed z) U:= by unfold expandAt; fun_prop
      exact ((ht i).measurable) S.patch.min_open.measurableSet
   apply hA.inter; unfold B; simp only [Set.setOf_forall]
   exact MeasurableSet.iInter fun t=> MeasurableSet.iInter fun x=> (S.connector_meas h t.1 x) S.patch.best_open.measurableSet

lemma calm_meas (P : BudgetPoint) : MeasurableSet (Calm P (f:=f) (G:=G)) := flags_measurable_eq ..

lemma uncharged (U : Config G f) (h : U∈Min S) (hp : S.patch.Branches S.kernel G) (t : S.Choices) : S.likelihood U t=(count S:ℝ)⁻¹ := by
   -- stage denominator uniform/count
   obtain ⟨hV,hz⟩:=h; have he (y : S.Choices) : S.likelihood U y=S.likelihood U t := by
      simp only [StepData.likelihood,Patch.frameMass,hV,↓reduceIte, Patch.predictorMass,hz]
   have ht:=S.chosen hp U
   have H (i : Finset S.Choices) := sum_congr (s₁:=i) rfl (g:=fun _=> S.likelihood U t) (fun k (_hk : k∈i)=> he k)
   apply mul_left_cancel₀ (show (count S:ℝ) ≠ 0 from by exact_mod_cast count_pos.ne')
   rw [mul_inv_cancel₀ (show (count S:ℝ) ≠ 0 from by exact_mod_cast count_pos.ne'), ← ht, H]; simp only [sum_const, Finset.card_univ,nsmul_eq_mul,count]
-- various ways minimal itself seems enough for safety at fixed branch
lemma unbranched (U : Config G f) (h : U∈ Min S) (t r : S.Choices): S.prediction U t=S.prediction U r := by
    have he z : S.frames U t.1 z=S.frames U r.1 z := by unfold StepData.frames Patch.frame; rw [if_pos (h.1 z),if_pos (h.1 z)]
    ext1 e; have hz : S.connector U t.1 e=S.connector U r.1 e := by unfold StepData.connector; simp_rw [he]
    unfold StepData.prediction Patch.predict; rw [if_pos (h.2 t e), if_pos (h.2 r e), hz]

lemma min_chart (h : S.patch.Branches S.kernel G) : ∀ᶠ y : fieldDir G f 1 in 𝓝 0, represent y∈ Min S :=
   (Progress.StationaryScenes.frameField h).roots.mono fun _ hx=>
      ⟨fun z=>(hx.1 z).1, fun i=>(hx.2 i).2.2⟩

-- Use F03 chart lemma rather than global surjectivity of log; here's also direct near config
lemma min_group (h : S.patch.Branches S.kernel G) : ∀ᶠ y : Config G f in 𝓝 1, y∈ Min S := by
   let W := fun y : Config G f=> fun i : Exterior.Body 1 f=> G.plog (G.mat (y (i.1,axisEquiv.symm i.2)))
   have he : Tendsto W (𝓝 1) (𝓝 0) := by
       apply tendsto_pi_nhds.mpr; intro i
       have hp : ContinuousAt G.plog 1:= G.plog_diff.continuousAt
       have hs := (G.continuous_mat.comp (continuous_apply (i.1, axisEquiv.symm i.2))).tendsto (1:Config G f)
       simp only [Function.comp_apply, Pi.one_apply,G.mat_one] at hs
       exact (G.plog_one ▸ hp.tendsto).comp hs
   have hq : ∀ᶠ y : Config G f in 𝓝 1, represent (W y)=y := by
       filter_upwards [eventually_all.mpr (fun i : Edge (Site f)=> ((continuous_apply i).tendsto (1:Config G f)).eventually G.plog_right)] with y hy
       funext i
       rw [Work.F03.represent_link]
       simpa only [W,show axisEquiv.symm (coord i.2)=i.2 from axisEquiv.symm_apply_apply i.2] using! hy i
   filter_upwards [hq,he.eventually (min_chart h)] with y hv hl; rwa [hv] at hl

lemma calm_germ (P : BudgetPoint) : ∀ᶠ y : Config G f in 𝓝 1, y ∈ Calm P := by
   have he (i : Face (Per f)) : Continuous (fun U : Config G f=> G.chord (faceValue U i)) := by unfold faceValue; fun_prop
   have hz (i : Face (Per f)) : faceValue (1:Config G f) i=1 := by rw [← link_one]; exact YM.Push.stroll_zero ..
   have hw (i) : ∀ᶠ u in 𝓝 (1:Config G f),G.chord (faceValue u i)<P.threshold:= (he i).continuousAt.eventually_lt continuousAt_const (by rw [hz,G.chord_one]; exact P.threshold_pos)
   filter_upwards [eventually_all.mpr hw] with y hy
   exact YM.Push.BetaTransport.flags_empty (fun i=>(hy i).le)

variable {P : PathData G} {p : Clip} {O : ChartRatio G} (K : Bulk.Kernel S p P O) (F : Forest S.ratio)
    (D : BudgetPoint) (g : ℝ) (x : fieldDir G c 1)
-- Use to instantiate the comparisons, track actual flag dependencies. Threshold frozen D, t IDs
-- maybe assembled from same θ, complete set here not tailored to their separate branches.
def zone (K : Bulk.Kernel S p P O) (D : BudgetPoint) (F : Forest S.ratio) (g : ℝ) (x : fieldDir G c 1) : Set (F.Slice G) := covered K.jacobian (repSample F g x) ∩ (F.drape ⁻¹' (Calm D ∩ Min S))
lemma plausible : Reach K F g x (zone K D F g x) := ⟨(covered_meas K.ratio _).inter (F.continuous_drape.measurable ((calm_meas D).inter (min_meas K.branches))),Set.inter_subset_left⟩
lemma limited (t : S.Choices) (A : Set (F.Slice G)) (ha : A ⊆ zone K D F g x) (hA : MeasurableSet A) : Trust K F t g x A := ⟨⟨hA,ha.trans (plausible ..).2⟩,fun _ h=>uncharged _ (ha h).2.2 K.branches t⟩
lemma trusted (t : S.Choices) : Trust K F t g x (zone K D F g x) := limited K F D g x t _ (Set.Subset.refl _) (plausible ..).1

-- Reach germ at fixed P in charge scaling; controls no rate as volume changes.
lemma feasible : ∀ᶠ v : ℝ × (F.Slice G) in 𝓝 (0,1), v.2∈ zone K D F v.1 x := by
   have hv0 : F.drape (1:F.Slice G)=1 := by
      have hf : lifting F (1:Config G c) 0=1 := by simp
      rw [← hf]; unfold lifting; rw [replica_one]; congr; simp only [Pi.zero_apply,G.mat_lieExp_zero,Pi.one_apply,mul_one]; rfl
   have hz : repSample F 0 x=1 := by unfold repSample sample; rw [zero_smul,link_one,replica_one]; rfl
   have he : Continuous (fun t : ℝ=>repSample F t x) := by
      apply continuous_pi; intro i
      unfold repSample replica sample represent increment Exterior.collect; split <;> fun_prop
   have hJ : Tendsto (fun (q : ℝ × F.Slice G)=> q.2 * (repSample F q.1 x)⁻¹) (𝓝 (0,1)) (𝓝 1) := by
      have hc:Continuous (fun (q : ℝ × F.Slice G)=> q.2 * (repSample F q.1 x)⁻¹):= continuous_snd.mul ((he.comp continuous_fst).inv)
      simpa only [hz,inv_one,mul_one] using hc.tendsto (0,1)
   have hr : (1:F.Slice G)∈covered O 1 := by
      rw [← release_image]; exact ⟨0,fun i _=>Metric.mem_ball_self K.ratio.patch,by ext1 i; simp [release]⟩
   have ha := (F.continuous_drape.comp continuous_snd).tendsto (((0:ℝ), (1:F.Slice G)))
   simp only [Function.comp_apply,hv0] at ha
   filter_upwards [ha.eventually ((calm_germ D).and (min_group K.branches)),hJ.eventually ((covered_isOpen K.ratio 1).mem_nhds hr)] with q hm hx
   refine ⟨?_,hm⟩; intro i _
   obtain ⟨a,v,he⟩:= hx i (Set.mem_univ _)
   refine ⟨a,v,?_⟩
   apply mul_right_cancel (b:=(repSample F q.1 x i)⁻¹)
   rw [mul_inv_cancel_right]; simpa using he

end YM.Comparison.RG02.Integral
