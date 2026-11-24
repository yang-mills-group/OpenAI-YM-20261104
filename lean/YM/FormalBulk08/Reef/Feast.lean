import YM.FormalBulk08.Reef.Fork
import YM.AnalyticNext.QUARTIC_MATCH.Rephase

/-! Rotation/translation with parent coarse gauge transported to the fine and
stripped back to the chosen tree. *Exact* probability measure statement. No
rotation covariance of a cutoff Λ implicit here. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Reef
open Series Wick Orb Jets Matrix Filter Set MeasureTheory Precision Work.F05 RG Wilson Lattice Tree Stationary
open scoped ContDiff BigOperators Topology ENNReal Classical Matrix.Norms.Frobenius
open Function
variable {G : Gauge} {c f : Side} {S : StepData c f}

lemma wick_preserves (G : Gauge) (F : Forest S.ratio) : MeasurePreserving (Profiles.wick F) (prior G f) (F.order G) := by
   refine ⟨(Profiles.continuous_wick F).measurable, Measure.ext (fun A hA=>?_)⟩
   let m:= Profiles.wick F (G:=G); let J:= A.indicator (fun _=> (1:ℝ))
   have h : Integrable (J ∘ m) (prior G f) := by
      rw [show J ∘ m=(m ⁻¹' A).indicator (fun _=> (1:ℝ)) by ext i; by_cases hh:m i∈A <;> simp [J,hh]]
      exact (integrable_const _).indicator ((Profiles.continuous_wick F).measurable hA)
   have he := F.pack _ h (fun k hk _ => congr_arg J (Profiles.wick_gauge F _ k hk))
   unfold J m at he; simp_rw [Function.comp_def,Profiles.wick_root] at he
   rw [Measure.map_apply (Profiles.continuous_wick F).measurable hA]
   apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
   have ht (x) : J (m x)=(m ⁻¹' A).indicator (fun _=> (1:ℝ)) x := by by_cases hz:m x∈A <;> simp [J,hz]
   unfold J m at ht; simp_rw [ht] at he
   rw [integral_indicator ((Profiles.continuous_wick F).measurable hA),integral_indicator hA,setIntegral_const,setIntegral_const] at he; simpa only [smul_eq_mul,mul_one] using! he

variable (S) (F : Forest S.ratio) (s : Signed) (x : Site c) (b : Site f → G.El)

def cook (U : Config G f) := Lattice.gauge b (pull s (S.ratio.embed x) U)
def pans (U : F.Slice G) : F.Slice G:= Profiles.wick F (cook S s x b (F.drape U))
lemma push_pans (U : Config G f) : pans S F s x b (Profiles.wick F U)=Profiles.wick F (cook S s x b U) := by
   let d:=F.foldAt U
   let e:=b * (d ∘ affine s (S.ratio.embed x)) * b⁻¹
   rw [pans,Profiles.wears]
   have he: cook S s x b (Profiles.wiped F U)=Lattice.gauge e (cook S s x b U) := by
      rw [cook,Profiles.wiped,YM.AnalyticNext.QuarticMatch.Joint.pullGauge];funext i; unfold cook e d; simp [Lattice.gauge,mul_assoc]
   rw [he,Profiles.wick_gauge]; intro i; simp [e,d,S.port,F.fold_root]
lemma feed_preserves : MeasurePreserving (pans S F s x b) (F.order G) (F.order G) := by
   have he : MeasurePreserving (cook S s x b) (prior G f) (prior G f) := (prior_gauge b).comp (prior_pull ..)
   have ha : Measurable (pans S F s x b) := ((Profiles.continuous_wick F).measurable.comp he.measurable).comp F.continuous_drape.measurable
   have hx:=(wick_preserves G F).map_eq
   refine ⟨ha,?_⟩
   nth_rw 1 [← hx]; rw [Measure.map_map ha (Profiles.continuous_wick F).measurable,show (pans S F s x b) ∘ Profiles.wick F= Profiles.wick F ∘ cook S s x b from funext fun i=>push_pans ..]
   exact ((wick_preserves G F).comp he).map_eq
lemma no_collapse : Function.Injective (pans S F s x b) := by
   let y:Site c := -(s⁻¹).act x
   let d := b⁻¹ ∘ affine s⁻¹ (S.ratio.embed y)
   apply Function.LeftInverse.injective (g:=pans S F s⁻¹ y d)
   intro i
   change pans S F s⁻¹ y d (Profiles.wick F _)=_

   rw [show _ = _ from push_pans S F s⁻¹ y d (cook S s x b (F.drape i))]
   simp_rw [cook,YM.AnalyticNext.QuarticMatch.Joint.pullGauge,pull_pull];
   rw [S.port, show affine s x y=0 from ?_]
   · have h : S.ratio.embed 0=0 := map_zero S.ratio.root
     rw [h,mul_inv_cancel,pull_id, show Lattice.gauge d (Lattice.gauge _ _)=F.drape i from ?_, Profiles.wick_root]
     ext j; simp [Lattice.gauge,d,mul_assoc]
   simp [affine,y]
end YM.FormalBulk08.Reef
