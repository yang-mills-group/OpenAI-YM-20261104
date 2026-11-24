import YM.Integration.WilsonOrdinaryNestedFixedInput
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! A unit mass smooth separated test recovers a full ordinary field value. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOrdinaryNestedShapeTest
open Set Filter MeasureTheory Metric Spec
open scoped Topology BigOperators Classical
variable {n:ℕ} {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem read {K:Set (Points n)} (clear:K⊆conf n) {z:Points n} (inside:K∈𝓝 z)
    {F:Points n→E} (continuous:∀x∈K,ContinuousAt F x) {C:ℝ}
    (income:∀φ:Test n,tsupport (φ:Points n→ℂ)⊆K →
      ‖∫x:Points n,φ x • F x‖≤C*(∫x:Points n,‖φ x‖)):
    ‖F z‖≤C:=by
  by_contra! large
  let δ:ℝ:=(‖F z‖-C)/2
  have dp:0<δ:=half_pos (sub_pos.mpr large)
  have good:∀ᶠ x in 𝓝 z,dist (F x) (F z)<δ:=
    (continuous z (mem_of_mem_nhds inside)).tendsto (ball_mem_nhds (F z) dp)
  obtain ⟨a,ap,near⟩:=Metric.mem_nhds_iff.mp (inter_mem inside good)
  let b:ContDiffBump z:=⟨a/4,a/2,by positivity,by linarith⟩
  let u:=b.normed (volume:Measure (Points n))
  have land:tsupport u⊆ball z a:=
    (b.tsupport_normed_eq (μ:=volume)).le.trans (Metric.closedBall_subset_ball (half_lt_self ap))
  let φ:Test n:=
    ⟨fun x=>(u x:ℂ),Complex.ofRealCLM.contDiff.comp b.contDiff_normed,
      b.hasCompactSupport_normed.comp_left Complex.ofReal_zero,by
        intro x hx
        apply clear (near (land ?_)).1
        exact (tsupport_comp_subset (f:=u) (g:=Complex.ofReal) Complex.ofReal_zero) hx⟩
  have supp:tsupport (φ:Points n→ℂ)⊆tsupport u:=
    tsupport_comp_subset (f:=u) (g:=Complex.ofReal) Complex.ofReal_zero
  have housed:tsupport (φ:Points n→ℂ)⊆K:=fun x hx=>(near (land (supp hx))).1
  have unit:∫x:Points n,‖φ x‖=1:=by
    change ∫x:Points n,‖(u x:ℂ)‖=1
    have one(x:Points n):‖(u x:ℂ)‖=u x:=(Complex.norm_real _).trans (Real.norm_of_nonneg (b.nonneg_normed x))
    simp_rw [one]
    exact b.integral_normed
  have exactUnit: (∫ x:Points n,φ x • F z)=F z:=by
    change (∫ x:Points n,(u x:ℂ) • F z)=F z
    have real(x:Points n):(u x:ℂ) • F z=u x • F z:=IsScalarTower.algebraMap_smul ℂ (u x) (F z)
    simp_rw [real]
    exact b.integral_normed_smul (μ:=volume) (F z)
  have ig:=RG17.localized φ F (fun x hx=>continuous x (housed hx))
  have ic:=RG17.localized φ (fun _=>F z) (fun _ _=>continuousAt_const)
  have er: ‖(∫x:Points n,φ x • F x)-F z‖≤δ:=by
    rw [←exactUnit,←integral_sub ig ic]
    apply (norm_integral_le_integral_norm _).trans
    calc
      _ ≤ ∫x:Points n,‖φ x‖*δ:=by
        refine integral_mono (ig.sub ic).norm ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm.mul_const δ) ?_
        intro x
        change ‖φ x • F x - φ x • F z‖≤‖φ x‖*δ
        rw [←smul_sub,norm_smul]
        by_cases hx:φ x=0
        · simp [hx]
        · have localBound : dist (F x) (F z)<δ:=(near (land (supp (subset_tsupport _ hx)))).2
          rw [dist_eq_norm] at localBound
          exact mul_le_mul_of_nonneg_left localBound.le (norm_nonneg _)
      _ = δ:=by rw [integral_mul_const,unit,one_mul]
  have bound:=income φ housed
  rw [unit,mul_one] at bound
  have close:=norm_le_norm_sub_add (F z) (∫x:Points n,φ x • F x)
  rw [norm_sub_rev] at close
  dsimp [δ] at er
  linarith
def shapes (n:ℕ) (U η:ℝ):Set (Points n):=
  {z | (∀i:Fin n,‖z i‖≤U) ∧ ∀i j:Fin n,i≠j→η≤‖z i-z j‖}

theorem cover (n:ℕ) (U η:ℝ) (sep:0<η):
    ∃K:Set (Points n),IsCompact K ∧ K⊆conf n ∧ ∀z∈shapes n U η,K∈𝓝 z:=by
  let B:=((@WithLp.toLp 2 (Fin n→E4)) '' Set.pi Set.univ (fun _:Fin n=>closedBall (0:E4) U))
  have compact:IsCompact B:=(isCompact_univ_pi (fun _:Fin n=>isCompact_closedBall (0:E4) U)).image (PiLp.continuous_toLp ..)
  have closed:IsClosed (shapes n U η):=by
    have eq:shapes n U η=(⋂i:Fin n,{z:Points n|‖z i‖≤U}) ∩
        (⋂i:Fin n,⋂j:Fin n,⋂_ : i≠j,{z:Points n|η≤‖z i-z j‖}):=by
      ext z
      simp only [shapes,mem_setOf,mem_inter_iff,mem_iInter]
    rw [eq]
    exact (isClosed_iInter fun i=>isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_iInter fun i=>isClosed_iInter fun j=>isClosed_iInter fun _=>isClosed_le continuous_const (by fun_prop))
  have lots:IsCompact (shapes n U η):=by
    refine compact.of_isClosed_subset closed ?_
    intro z hz
    refine ⟨z.ofLp,fun i _=>?_,rfl⟩
    rw [mem_closedBall_iff_norm,sub_zero]
    exact hz.1 i
  have safe:shapes n U η⊆conf n:=by
    intro z hz i j e
    by_contra hij
    have gap:=hz.2 i j hij
    rw [e,sub_self,norm_zero] at gap
    exact sep.not_ge gap
  obtain ⟨δ,pos,margin⟩:=lots.exists_cthickening_subset_open (conf_open n) safe
  refine ⟨cthickening δ (shapes n U η),lots.cthickening,margin,?_⟩
  intro z hz
  apply mem_of_superset (ball_mem_nhds z pos)
  intro x hx
  exact mem_cthickening_of_dist_le _ z _ _ hz (mem_ball.mp hx).le

end YM.Integration.WilsonOrdinaryNestedShapeTest
end
