import YM.SchemeRG11.Cluster.Bells

/-! Meromorphic reading regular on separated supports for tripod. Same in IR removal. -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.SchemeRG11.Cluster
open Set MeasureTheory Filter Metric Function Hot MSbar
open scoped Topology ContDiff BigOperators Classical
variable {n : ℕ}

def box (A B C : ℝ) : Set Time := Ioc 0 A ×ˢ Ioc 0 B ×ˢ Ioc 0 C
def badge (μ A B C : ℝ) (l : Sweep n) (e : ℂ) (x : Nodes n) := ∫ p in box A B C, spin μ l p e x
def finale (μ : ℝ) (l : Sweep n) (x : Nodes n) := ∫ p in tripod, spin μ l p 0 x
lemma box_meas (A B C : ℝ) : MeasurableSet (box A B C) := measurableSet_Ioc.prod (measurableSet_Ioc.prod measurableSet_Ioc)
lemma box_wise (A B C : ℝ) : box A B C ⊆ tripod := prod_mono Ioc_subset_Ioi_self (prod_mono Ioc_subset_Ioi_self Ioc_subset_Ioi_self)
lemma knot_box {A B C : ℝ} {p : Time} (hp : p ∈ box A B C) : knot p ≤ A*B+A*C+B*C := by
  have ha : p.1∈Ioc 0 A:=hp.1
  have hb : p.2.1∈Ioc 0 B:=hp.2.1
  have hc : p.2.2∈Ioc 0 C:=hp.2.2
  have hm := le_trans ha.1.le ha.2; have hn := le_trans hb.1.le hb.2
  exact add_le_add (add_le_add (mul_le_mul ha.2 hb.2 hb.1.le hm) (mul_le_mul ha.2 hc.2 hc.1.le hm)) (mul_le_mul hb.2 hc.2 hc.1.le hn)
lemma postage (A B C : ℝ) : volume (box A B C)<⊤ := by
  unfold box; rw [show (volume: Measure Time)=Measure.prod volume volume from rfl,Measure.prod_prod,show (volume:Measure (ℝ×ℝ))=Measure.prod volume volume from rfl,Measure.prod_prod]; simp; finiteness

variable {μ : ℝ} (hμ : 0<μ) (l : Sweep n) {A B C : ℝ} {x : Nodes n} (hx : x∈ clearance n)
include hμ
lemma blade {U : Set Time} (hu : MeasurableSet U) (h : U⊆tripod) (z : ℂ) (x : Nodes n) :
    AEStronglyMeasurable (fun p=> spin μ l p z x) (volume.restrict U) :=
    ContinuousOn.aestronglyMeasurable (fun p hp=> (crew hμ l (p:=p) (x:=p) (globe p (h hp)) continuousAt_const (hF:=continuousAt_id) continuousAt_const rfl).continuousWithinAt) hu
include hx
lemma horn (z : ℂ) : IntegrableOn (fun p=> spin μ l p z x) (box A B C) := by
  obtain ⟨T,hT,h⟩:= flash hμ isCompact_singleton (singleton_subset_iff.mpr hx) l (isCompact_singleton (x:=z)) (A*B+A*C+B*C)
  exact (integrableOn_const (postage A B C).ne (C:=T)).mono' (blade hμ l (box_meas ..) (box_wise ..) z x) (ae_restrict_of_forall_mem (box_meas ..) (fun p hp=> h _ rfl _ rfl p (box_wise A B C hp) (knot_box hp)))

lemma suffix : Differentiable ℂ (fun e=>badge μ A B C l e x) := by
  intro z
  obtain ⟨T,hT,h⟩:= flash hμ isCompact_singleton (singleton_subset_iff.mpr hx) l (isCompact_closedBall z 1) (A*B+A*C+B*C)
  refine diffuse (F:=fun e p=>spin μ l p e x) (s:=closedBall z 1) (closedBall_mem_nhds z zero_lt_one) (Eventually.of_forall fun e=> blade hμ l (box_meas ..) (box_wise ..) e x) ?_ (integrableOn_const (postage A B C).ne (C:=T))
  exact ae_restrict_of_forall_mem (box_meas ..) (fun p hp y hy=> ⟨webs hμ l p (globe p (box_wise A B C hp)) x y,h x rfl y hy p (box_wise A B C hp) (knot_box hp)⟩)
lemma fades : IntegrableOn (fun p=>spin μ l p 0 x) tripod := by
  obtain ⟨T,hT,h⟩:=Cluster.respite hμ isCompact_singleton (singleton_subset_iff.mpr hx) l
  exact (compass.const_mul T).mono' (blade hμ l tripod_meas Subset.rfl _ _) (ae_restrict_of_forall_mem tripod_meas (fun p hp=> by simpa only [div_eq_mul_inv] using h p hp x rfl))
lemma walks : ContinuousAt (badge μ A B C l 0) x := by
  obtain ⟨K,hK,hx,h⟩:= exists_compact_subset clearance_open hx
  obtain ⟨T,hT,e⟩:= Cluster.respite hμ hK h l
  have he : ∀ᶠ y in 𝓝 x,y∈K:=mem_interior_iff_mem_nhds.mp hx
  refine tendsto_integral_filter_of_dominated_convergence (F:=fun y p=> spin μ l p 0 y) (l:=𝓝 x) (μ:=volume.restrict (box A B C)) (fun p=> T*(wages p)⁻¹) (Eventually.of_forall (fun z=> blade hμ l (box_meas ..) (box_wise ..) _ z)) (he.mono fun y hy=> ae_restrict_of_forall_mem (box_meas ..) fun p hp=> by simpa only [div_eq_mul_inv] using e p (box_wise A B C hp) y hy) ((compass.mono_set (box_wise A B C)).const_mul _) (ae_restrict_of_forall_mem (box_meas ..) fun p hp=> crew hμ l (p:=p) (F:=fun _ : Nodes n=>p) (globe p (box_wise A B C hp)) continuousAt_id continuousAt_const continuousAt_const rfl)

/-- Read first, remove the individual times later. -/
theorem rolling {X : Type} {v : Filter X} [v.IsCountablyGenerated] {a b c : X→ℝ}
    (ha : Tendsto a v atTop) (hb : Tendsto b v atTop) (hc : Tendsto c v atTop) {y : X→Nodes n} (hy : Tendsto y v (𝓝 x)) : Tendsto (fun Y=>badge μ (a Y) (b Y) (c Y) l 0 (y Y)) v (𝓝 (finale μ l x)) := by
  let S (w):=box (a w) (b w) (c w)
  let F w:= (S w).indicator (fun p=>spin μ l p 0 (y w))
  obtain ⟨K,hK,hx,h⟩:= exists_compact_subset clearance_open hx
  obtain ⟨T,hT,h'⟩:= Cluster.respite hμ hK h l
  have he : ∀ᶠ p in v, y p∈K:= hy.eventually (show ∀ᶠ y in 𝓝 x,y∈K from mem_interior_iff_mem_nhds.mp hx)
  have ht:=tendsto_integral_filter_of_dominated_convergence (l:=v) (F:=F) (μ:=volume.restrict tripod) (f:=fun p=> spin μ l p 0 x) (fun p=>T*(wages p)⁻¹) (Eventually.of_forall fun t=> (blade hμ l tripod_meas Subset.rfl _ _).indicator (box_meas ..))
    (he.mono fun Y hY=> ae_restrict_of_forall_mem tripod_meas (fun p hp=> by
       by_cases hu:p∈S Y
       · simpa only [F,indicator_of_mem hu,div_eq_mul_inv] using h' p hp _ hY
       simp only [F,indicator_of_notMem hu,norm_zero]; have hh:=wag p hp; positivity)) (compass.const_mul _)
    (ae_restrict_of_forall_mem tripod_meas (fun p hp=> by
       have hu := (crew hμ l (p:=p) (F:=fun _ : Nodes n=>p) (e:=fun _=>0) (x:=x) (globe p hp) continuousAt_id continuousAt_const continuousAt_const rfl).tendsto.comp hy
       refine hu.congr' ?_
       filter_upwards [ha.eventually (eventually_ge_atTop p.1),hb.eventually (eventually_ge_atTop p.2.1),hc.eventually (eventually_ge_atTop p.2.2)] with Y hA hB hC
       have hS : p∈S Y := ⟨⟨hp.1,hA⟩,⟨hp.2.1,hB⟩,⟨hp.2.2,hC⟩⟩
       exact Eq.symm (indicator_of_mem hS _)))
  apply ht.congr'
  filter_upwards with t
  change (∫ p in tripod, (S t).indicator _ p) = _; rw [setIntegral_indicator (box_meas ..),inter_eq_self_of_subset_right (box_wise ..)]; rfl
end YM.SchemeRG11.Cluster
