import YM.Integration.WilsonThermometerPositionFilmMaterials
import YM.Integration.WilsonThermometerVertexVariation

/-! The complete normalized marked socket in the true lower forest chart. Both estimates use the same group field and preserve the entire partition sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmChartContact
open Function Finset Filter RG Lattice Wilson Tree Precision Exterior Marker Multi
open PertExtension.Series PertExtension.Series.Tested
open Comparison.RG02 Comparison.RG02.Assembly Comparison.RG02.Laplace Comparison.RG02.Moving
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {R:Census V} {c f:Side}
    (S:StepData c f) (F:Forest S.ratio) (C:Bulk.Colors R G f) (s:R.Mode)

def flat (n:ℕ) (y:fieldDir G f 1) : ℂ :=
  rows (fun x=>markExp (curve C.power (fun i=>Bulk.projected (C.mark i)) x)) s n (1,y)

def bent (n:ℕ) (u:Bulk.SliceDir S F G) : ℂ :=
  rows (fun x=>markExp (curve C.power (Bulk.markFn S F C) x)) s n (1,u)

def seen (u:Bulk.SliceDir S F G) (t:ℝ) : ℂ :=
  (Poly.pass (Integral.markedLog t (Work.F03.live F (t•u)) C)).part s

private theorem stocks {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (ls:Hot R→E→ℂ) (grade:∀i,GradeAt (C.power i) (ls i)) :
    Zonal (Radial.zone (E:=E)) 1 (fun t x=>(smoothMark C.power ls t x).pass)
      (fun x=>markExp (curve C.power ls x)) := by
  apply power_zonal (f:=smoothMark C.power ls)
  apply mark_test C.power ls (0:E→ℝ)
  refine ⟨⟨contDiffAt_const,rfl,?_⟩,?_⟩
  · intro u
    simp [Radial.jet]
  · intro i
    refine ⟨(grade i).smooth.of_le le_top,?_⟩
    intro n hn u
    simp only [Assembly.jet,(grade i).vanish n hn,zero_apply,smul_zero]

theorem current (hw:∀i,GradeAt (C.power i) (Bulk.projected (C.mark i))) (u:Bulk.SliceDir S F G) :
    Trial (fun b=>bent S F C s b u) (seen S F C s u) 1 := by
  let z:ℝ×Bulk.SliceDir S F G := (1,u)
  have sale:=stocks C (Bulk.markFn S F C) (fun i=>Bulk.joint_receipt S F (hw i)) s
  have pass:=Moving.Path.encounter (p:=fun _=>z) (W:=1) (by exact continuousAt_const)
    (by exact continuousAt_const.add continuous_norm.continuousAt) continuousAt_const (sale.fits 1)
  apply bill_congr (x:=fun t=>((smoothMark C.power (Bulk.markFn S F C) t z).pass.part s)-
      (Zone.eval (rows (fun x=>markExp (curve C.power (Bulk.markFn S F C) x)) s) 1 t z)) _ pass
  filter_upwards with t
  simp only [seen,bent,peval,Zone.eval,Pi.sub_apply,Integral.markedLog,smoothMark,divided,Bulk.markFn,
    Bulk.posed,z,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_one]

private def coord (u:Bulk.SliceDir S F G) (t:ℝ) : fieldDir G f 1 :=
  dslope (fun h:ℝ=>Work.F03.axisLog F (h•u)) 0 t

private theorem coord_smooth (u:Bulk.SliceDir S F G) : ContinuousAt (coord S F u) 0 := by
  have h:ContDiffAt ℝ ω (fun t:ℝ=>Work.F03.axisLog F (t•u)) 0:=by
    have inner:ContDiffAt ℝ ω (fun t:ℝ=>t•u) 0:=contDiffAt_id.smul contDiffAt_const
    have angular:ContDiffAt ℝ ω (Work.F03.axisLog F (G:=G)) ((0:ℝ)•u):=by
      rw [zero_smul]
      exact (Work.F03.inclusion_smooth F).snd
    exact angular.comp 0 inner
  exact continuousAt_dslope_same.mpr (h.differentiableAt (by simp))

private theorem placed (u:Bulk.SliceDir S F G) : ∀ᶠ t in along,
    represent (t•coord S F u t)=Work.F03.live F (t•u) := by
  have h:∀ᶠ t in 𝓝 (0:ℝ), represent (Work.F03.axisLog F (t•u))=Work.F03.live F (t•u):=by
    have h₀:ContinuousAt (fun t:ℝ=>t•u) 0:=continuousAt_id.smul continuousAt_const
    have step:Tendsto (fun t:ℝ=>t•u) (𝓝 0) (𝓝 0):=by simpa only [zero_smul] using h₀.tendsto
    exact (Work.F03.inclusion_works (G:=G) F).comp_tendsto step
  filter_upwards [nhdsWithin_le_nhds h,Tested.eventually_pos] with t ht pos
  rw [coord,dslope_of_ne _ pos.ne',slope_def_module,sub_zero,zero_smul,
    show Work.F03.axisLog F (0:Bulk.SliceDir S F G)=0 from congrArg Prod.snd (Work.F03.inclusion_zero F),
    sub_zero,smul_smul,mul_inv_cancel₀ pos.ne',one_smul,ht]

theorem ray (hw:∀i,GradeAt (C.power i) (Bulk.projected (C.mark i))) (u:Bulk.SliceDir S F G) :
    Bill 2 (fun t=>seen S F C s u t-(flat C s 0 (coord S F u t)+ t • flat C s 1 (coord S F u t))) := by
  let follow:=fun t:ℝ=>((1:ℝ),coord S F u t)
  have continuousFollow:ContinuousAt follow 0:=continuousAt_const.prodMk (coord_smooth S F u)
  have sale:=stocks C (fun i=>Bulk.projected (C.mark i)) hw s
  have pass:=Moving.Path.encounter (p:=follow) (W:=1) (by exact continuousAt_const)
    (by exact continuousAt_const.add continuous_norm.continuousAt) continuousFollow (sale.fits 1)
  refine bill_congr (x:=fun t=>((smoothMark C.power (fun i=>Bulk.projected (C.mark i)) t (follow t)).pass).part s-
    Zone.eval (rows (fun x=>markExp (curve C.power (fun i=>Bulk.projected (C.mark i)) x)) s) 1 t (follow t)) ?_ pass
  filter_upwards [placed S F u] with t ht
  simp only [Zone.eval,sum_range_succ,sum_range_zero,pow_zero,pow_one,one_smul,zero_add,flat,seen,
    Integral.markedLog,smoothMark,divided,Bulk.projected,follow,Prod.smul_fst,Prod.smul_snd,
    smul_eq_mul,mul_one,ht]

end YM.Integration.WilsonThermometerPositionFilmChartContact
