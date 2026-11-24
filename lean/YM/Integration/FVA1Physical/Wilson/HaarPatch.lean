import YM.Integration.FVA1Physical.Wilson.BoundaryRows
import YM.LocalH.Chart

/-! An actual positive product-Haar neighborhood for the inherited marked comparison.
The local logarithm and the path to every tested configuration are constructed here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Metric Tree Precision Exterior RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {f : Side}
local notation "𝒳" => Positions (Primary f G)

def exponentialPatch (G : Gauge) := G.lieExp '' ball 0 (LocalH.geom_patch G).choose

def logWithin (G : Gauge) := (exponentialPatch G).piecewise (LocalH.snap G) (fun _=>0)

private theorem chartGeom (G : Gauge) : LocalH.Geom G (exponentialPatch G) (ball 0 (LocalH.geom_patch G).choose) :=
  (LocalH.geom_patch G).choose_spec.2 _ le_rfl

theorem logWithin_meas (G : Gauge) : Measurable (logWithin G) := by
  obtain ⟨op,_,_,_,_,_,hot⟩ := chartGeom G
  apply ContinuousOn.measurable_piecewise _ continuousOn_const op.measurableSet
  intro U hU
  exact ((hot _ hU).continuousAt.comp (G.continuous_mat.continuousAt (x:=U))).continuousWithinAt

theorem logWithin_hot (U : G.El) (hU : U∈exponentialPatch G) : ContinuousAt (logWithin G) U := by
  obtain ⟨op,_,_,_,_,_,hot⟩ := chartGeom G
  apply ((hot _ hU).continuousAt.comp (G.continuous_mat.continuousAt (x:=U))).congr_of_eventuallyEq
  filter_upwards [op.mem_nhds hU] with a ha
  exact Set.piecewise_eq_of_mem _ _ _ ha

def chartLog (g : ℝ) (U : Config G f) : 𝒳 :=
  g⁻¹ • (panel G f).symm (fun e=> logWithin G (U e))

private def fields (G : Gauge) (f : Side) : Set (Config G f) := fun U=>∀ e,U e∈exponentialPatch G

private theorem fields_open (G : Gauge) (f : Side) : IsOpen (fields G f) := by
  have eq : fields G f = Set.univ.pi (fun _=>exponentialPatch G) := by
    ext U; exact Set.mem_univ_pi.symm
  rw [eq]
  exact isOpen_set_pi finite_univ fun _ _=>(chartGeom G).1

theorem chartLog_meas (g : ℝ) : Measurable (chartLog (G:=G) (f:=f) g) := by
  have src := measurable_pi_lambda (fun U : Config G f=>fun e=>logWithin G (U e)) fun e=> (logWithin_meas G).comp (measurable_pi_apply e)
  exact ((panel G f).symm.continuous.measurable.comp src).const_smul g⁻¹

private theorem chartLog_hot (g : ℝ) (U : Config G f) (hU : U∈fields G f) :
    ContinuousAt (chartLog g) U := by
  have src : ContinuousAt (fun V : Config G f=>fun e=>logWithin G (V e)) U :=
    by
      rw [continuousAt_pi]
      intro e
      change ContinuousAt (fun V : Config G f=>logWithin G (V e)) U
      have project : ContinuousAt (fun V : Config G f=>V e) U := (continuous_apply e).continuousAt
      exact ContinuousAt.comp (f:=fun V : Config G f=>V e) (logWithin_hot (U e) (hU e)) project
  exact ((panel G f).symm.continuous.continuousAt.comp src).const_smul g⁻¹

theorem recover_chartLog {g : ℝ} (hg : g ≠ 0) (U : Config G f) (hU : ∀ e, U e ∈ exponentialPatch G) :
    palace (g • chartLog g U) = U := by
  rw [chartLog,smul_inv_smul₀ hg]
  unfold palace
  rw [ContinuousLinearEquiv.apply_symm_apply]
  obtain ⟨_,_,_,inv,_,_,_⟩ := chartGeom G
  funext e
  change G.lieExp (logWithin G (U e)) * 1 = U e
  rw [logWithin,Set.piecewise_eq_of_mem _ _ _ (hU e),mul_one]
  exact inv (hU e)

theorem enter_chartLog {g : ℝ} (hg : g ≠ 0) (x : 𝒳)
    (small : ∀ e, ‖g • panel G f x e‖ < (LocalH.geom_patch G).choose) :
    palace (g • x)∈fields G f ∧ chartLog g (palace (g • x))=x := by
  obtain ⟨_,_,inv,_,_,openE,_⟩ := chartGeom G
  have id (e) : palace (g • x) e= G.lieExp (g • panel G f x e) := by
    rw [palace,map_smul]; exact mul_one _
  have within (e) : g • panel G f x e ∈ ball 0 (LocalH.geom_patch G).choose :=
    mem_ball_zero_iff.mpr (small e)
  have box : palace (g • x)∈fields G f := fun e => (id e).symm ▸ openE (within e)
  refine ⟨box,?_⟩
  have logid : (fun e=> logWithin G (palace (g • x) e))=panel G f (g • x) := by
    funext e
    rw [logWithin,Set.piecewise_eq_of_mem _ _ _ (box e),id,map_smul]
    exact inv (within e)
  rw [chartLog,logid,ContinuousLinearEquiv.symm_apply_apply,inv_smul_smul₀ hg]

def haarPatch (g w H : ℝ) (x : 𝒳) : Set (Config G f) :=
  fields G f ∩ {U | (∑ i, |(chartLog g U - x) i|) < min H (w-‖x‖)}

theorem haarPatch_meas (g w H : ℝ) (x : 𝒳) : MeasurableSet (haarPatch g w H x) := by
  apply (fields_open G f).measurableSet.inter
  apply measurableSet_lt _ measurable_const
  apply Finset.measurable_fun_sum
  intro i _
  exact ((measurable_pi_apply i).comp ((chartLog_meas g).sub measurable_const)).abs

theorem haarPatch_mass {g w H : ℝ} (hg : g ≠ 0) (hH : 0<H) (x : 𝒳) (hx : ‖x‖<w)
    (small : ∀ e, ‖g • panel G f x e‖ < (LocalH.geom_patch G).choose) :
    0 < (prior G f) (haarPatch g w H x) := by
  let U := palace (g • x)
  obtain ⟨box,recover⟩ := enter_chartLog hg x small
  have test : ContinuousAt (fun V : Config G f=>(∑ i, |(chartLog g V-x) i|)) U := by
    have one (i : Primary f G) : ContinuousAt (fun V : Config G f => |(chartLog g V-x) i|) U :=
      ((continuous_apply i).continuousAt.comp ((chartLog_hot g U box).sub continuousAt_const)).abs
    have sum (I : Finset (Primary f G)) : ContinuousAt (fun V : Config G f => ∑ i∈I, |(chartLog g V-x) i|) U := by
      induction I using Finset.induction_on with
      | empty => simpa only [Finset.sum_empty] using (continuousAt_const (x:=U) (y:=(0:ℝ)))
      | insert i I hi ih =>
        simp only [Finset.sum_insert hi]
        convert (one i).add ih using 1
        funext v; rfl
    exact sum Finset.univ
  have positive : (∑ i, |(chartLog g U - x) i|) < min H (w-‖x‖) := by
    rw [show chartLog g U=x from recover,sub_self]
    simpa using lt_min hH (sub_pos.mpr hx)
  haveI : (prior G f).IsOpenPosMeasure := by unfold prior;infer_instance
  apply Measure.measure_pos_of_mem_nhds (prior G f) (x:=U)
  exact inter_mem ((fields_open G f).mem_nhds box) (test.preimage_mem_nhds (gt_mem_nhds positive))

theorem haarPatch_point {g w H : ℝ} (hg : g ≠ 0) (x : 𝒳) (U : Config G f) (hu : U ∈ haarPatch g w H x) :
    let v := fun A : Config G f=>chartLog g A-x
    palace (g • (x+v U))=U ∧ (∑ i, |v U i|) ≤ H ∧
      ∀ t∈Set.Icc (0:ℝ) 1, x+t • v U ∈ closedBall 0 w := by
  intro v
  have size : (∑ i, |v U i|) < min H (w-‖x‖) := hu.2
  have cost : ‖v U‖ ≤ ∑ i, |v U i| := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _=> abs_nonneg _)).mpr
    intro i
    exact Finset.single_le_sum (f:=fun j=> |v U j|) (fun _ _=>abs_nonneg _) (Finset.mem_univ i)
  refine ⟨?_,size.le.trans (min_le_left ..),?_⟩
  · change palace (g • (x+(chartLog g U-x)))=U
    rw [show x+(chartLog g U-x)=chartLog g U by abel, recover_chartLog hg U hu.1]
  intro t ht
  apply mem_closedBall_zero_iff.mpr
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_of_nonneg ht.1]
  have hh := (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (v U))).trans_eq (one_mul _)
  linarith only [hh,cost,size.le.trans (min_le_right ..)]

theorem haarPatch_good {g w H : ℝ} (hg : g ≠ 0) (x : 𝒳) :
    let μ := (prior G f).restrict (haarPatch g w H x)
    let v : Config G f→𝒳 := fun U=>chartLog g U-x
    AEMeasurable v μ ∧ ∀ᵐ U ∂μ, palace (g • (x+v U))=U ∧ (∑ i, |v U i|) ≤ H ∧
      ∀ t∈Set.Icc (0:ℝ) 1, x+t • v U ∈ closedBall 0 w := by
  intro μ v
  have meas := haarPatch_meas g w H x
  refine ⟨((chartLog_meas g).sub measurable_const).aemeasurable,?_⟩
  filter_upwards [ae_restrict_mem meas] with U hu
  exact haarPatch_point hg x U hu

end YM.Integration.FVA1Physical.Wilson
