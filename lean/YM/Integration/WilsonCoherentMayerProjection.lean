import YM.Integration.WilsonCoherentMayerNoise

/-! The source derivatives use only the submitted finite stencils in the
original centered Gaussian. Its covariance is the pushforward of the same
sample under the actual forest restrictions, including coincident bonds. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerProjection
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert ProbabilityTheory
open scoped Topology BigOperators ContDiff Classical

variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] (d:I→ℕ)
  {c f:Side} {S:StepData c f} (F:Forest S.ratio) (o:I→Site f)

abbrev Panels := ∀ i, Dict06.Wil.Panel (R.family.localSection (d i)).stencil G

def restrict : Air f G →L[ℝ] Panels R d :=
  ({ toFun:=fun z i=>Dict06.Wil.restrictLog (R.family.localSection (d i)).stencil
       (expandAt (o i) (WilsonCoherentMayerNoise.row F z))
     map_add':=by
       intro z w
       funext i l
       let e:Bond f:=(wrap f l.val.1+o i,l.val.2)
       by_cases h:e∈F.trunks <;>
         simp [Dict06.Wil.restrictLog,expandAt,WilsonCoherentMayerNoise.row,show (wrap f l.val.1+o i,l.val.2)=e from rfl,h]
       all_goals rfl
     map_smul':=by
       intro t z
       funext i l
       let e:Bond f:=(wrap f l.val.1+o i,l.val.2)
       by_cases h:e∈F.trunks <;>
         simp [Dict06.Wil.restrictLog,expandAt,WilsonCoherentMayerNoise.row,show (wrap f l.val.1+o i,l.val.2)=e from rfl,h]
       all_goals rfl
      }:Air f G →ₗ[ℝ] Panels R d).toContinuousLinearMap

variable (θ:ℝ) (y:∀i,R.family.label (d i))

def content (a:Panels R d):ℂ :=
  ∏ i, Dict06.Wil.echo (R.family.localSection (d i))
    ((R.family.labels.level (d i)).scaled θ⁻¹ (y i)) (a i)

theorem smooth : ContDiff ℝ ω (content R d θ y) :=by
  unfold content
  generalize (univ:Finset I)=s
  induction s using Finset.induction_on with
  | empty=>simp only [prod_empty]; exact contDiff_const
  | insert i s hi ih=>
    simp_rw [prod_insert hi]
    exact ((Dict06.Wil.echo_smooth (R.family.localSection (d i)) _).comp
      (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun i:I=>Dict06.Wil.Panel (R.family.localSection (d i)).stencil G) i).contDiff).mul ih

def books (z:Air f G):PowerSeries ℂ :=
  ∏ i, Dict06.Wil.book (R.family.localSection (d i))
    ((R.family.labels.level (d i)).scaled θ⁻¹ (y i)) (expandAt (o i) (WilsonCoherentMayerNoise.row F z))

theorem graded (e:ℕ) (z:Air f G):
    PowerSeries.coeff e (books R d F o θ y z)=
      Tensor.diagonal (Tensor.coeff (content R d θ y) e 0) (restrict R d F o z) :=by
  let A:=restrict R d F o z
  let f' (i:I) (t:ℝ):=Dict06.Wil.echo (R.family.localSection (d i))
     ((R.family.labels.level (d i)).scaled θ⁻¹ (y i)) (t•A i)
  have each i:ps (f' i)=Dict06.Wil.book (R.family.localSection (d i))
      ((R.family.labels.level (d i)).scaled θ⁻¹ (y i)) (expandAt (o i) (WilsonCoherentMayerNoise.row F z)):=by
    rw [← Dict06.Wil.echo_book]
    simp_rw [Dict06.Wil.echo_exact]
    rfl
  have all:=Dict06.Tags.ps_product f' univ (fun i _=>
    ((Dict06.Wil.echo_smooth _ _).comp (contDiff_id.smul contDiff_const)).contDiffAt.of_le le_top)
  have h:ps (fun t:ℝ=>content R d θ y (t•A))=books R d F o θ y z:=by
    rw [show (fun t:ℝ=>content R d θ y (t•A))=∏i,f' i from funext fun t=>by
      simp only [content,Finset.prod_apply]; rfl]
    exact all.2.trans (prod_congr rfl (fun i _=>each i))
  rw [←h,ps_at]
  exact radial_eq e ((smooth R d θ y).contDiffAt.of_le le_top) A

theorem price (e:ℕ) (phase:ℂ→L[ℝ]ℝ) (z:Air f G):
    |phase (PowerSeries.coeff e (books R d F o θ y z))| ≤
      ‖phase‖*‖Tensor.coeff (content R d θ y) e 0‖*‖restrict R d F o z‖^e :=by
  rw [graded,←Real.norm_eq_abs,mul_assoc]
  apply (phase.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa [Tensor.diagonal] using (Tensor.coeff (content R d θ y) e 0).le_opNorm (fun _=>restrict R d F o z)

theorem integrable {T:Tube G S} (X:Coat T F) (e:ℕ) (phase:ℂ→L[ℝ]ℝ):
    Integrable (fun z=>phase (PowerSeries.coeff e (books R d F o θ y z))) X.dice :=by
  let L:=restrict R d F o
  let μ:=X.dice
  haveI : IsGaussian μ:=inferInstanceAs (IsGaussian (multivariateGaussian 0 X.relating))
  have hm : Integrable (fun a:Panels R d=>‖a‖^e) (μ.map L) :=
    MemLp.integrable_norm_pow' (p:=e) (f:=id) (IsGaussian.memLp_id (μ.map L) _ (by simp))
  have hL:Integrable (fun z=>‖L z‖^e) μ:=
    (integrable_map_measure (by fun_prop) L.continuous.aemeasurable).mp hm
  have cont : Continuous (fun z=>phase (PowerSeries.coeff e (books R d F o θ y z))) :=by
    simp_rw [graded]
    exact phase.continuous.comp ((Tensor.diag_smooth _ 1).continuous.comp L.continuous)
  exact (hL.const_mul (‖phase‖*‖Tensor.coeff (content R d θ y) e 0‖)).mono'
    cont.aestronglyMeasurable (Eventually.of_forall (fun z=>price R d F o θ y e phase z))

end YM.Integration.WilsonCoherentMayerProjection
