import YM.Integration.WilsonRetainedSignedStencilTaylor
import YM.Integration.WilsonCoherentMayerProjection

/-! Independently project the coefficients of every original Wilson book, then multiply in the real power series ring. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRetainedSignedStencilBooks
open Function Lattice RG Pressure Tree Wilson Source ConnectedActivityE6
open Pressure.Stores Pressure.Tube Push Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt
open RGLocalTaylor RGLocalTaylor.Insert PhysicalNext.Repeat.Legato Finset Dict06.Series
open WilsonCoherentMayerProjection (restrict Panels)
open WilsonRetainedSignedStencilTaylor
open AnalyticBridge.LocalGaussianLaws Precision
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

def sheet (φ:Reading)(B:PowerSeries ℂ):PowerSeries ℝ:=
  PowerSeries.mk fun j=>φ (PowerSeries.coeff j B)

private theorem product_germ {I:Type}(f:I→ℝ→ℝ)(s:Finset I)
    (he:∀i∈s,ContDiffAt ℝ ∞ (f i) 0):
    ContDiffAt ℝ ∞ (∏i∈s,f i) 0 ∧ ps (∏i∈s,f i)=∏i∈s,ps (f i):=by
  induction s using Finset.induction_on with
  | empty=>rw [prod_empty,prod_empty];exact ⟨contDiffAt_const,ps_one⟩
  | insert a s ha ih=>
    obtain ⟨hr,hp⟩:=ih (fun i hi=>he i (mem_insert_of_mem hi))
    have hu:=he a (mem_insert_self ..)
    rw [prod_insert ha,prod_insert ha]
    exact ⟨hu.mul hr,(ps_mul _ _ hu hr).trans (by rw [hp])⟩

variable {G:Gauge}(R:Run G){I:Type}[Fintype I](d:I→ℕ)
variable {c f:Side}{S:StepData c f}(F:Forest S.ratio)(o:I→Site f)
variable (φ:I→Reading)(θ:ℝ)(y:∀i,R.family.label (d i))

def row (A:Panels R d):ℝ:=
  ∏i,φ i (Dict06.Wil.echo (R.family.localSection (d i)) ((R.family.labels.level (d i)).scaled θ⁻¹ (y i)) (A i))

def books (z:Air f G):PowerSeries ℝ:=
  ∏i,sheet (φ i) (Dict06.Wil.book (R.family.localSection (d i))
    ((R.family.labels.level (d i)).scaled θ⁻¹ (y i)) (expandAt (o i) (WilsonCoherentMayerNoise.row F z)))

theorem issued (z:Air f G):
    ContDiffAt ℝ ∞ (fun t:ℝ=>row R d φ θ y (t•restrict R d F o z)) 0 ∧
    ps (fun t:ℝ=>row R d φ θ y (t•restrict R d F o z))=books R d F o φ θ y z:=by
  let A:=restrict R d F o z
  let raw (i:I)(t:ℝ):=Dict06.Wil.echo (R.family.localSection (d i))
    ((R.family.labels.level (d i)).scaled θ⁻¹ (y i)) (t•A i)
  have sm (i:I):ContDiffAt ℝ ω (raw i) 0:=
    ((Dict06.Wil.echo_smooth _ _).comp (contDiff_id.smul contDiff_const)).contDiffAt
  have germ (i:I):ps (raw i)=Dict06.Wil.book (R.family.localSection (d i))
      ((R.family.labels.level (d i)).scaled θ⁻¹ (y i)) (expandAt (o i) (WilsonCoherentMayerNoise.row F z)):=by
    rw [←Dict06.Wil.echo_book]
    simp_rw [Dict06.Wil.echo_exact]
    rfl
  have each (i:I):ps (fun t=>φ i (raw i t))=sheet (φ i) (ps (raw i)):=by
    ext1 j
    rw [ps_at,sheet,PowerSeries.coeff_mk,ps_at]
    exact ordinary_map (raw i) j ((sm i).of_le le_top) (φ i)
  have all:=product_germ (fun i t=>φ i (raw i t)) univ (fun i _=>(φ i).contDiff.contDiffAt.comp 0 ((sm i).of_le le_top))
  rw [show (fun t:ℝ=>row R d φ θ y (t•restrict R d F o z))=∏i,(fun t=>φ i (raw i t)) from funext fun t=>by
    simp only [row,Finset.prod_apply];rfl]
  exact ⟨all.1,all.2.trans (prod_congr rfl fun i _=>(each i).trans (congrArg (sheet (φ i)) (germ i)))⟩

theorem graded (z:Air f G)(j:ℕ):
    ordinary j (fun t:ℝ=>material R d φ (fun i=>(R.family.labels.level (d i)).scaled θ⁻¹ (y i))
      (t•restrict R d F o z))=(PowerSeries.coeff j (books R d F o φ θ y z):ℝ):=by
  let V:=fun t:ℝ=>row R d φ θ y (t•restrict R d F o z)
  obtain ⟨sm,bought⟩:=issued R d F o φ θ y z
  have hf:ContDiffAt ℝ j V 0:=sm.of_le (WithTop.coe_le_coe.mpr le_top)
  have line:ordinary j V=PowerSeries.coeff j (books R d F o φ θ y z):=by
    simpa only [ps_at] using congrArg (PowerSeries.coeff j) bought
  rw [show (fun t:ℝ=>material R d φ (fun i=>(R.family.labels.level (d i)).scaled θ⁻¹ (y i))
      (t•restrict R d F o z))=Complex.ofRealCLM ∘ V from funext fun t=>real_product R d φ _ _,
    ordinary_map V j hf,line]
  rfl

end YM.Integration.WilsonRetainedSignedStencilBooks
