import YM.Integration.WilsonCenteredCompactBooking
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Separation.Regular

/-! A single positive physical test pays the original cell mass at every
nonzero cover-grid sample of a compact separated roster, including points
on the boundary of a right-closed cell. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedLocatedCell
open Function Set Filter MeasureTheory Metric Extraction Lattice OPE Orbits Trace Table Spec
open Function Set MeasureTheory Table Spec Lattice Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Wilson RG Source PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame
open Finset RG12 Cells Push.GridApprox Trace.Physical.GermGraph RG16 RG16.Literal
open WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{n:ℕ}

theorem sites (R:Run G){r:ℝ}(hr:0<r)(z:UVIndex)(o:Fin n → Cover):
    segment (R.family.S.a z.1/r) o ⊆ cell R r z (wrap _ ∘ o):=by
  intro x hx
  change wrap _ ∘ address (R.family.S.a z.1) (r • x) = wrap _ ∘ o
  have eq:address (R.family.S.a z.1) (r • x)=address (R.family.S.a z.1/r) x:=by
    funext i a
    refine congrArg Int.ceil ?_
    change r*x i a/R.family.S.a z.1=x i a/(R.family.S.a z.1/r)
    field_simp [ne_of_gt hr,ne_of_gt (R.family.S.a_pos _)]
  rw [eq,show address (R.family.S.a z.1/r) x=o from hx]

theorem positive (R:Run G)(B:Test n)(real:∀x,0≤(B x).re){r:ℝ}(hr:0<r)(z:UVIndex)
    (o:Fin n → Cover)(inside:∀x∈segment (R.family.S.a z.1/r) o,0<(B x).re):
    mass R B r z (wrap _ ∘ o)≠0:=by
  let A:=cell R r z (wrap _ ∘ o)
  let E:=segment (R.family.S.a z.1/r) o
  let μ:=volume.restrict A
  have routed:E ⊆ A:=sites R hr z o
  have width:0<R.family.S.a z.1/r:=div_pos (R.family.S.a_pos _) hr
  have meas:MeasurableSet E:=measurable_segment width o
  have massE:0<μ E:=by
    rw [show μ E=volume (E∩A) from Measure.restrict_apply meas,inter_eq_self_of_subset_left routed,
      cell_volume width]
    exact ENNReal.ofReal_pos.mpr (pow_pos width _)
  have ready:Integrable (fun x:Points n=>B x) μ:=
    (B.continuous.integrable_of_hasCompactSupport B.hasCompactSupport).restrict
  have pos:0<∫x,(B x).re ∂μ:=(integral_pos_iff_support_of_nonneg real ready.re).2
    (massE.trans_le (measure_mono fun x hx=>ne_of_gt (inside x hx)))
  have actual:(∫x,(B x).re ∂μ)=(mass R B r z (wrap _ ∘ o)).re:=integral_re ready
  intro zero
  rw [actual,zero] at pos
  exact (lt_irrefl (0:ℝ)) pos

/-- Choose the test before the independent points and the two physical
regulators. Its cell mass is spent only as the native incidence condition. -/
theorem original {X:Set (Points n)}(compact:IsCompact X)(legal:X⊆conf n):
    ∃B:Test n,∃σ:ℝ,0<σ ∧ (∀x,0≤(B x).re) ∧ ∀(R:Run G){r:ℝ},0<r→∀z:UVIndex,
        (4*n:ℝ)*(R.family.S.a z.1/r)≤σ → ∀o:Fin n → Cover,tag (R.family.S.a z.1/r) o∈X →
          mass R B r z (wrap _ ∘ o)≠0:=by
  obtain ⟨U,opened,contains,licensed,finite⟩:=exists_open_between_and_isCompact_closure compact (conf_open n) legal
  obtain ⟨σ,sp,thick⟩:=compact.exists_cthickening_subset_open opened contains
  obtain ⟨f,support,smooth,range⟩:=opened.exists_contDiff_support_eq (n:=⊤)
  have nn(x:Points n):0≤f x:=(range ⟨x,rfl⟩).1
  let F:Points n→ℂ:=fun x=>(f x:ℂ)
  have enclosed:tsupport F⊆closure U:=by
    refine closure_mono fun x non=>?_
    rw [←support]
    intro h
    exact non (by simp [F,h])
  let B:Test n:=⟨F,Complex.ofRealCLM.contDiff.comp smooth,
    finite.of_isClosed_subset isClosed_closure enclosed,enclosed.trans licensed⟩
  have real(x:Points n):0≤(B x).re:=nn x
  refine ⟨B,σ,sp,real,?_⟩
  intro R r hr z fit o enrolled
  apply positive R B real hr z o
  intro x hx
  have index:address (R.family.S.a z.1/r) x=o:=hx
  have dist₀:=approximate (div_pos (R.family.S.a_pos z.1) hr) x
  rw [index] at dist₀
  have region:x∈U:=thick (mem_cthickening_of_dist_le x _ σ X enrolled ((dist_comm x _).trans_le (dist₀.trans fit)))
  rw [←support] at region
  exact lt_of_le_of_ne (nn x) (Ne.symm region)
end YM.Integration.WilsonIndependentConditionedLocatedCell
end
