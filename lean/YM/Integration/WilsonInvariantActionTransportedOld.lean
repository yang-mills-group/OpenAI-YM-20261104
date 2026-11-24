import YM.Integration.WilsonInvariantActionOriginalQCarry

/-! Submitting the complete previously paid regular sector as a centered
test of the genuine earlier Wilson conditional, at arbitrary original dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionTransportedOld
open Function Filter Finset MeasureTheory Lattice RG Wilson Precision Marker Multi
open RG3.Script.Picnic Source OPE.Therm Pert.Asymptotics MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato
open WilsonInvariantActionMixedMaterial LocalComparison IterationFour.Vacuum
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N p j l:ℕ}

def reading (jl:j≤l) (live:l≤N) (w:R.family.label 4) (y:Site (R.family.side l p)) (I:Set ℕ) :=
  actualTransport R.family (N:=N) (earlier R.makes live w y I) jl

def centered (jl:j≤l) (live:l≤N) (w:R.family.label 4) (y:Site (R.family.side l p)) (I:Set ℕ)
    (U:Config G (R.family.side j p)):ℂ:=
  reading R jl live w y I U - ∫V,reading R jl live w y I V ∂scene R.family.path N p j

theorem billed (jl:j≤l) (live:l≤N) (birth:R.family.ref 4≤l) (w:R.family.label 4)
    (y:Site (R.family.side l p)) (I:Set ℕ)
    (F:Config G (R.family.side j p)→ℂ) (hF:Integrable (fun U=>‖F U‖) (scene R.family.path N p j)):
    ‖∫U,F U*centered R jl live w y I U ∂scene R.family.path N p j‖≤
      2*budget w l N p*∫U,‖F U‖ ∂scene R.family.path N p j:=by
  let μ:=scene R.family.path N p j
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson (jl.trans live)
  let c:=budget w l N p
  have old:∀U,‖earlier R.makes live w y I U‖≤c:=(filed R.makes live birth w y I).2.2.2
  have cap:∀U,‖reading R jl live w y I U‖≤c:=
    actualTransport_norm_le R.family R.makes live old jl
  have mean:‖∫U,reading R jl live w y I U ∂μ‖≤c:=by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=μ) (ae_of_all _ cap)
  have weight:∀U,‖centered R jl live w y I U‖≤2*c:=by
    intro U
    exact (norm_sub_le _ _).trans ((add_le_add (cap U) mean).trans_eq (by ring))
  change ‖∫U,F U*centered R jl live w y I U ∂μ‖≤(2*c)*∫U,‖F U‖ ∂μ
  calc
    _≤∫U,‖F U*centered R jl live w y I U‖ ∂μ:=norm_integral_le_integral_norm _
    _≤∫U,(2*c)*‖F U‖ ∂μ:=by
      refine integral_mono_of_nonneg (ae_of_all _ (fun _=>norm_nonneg _)) (hF.const_mul (2*c)) ?_
      exact ae_of_all _ (fun U=>by
        change ‖F U*centered R jl live w y I U‖≤(2*c)*‖F U‖
        rw [norm_mul,mul_comm (2*c)]
        exact mul_le_mul_of_nonneg_left (weight U) (norm_nonneg _))
    _=_:=integral_const_mul _ _

end YM.Integration.WilsonInvariantActionTransportedOld
