import YM.Integration.WilsonCoherentMayerPriorNonbare

/-! The original full density factors at the measured fine coupling before the next clock change. After normalization each proper submoment of the earlier residual enters the connected logarithm on the same field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorMeasured
open Filter Lattice Wilson RG Source Marker Precision
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 WilsonLimitConstruction
open scoped Classical
variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V]{Γ:Census V}
    {R:Run G}{J:Request V}{A:NumericSchedule R.family J}{d:LocalFormal.Datum R.family Γ}
    {F:AnalyticInput J A d}{η:ℝ}{I:FullPreparedInputAt F η}

theorem split {actual model old:Poly Γ} (q:model.part Γ.quiet=0)
    (parts:actual=Poly.pass model*old)(present:actual.part Γ.quiet=1):
    old.part Γ.quiet=1 ∧ massLog actual=model+massLog old:=by
  have p:(Poly.pass model).part Γ.quiet=1:=Poly.pass_part _ q
  have keep:old.part Γ.quiet=1:=by simpa only [parts,Poly.quiet_mul,p,one_mul] using present
  exact ⟨keep,by rw [parts,massLog_product (ne_zero_of_eq_one p) (ne_zero_of_eq_one keep),massLog_pass q]⟩

theorem original (M:FundedRenderedBank.Catalogue J d)(S:FundedRenderedBank.Bank I M)
    (b:TestSpace J.tests)(U:Config G (R.family.side d.level d.period)):
    let ρ:=((R.family.path.rep d.cutoff d.period d.level).eval U)⁻¹
    let input:=ρ • (S.output.output.leaf b).density U
    let old:=ρ • (S.output.residual.leaf b).density U
    let model:=M.model.read b (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)) U
    input.part Γ.quiet=1 → old.part Γ.quiet=1 ∧ massLog input=model+massLog old:=by
  intro ρ input old model present
  have parts:input=Poly.pass model*old:=by
    dsimp only [input,model,old]
    rw [S.output.full,S.same_model,mul_smul_comm]
  exact split (M.model.quiet_read ..) parts present

end YM.Integration.WilsonCoherentMayerPriorMeasured
