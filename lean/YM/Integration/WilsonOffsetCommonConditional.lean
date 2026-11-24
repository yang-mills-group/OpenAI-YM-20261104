import YM.Integration.WilsonOffsetPosteriorInterval
import YM.Integration.WilsonLimitConstruction.FundedWilsonTransportMoments

/-! The reporting exterior and the physical observable transport are the
same all-depth conditional. The common bare partition cancels exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetCommonConditional
open Function Set MeasureTheory Lattice Wilson RG Source OPE.Therm Push.GridApprox
open MergeProof.Accent PhysicalNext.Repeat.Legato
open scoped Classical
variable {G:Gauge} {C:Family G} {N p k j:ℕ}

private theorem chain (A:History G) (N p j:ℕ) (f:Config G (A.S.side j p)→ℂ) {k:ℕ} (hk:k≤j):
    gust A N p j f k hk=pushTo A N p hk f:=by
  induction hk using Nat.decreasingInduction with
  | self=>rw [gust_base,pushTo_self]
  | of_succ i hi ih=>rw [gust_step A N p j f hi,Birth.push_first A N p hi,ih]

private theorem multiple (A:History G) (N p j:ℕ) (f:Config G (A.S.side j p)→ℂ)
    (live:Integrable f (prior G _)) (b:ℂ) {k:ℕ} (hk:k≤j):
    pushTo A N p hk (b • f)=b • pushTo A N p hk f:=by
  induction hk using Nat.decreasingInduction with
  | self=>rw [pushTo_self,pushTo_self]
  | of_succ i hi ih=>
    rw [Birth.push_first A N p hi,Birth.push_first A N p hi,ih]
    exact StepData.push_smul _ _ _ _ (pushTo_integrable A N p hi f live)

theorem realized (H:C.Makes) (hj:j≤N) (hk:k≤j) (X:Config G (C.side j p)→ℂ)
    (live:Integrable X (scene C.path N p j)):
    WilsonReportForwardTransfer.exterior (C:=C) (N:=N) hk X=actualTransport C (N:=N) X hk:=by
  let Z:=Wilson.partition G (C.side N p) (C.path.β N p N)
  let J:=fun U=>(C.path.rep N p j).eval U • X U
  have hJ:Integrable J (prior G _):=WilsonLimitConstruction.FundedWilsonTransportMoments.weighted C H hj live
  have start:WilsonReportForwardTransfer.weighted (C:=C) (N:=N) X=(Z:ℂ)⁻¹ • J:=by
    funext U
    simp only [WilsonReportForwardTransfer.weighted,dose,J,Pi.smul_apply,Complex.real_smul,smul_eq_mul,div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv,Z]
    ring
  funext U
  have pos:((C.path.rep N p k).eval U:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive H.wilson (hk.trans hj) U).ne'
  have nz:(Z:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Wilson.partition_pos _).ne'
  unfold WilsonReportForwardTransfer.exterior actualTransport
  rw [start,multiple _ _ _ _ J hJ _ hk,chain C.path N p j J hk]
  change (Z:ℂ)⁻¹*pushTo C.path N p hk J U/(((C.path.rep N p k).eval U/Z:ℝ):ℂ)=
    ((C.path.rep N p k).eval U)⁻¹ • pushTo C.path N p hk J U
  rw [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_div]
  field_simp [nz,pos]

end YM.Integration.WilsonOffsetCommonConditional
