import YM.Integration.WilsonPositionProgramTrialGroundWords
import YM.Integration.WilsonPositionProgramTrialAppointment
import YM.Integration.WilsonThermometerPositionInversionCoefficient

/-! The physically filed finite vector and its curvature expansion on the
same finite group configurations at every positive reannouncement. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialGroundCylinder
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato PertExtension
open WilsonThermometerDeclaredSeeds
open scoped Classical BigOperators
variable {G:Gauge}

private theorem split {h:ℕ}(F:Frame G h)(v:F.Coeff)(q:F.Index→ℂ)(one:q 0=1):
    v 0+∑a,(F.core v) a*q a=∑a,v a*q a:=by
  have entries(a:F.Index):v a*q a=(if a=0 then v 0 else 0)+(F.core v) a*q a:=by
    by_cases live:a=0
    · subst a
      simp [one,Frame.core]
    · simp [Frame.core,live]
  simp_rw [entries]
  rw [Finset.sum_add_distrib]
  simp

variable (R:Run G) {I:Type} [Fintype I][LinearOrder I] (d:I→ℕ)
variable (v:∀j,(R.family.labels.level (d j)).Coeff) (z:I → Cover)
local notation "F" i:max => R.family.labels.level (d i)
local notation "at" i:max u:max n:max U:max => ∑a:Choice R d i,WilsonThermometerFrozenCopies.word
  R d 1 1 v (fun (_:I) (_:Unit)=>(1:ℂ)) (entry R d i a) u () (wrap n (z i)) U

omit [Fintype I] [LinearOrder I] in
private theorem leg (i:I){u:ℝ}(live:u≠0){n:Side}(U:Config G n):
    ((u^(d i+1):ℝ):ℂ)⁻¹*(at i u n U)=
      ∑a:(F i).Index,WilsonOriginalPublicTrialFigure.amount R d u v i a*
        (R.family.localSection (d i)).places (Pi.single a 1) (wrap n (z i)) U:=by
  rw [WilsonThermometerProgramBasis.placed R d 1 1 v (fun (_:I) (_:Unit)=>1) i u () _ U live]
  let val(a:(F i).Index):ℂ:=(↑(u^((F i).grades a).2:ℝ)⁻¹:ℂ)*
    (R.family.localSection (d i)).places (Pi.single a 1) (wrap n (z i)) U
  have unit:val 0=1:=by
    dsimp only [val]
    rw [(F i).zero_degree]
    simp only [pow_zero,inv_one,Complex.ofReal_one,one_mul]
    exact congrFun (R.makes.sections (d i)).unit _
  have one(a:(F i).Index):WilsonThermometerProgramBasis.weight R d 1 1 v
      (fun (_:I) (_:Unit)=>1) i u () a*
      (R.family.localSection (d i)).places (Pi.single a 1) (wrap n (z i)) U
      =(F i).core (v i) a*val a:=by
    simp only [WilsonThermometerProgramBasis.weight,val,one_div,inv_one,one_pow,one_mul,
      Complex.ofReal_one,mul_one,inv_pow]
    ring
  simp_rw [one]
  rw [one_mul,split (F i) (v i) val unit]
  simp only [WilsonOriginalPublicTrialFigure.amount,val,mul_assoc]

omit [LinearOrder I] in
theorem original {u:ℝ}(live:u≠0){n:Side}(U:Config G n)(L:ℂ→L[ℝ]ℝ):
    WilsonThermometerInversionFaces.face R d (wrap n ∘ z) 1 1 v
      (fun (_:I) (_:Unit)=>1) () L u U=L (WilsonOriginalPublicTrialFigure.measured R d u v z U):=by
  unfold WilsonThermometerInversionFaces.face WilsonOriginalPublicTrialFigure.measured
  rw [←smul_eq_mul,←L.map_smul,Complex.real_smul,Complex.ofReal_prod,←Finset.prod_mul_distrib]
  apply congrArg L
  refine prod_congr rfl fun i _=>?_
  simpa only [Complex.ofReal_inv,Function.comp_apply] using leg R d v z i live U

end YM.Integration.WilsonPositionProgramTrialGroundCylinder
end
