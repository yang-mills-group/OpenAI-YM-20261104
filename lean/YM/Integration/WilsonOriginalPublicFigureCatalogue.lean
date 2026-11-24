import YM.Integration.WilsonOriginalPublicFigurePole
import YM.Integration.WilsonOriginalPublicFigureHearing

/-! The measured opening is entered in the actual independently registered basis.
Its difference from a prescribed input is one signed input on that same finite program. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicFigureCatalogue
open Finset Lattice Wilson RG XSpace RegulatorIR.FVAAlt2 PertExtension PertExtension.Orb
open PhysicalNext.Repeat.Legato Precision Labels PowerSeries
open WilsonPositionProgramInversionMaterial (Axes axis degree ceiling reported)
open WilsonThermometerPositionTunedSlope (Columns paid)
open WilsonPositionProgramTrialThermalGrades (frozen)
open scoped Classical ENNReal BigOperators PowerSeries
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](d:I → ℕ)
local notation "E" i:max => R.family.labels.level (d i)
def plain (b:Columns R d):Axes R d:=fun i=>WilsonPositionProgramSubmittedCoordinates.plain (E i) (b i)
def filed (v:(i:I) → (E i).Coeff)(a:Axes R d):PowerSeries ℂ:=
  ∑b:Columns R d, if plain R d b=a then PowerSeries.C (∏i:I,v i (b i)) else 0

omit [Fintype I] [LinearOrder I] in
theorem located (b:Columns R d):axis R d (plain R d b)=b:=rfl

theorem invoice (v:(i:I) → (E i).Coeff)(f:Axes R d → PowerSeries ℂ):
    ∑a,filed R d v a*f a=∑b:Columns R d,PowerSeries.C (∏i:I,v i (b i))*f (plain R d b):=by
  simp only [filed,sum_mul,ite_mul,zero_mul]
  rw [sum_comm]
  simp

variable (v:(i:I) → (R.family.labels.level (d i)).Coeff)(P:Period)(z:I → Cover)(T:P.Tree)(D:ChartRatio G)(law:LocalRatio D)
include law in
theorem ordinary (b:Columns R d):
    reported R P d z D (plain R d b)=WilsonThermometerPositionTunedSlope.finite R d P z T b:=by
  ext k
  simp only [reported,WilsonThermometerPositionTunedSlope.finite,coeff_mk,degree,located]
  exact (WilsonPositionProgramCopyTop.original R P d z b D law T k).symm

include law in
theorem ledger:
    ∑a,filed R d v a*reported R P d z D a=
      paid R d (frozen R d v) (WilsonThermometerPositionTunedSlope.finite R d P z T):=by
  rw [invoice,paid]
  apply sum_congr rfl
  intro b _
  rw [ordinary R d P z T D law]
  have head:WilsonThermometerPositionTunedSlope.price R d (frozen R d v) b=
      PowerSeries.C (∏i:I,v i (b i)):=(map_prod PowerSeries.C _ univ).symm
  rw [head]

include law in
theorem read:
    Bare.normalized T G (WilsonPositionProgramInversionMaterial.finite R P d z T (filed R d v))=
      X^ceiling R d * paid R d (frozen R d v) (WilsonThermometerPositionTunedSlope.finite R d P z T):=by
  rw [WilsonPositionProgramInversionMaterial.original R P d z T D law,ledger R d v P z T D law]

include law in
theorem original (ζ:Axes R d → PowerSeries ℂ)(q:ℕ):
    coeff (q+WilsonOriginalPublicFigurePole.roof R d) (Bare.normalized T G
        (WilsonOriginalPublicFigurePole.material R d v z P T))-
      coeff (q+ceiling R d) (Bare.normalized T G
        (WilsonPositionProgramInversionMaterial.finite R P d z T ζ))=
      coeff (q+ceiling R d) (Bare.normalized T G
        (WilsonPositionProgramInversionMaterial.finite R P d z T (fun a=>filed R d v a-ζ a))):=by
  rw [WilsonOriginalPublicFigurePole.filed,PowerSeries.coeff_X_pow_mul,
    WilsonPositionProgramInversionMaterial.original R P d z T D law ζ,PowerSeries.coeff_X_pow_mul,
    WilsonPositionProgramInversionMaterial.original R P d z T D law _,PowerSeries.coeff_X_pow_mul]
  rw [←ledger R d v P z T D law]
  simp only [sub_mul,sum_sub_distrib,map_sub]

end YM.Integration.WilsonOriginalPublicFigureCatalogue
end
