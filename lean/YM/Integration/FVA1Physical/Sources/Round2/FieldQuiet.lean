import YM.Integration.FVA1Physical.Round2.FieldSharpSeason
import YM.MSbar.Wave.Touch

/-! Exact scalar vacuum and zero imaginary component for the literal empty
physical Wilson stencil, including the same interacting formal denominator. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Finset Matrix MvPolynomial Lattice RG YM.Wilson Tree Exterior Push.Uniform
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open MSbar MSbar.Cacao MSbar.Heath.Stock MSbar.Mosaic MSbar.Bakery MSbar.Lapaz
open Precision Next.SectorChange MSbar.Whisk MSbar.Heath MSbar.Lis MSbar.Heath.Cottage MSbar.Bakery.Portal MSbar.Bulk
open MSbar.Rolling YM.Integration.FVA1Physical.Wilson
open Precision MSbar.Bakery.Film
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι] [IsEmpty ι] (J:ι→Lamp G)

theorem empty_field_bank (A:Issue G) (o:ι→Site A.f) (part:Bool) :
    jointFieldBank J A o part = if part then 0 else 1 := by
  apply PowerSeries.ext
  intro n
  rw [jointFieldBank,PowerSeries.coeff_mk]
  let U:=activeSlots J A.S A.F o
  have start : lampRow J part U 0 = if part then 0 else 1 := by
    apply MvPolynomial.funext
    intro x
    change MvPolynomial.eval x (lampRow J part U 0)=MvPolynomial.eval x _
    rw [lampRow_eval, PertExtension.Series.Radial.jet_zero]
    cases part <;> simp [lampShape, exhibit, look]
  cases n with
  | zero=> change MvPolynomial.rename _ (lampRow J part U 0)=_; rw [start];cases part <;> simp
  | succ n=>
    haveI:IsEmpty (Fin (n+1)→Wire G (↑U)):=⟨fun f=>isEmptyElim (f 0).1.val.1⟩
    change MvPolynomial.rename _ (lampRow J part U (n+1))=_
    cases part <;> simp [lampRow,PowerSeries.coeff_one]

private theorem tilted_unit {σ:Type} [Fintype σ] [DecidableEq σ] (f:PowerSeries (Pot σ)) (hf:Kind f) :
    tiltedStencil f 1=1 := by
  rw [tiltedStencil,one_mul,mul_comm,PowerSeries.invOfUnit_mul]
  rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,wickSeries,PowerSeries.coeff_mk,covers hf,wickStencil_one]
  rfl

theorem empty_bulk_field (A:Issue G) (χ:ChartRatio G) (z:Positions (Primary A.c G))
    (p:ℕ) (o:ι→Site A.f) (part:Bool) (kind:Kind A.T) (pos:(mold A.pre A.F A.v).PosDef) :
    taste p (bulkColumn A χ z (jointFieldBank J A o part) p) A.fClock = if part then 0 else 1 := by
  rw [empty_field_bank]
  cases part with
  | true=>
    simp [bulkColumn,owes,picture,growP,Scan,taste]
  | false=>
    change taste p (bulkColumn A χ z 1 p) A.fClock=1
    rw [←MSbar.Wave.single A.fClock p]
    apply sum_congr rfl
    intro n hn
    apply congrArg (A.fClock^n * ·)
    rw [bulkColumn, owes, picture, PowerSeries.coeff_map]
    rw [←tiltedStencil_eq_grow _ _ pos.inv _ _ (well A.F A.v χ A.T kind) (p+1) n (mem_range.mp hn),
      tilted_unit _ (well A.F A.v χ A.T kind)]
    by_cases zero:n=0 <;> simp [PowerSeries.coeff_one,zero]

end YM.Integration.FVA1Physical.Round2.Curvature
