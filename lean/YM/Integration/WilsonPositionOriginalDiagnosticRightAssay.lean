import YM.Integration.WilsonPositionOriginalDiagnosticRightSeries
import YM.Integration.WilsonMatrixOriginalDeckPrescriptionRightAssay

/-! Price the full filed transfer on the right of the true two-clock Wilson test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticRightAssay
open Finset Function MeasureTheory Lattice Wilson RG MS MS.Land MS.Menus MS.Local.Physical
open Spec Table Ward PhysMS RG17 Extraction Extraction.Order PhysicalNext.Repeat.Legato Push.GridApprox Next.UVStress OPE OPE.Therm
open WilsonMatrixOriginalDeckRawMoment WilsonMatrixOriginalDeckPrescription
open WilsonMatrixOriginalDeckPrescriptionFields WilsonPositionOriginalDiagnosticRightSeries
open scoped Classical BigOperators Matrix Polynomial Topology
variable {G:Gauge} (R:Run G) {D:Deck G} (Q:MS.Land.Prescription D)
variable {f:Extraction.Order} {S:Table R.family.book} (F:Spec.Final R.family f S) (L:Layout F) (h:ℕ)
local notation "I"=>Glyph D h

def posted (μ:ℝ)(p:ℕ)(g:ℂ)(N per:ℕ)(j:I):SiteField R N per:=fun o U=>
  ∑a:I,raw (B:=D) R h N per o U a*(sources Q h μ p a j).eval g

def right (μ ν r s:ℝ)(p:ℕ)(g:ℂ)(w v:I→R.family.label h)(N per:ℕ)(j:I):SiteField R N per :=fun o U=>
  deposited R F L h s (v j) N per o U -
    ∑b:I,deposited R F L h r (w b) N per o U * (change Q h μ ν p b j).eval g

private theorem sum_posted (μ ν:ℝ)(p:ℕ)(g:ℂ)(N per:ℕ)(o:Site (R.family.side N per))
    (U:Config G (R.family.side N per))(j:I) :
    ∑b:I,posted R Q h μ p g N per b o U * (change Q h μ ν p b j).eval g =
      posted R Q h ν p g N per j o U +
       g^(p+1)*∑a:I,raw (B:=D) R h N per o U a*(tail Q h μ ν p a j).eval g :=by
  let A:=raw (B:=D) R h N per o U
  change ∑b:I,(∑a:I,A a*(sources Q h μ p a b).eval g)*(change Q h μ ν p b j).eval g=_
  simp only [Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum]
  have rows (a:I):∑ b:I,(sources Q h μ p a b).eval g*(change Q h μ ν p b j).eval g =
      (sources Q h ν p a j).eval g+g^(p+1)*(tail Q h μ ν p a j).eval g :=by
    exact (sub_eq_iff_eq_add.mp (WilsonPositionOriginalDiagnosticRightSeries.evaluated Q h μ ν p g a j)).trans (add_comm _ _)
  simp_rw [rows,mul_add,Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [A];ring

/-- The independently filed part of the literal right contrast starts above
the full retained order, with all surviving coefficients on their original fields. -/
theorem source (μ ν r s:ℝ)(p:ℕ)(g:ℂ)(w v:I→R.family.label h)(N per:ℕ)(j:I)
    (o:Site (R.family.side N per))(U:Config G (R.family.side N per)):
    right R Q F L h μ ν r s p g w v N per j o U =
      (deposited R F L h s (v j) N per o U - posted R Q h ν p g N per j o U)
      - (∑ b:I,(deposited R F L h r (w b) N per o U-posted R Q h μ p g N per b o U)*
        (change Q h μ ν p b j).eval g)
      - g^(p+1)*∑a:I,raw (B:=D) R h N per o U a*(tail Q h μ ν p a j).eval g :=by
  simp only [right,sub_mul,Finset.sum_sub_distrib,sum_posted R Q h μ ν p g N per o U j]
  abel

/-- Both cutoff deposit maps and every lower right field share one original
normalized Wilson measure and one test, before taking either regulator. -/
theorem hearing (T:Test 2)(μ ν r s:ℝ)(p:ℕ)(g:ℂ)(w v:I→R.family.label h)(N per:ℕ)(i j:I):
    let ρ:=scene R.family.path N per N
    let X:=deposited R F L h r (w i) N per
    joint R T N per ρ X (right R Q F L h μ ν r s p g w v N per j) =
      joint R T N per ρ X (deposited R F L h s (v j) N per) -
      ∑ b:I,joint R T N per ρ X (deposited R F L h r (w b) N per)*(change Q h μ ν p b j).eval g :=by
  intro ρ X
  letI:IsProbabilityMeasure ρ:=probability R.makes.wilson le_rfl
  let Y:=deposited R F L h s (v j) N per
  let Z:=fun b:I=>deposited R F L h r (w b) N per
  let c:=fun b:I=>(change Q h μ ν p b j).eval g
  have cx(o):Continuous (X o):=R.family.continuousO ..
  have cy(o):Continuous (Y o):=R.family.continuousO ..
  have cz(b o):Continuous (Z b o):=R.family.continuousO ..
  have cs(o):Continuous (fun U=>∑ b:I,Z b o U*c b):=continuous_finsetSum _ fun b _=>(cz b o).mul_const _
  have line:=WilsonMatrixOriginalDeckPrescriptionPairing.linear R T N per ρ X Z c cx cz
  exact (WilsonMatrixOriginalDeckPrescriptionRightCharge.subtract R T N per ρ X Y
    (fun o U=>∑b:I,Z b o U*c b) cx cy cs).1.trans (congrArg (_ - ·) line)

end YM.Integration.WilsonPositionOriginalDiagnosticRightAssay
