import YM.Integration.WilsonMatrixOriginalDeckPrescriptionPairing

/-! The complete independent mixed Gram is measured on the original signed two-field mesh and both true Wilson marginals. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescriptionGram
open PhysicalNext.Repeat.Legato Finset MeasureTheory Spec Table Lattice Wilson RG MS MS.Menus MS.Local.Physical
open Extraction Extraction.Order Next.UVStress Push.GridApprox OPE OPE.Therm Ward PhysMS RG17
open WilsonMatrixOriginalDeckRawMoment WilsonMatrixOriginalDeckRawAssay WilsonMatrixOriginalDeckPrescriptionFields
open WilsonMatrixOriginalDeckPrescriptionPairing WilsonMatrixOriginalDeckPrescriptionSeries
open scoped Classical BigOperators Matrix
variable {G:Gauge}{B:Deck G} (R:Run G) (Q:MS.Land.Prescription B) (h:ℕ)
local notation "I"=>Glyph B h

theorem measured (T:Test 2)(z:ℕ×ℕ)(a:Roster B h)(μ ν:ℝ)(k:ℕ):
    matrix R Q h T z a (WilsonMatrixOriginalDeckPrescriptionPairing.basis (B:=B) h ν k)=∑j:Fin (k+1),matrix R Q h T z a (WilsonMatrixOriginalDeckPrescriptionPairing.basis (B:=B) h μ (k-j.val))*trial Q h μ ν j.val:=by
  let ρ:=scene R.family.path z.1 z.2 z.1
  letI:IsProbabilityMeasure ρ:=probability R.makes.wilson le_rfl
  ext i l
  let X:=WilsonMatrixOriginalDeckRawPanel.registered R Q h z.1 z.2 (a.weights i) (a.clock i) (a.order i)
  let Y:=fun (j:Fin (k+1)×I) (o:Site (R.family.side z.1 z.2)) (U:Config G (R.family.side z.1 z.2))=>field R Q h μ (k-j.1.val) z.1 z.2 o U j.2
  let c:=fun j:Fin (k+1)×I=>trial Q h μ ν j.1.val j.2 l
  have cont(j:Fin (k+1)×I)(o:Site (R.family.side z.1 z.2)):Continuous (Y j o):=by
    have pay:=continuousRaw R h Q z.1 z.2 ((WilsonMatrixOriginalDeckPrescriptionPairing.basis (B:=B) h μ (k-j.1.val)).weights j.2) μ (k-j.1.val) o
    rw [point] at pay;exact pay
  have realized:(fun o U=>field R Q h ν k z.1 z.2 o U l)=(fun o U=>∑j,Y j o U*c j):=by
    funext o U
    have paid:=congrFun (WilsonMatrixOriginalDeckPrescriptionReturn.measured R Q h μ ν k z.1 z.2 o U) l
    simpa only [Finset.sum_apply,Matrix.vecMul_apply_eq_sum,Fintype.sum_prod_type,Y,c] using paid
  rw [WilsonMatrixOriginalDeckPrescriptionPairing.original,realized]
  change joint R T z.1 z.2 ρ X _=_
  rw [linear R T z.1 z.2 ρ X Y c (continuousRaw R h Q z.1 z.2 _ _ _) cont,Fintype.sum_prod_type]
  simp only [Matrix.sum_apply,Matrix.mul_apply]
  apply sum_congr rfl;intro j _;apply sum_congr rfl;intro b _
  rw [WilsonMatrixOriginalDeckPrescriptionPairing.original]

/-- At order zero the authentic prescribed mixed matrix is precisely its near-clock self matrix times the independent transfer. -/
theorem born (T:Test 2)(z:ℕ×ℕ)(a:Roster B h)(μ ν:ℝ):
    matrix R Q h T z a (WilsonMatrixOriginalDeckPrescriptionPairing.basis (B:=B) h ν 0)=matrix R Q h T z a (WilsonMatrixOriginalDeckPrescriptionPairing.basis (B:=B) h μ 0)*trial Q h μ ν 0:=by
  simpa using measured R Q h T z a μ ν 0

end YM.Integration.WilsonMatrixOriginalDeckPrescriptionGram
