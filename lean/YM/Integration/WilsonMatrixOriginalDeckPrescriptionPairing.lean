import YM.Integration.WilsonMatrixOriginalDeckPrescriptionReturn
import YM.Integration.WilsonMatrixOriginalDeckRawAssay

/-! Linear two-field integration through the two-clock transfer on the same signed test and whole original Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescriptionPairing
open PhysicalNext.Repeat.Legato Finset MeasureTheory Spec Table Lattice Wilson RG MS MS.Menus MS.Local.Physical
open Extraction Extraction.Order Next.UVStress Push.GridApprox OPE OPE.Therm Ward PhysMS RG17
open WilsonMatrixOriginalDeckRawMoment WilsonMatrixOriginalDeckRawAssay WilsonMatrixOriginalDeckPrescriptionFields
open scoped Classical BigOperators Matrix
variable {G:Gauge}{B:Deck G} (R:Run G) (Q:MS.Land.Prescription B) (h:ℕ)
local notation "I"=>Glyph B h

def basis (μ:ℝ)(k:ℕ):Roster B h where
  weights i j:=if j=i then 1 else 0
  clock _:=μ
  order _:=k

theorem point (μ:ℝ)(k N p:ℕ)(i:I):
    WilsonMatrixOriginalDeckRawPanel.registered R Q h N p ((basis h μ k).weights i) μ k=
      fun o U=>field R Q h μ k N p o U i:=by
  funext o U;simp [basis,WilsonMatrixOriginalDeckRawPanel.registered,field,ite_mul]

/-- A separate finite signed scalar is attached to each original field under the same joint law. -/
theorem linear {J:Type*}[Fintype J] (T:Test 2)(N p:ℕ)(ν:Measure (Config G (R.family.side N p)))[IsFiniteMeasure ν]
    (X:SiteField R N p)(Y:J→SiteField R N p)(coeff:J→ℂ)(hX:∀o,Continuous (X o))(hY:∀j o,Continuous (Y j o)):
    joint R T N p ν X (fun o U=>∑j,Y j o U*coeff j)=∑j,joint R T N p ν X (Y j)*coeff j:=by
  unfold joint
  calc
    _ = ∑x:Var R.family.S 2 N p,∑j,(WilsonExternalMeshMass.charge R.family T x*(∫U,X (x 0) U*Y j (x 1) U ∂ν))*coeff j:=by
      apply sum_congr rfl;intro x _
      have integrable(j:J):Integrable (fun U=>X (x 0) U*Y j (x 1) U) ν:=
        ((hX _).mul (hY j _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      simp_rw [Finset.mul_sum,←mul_assoc]
      rw [integral_finsetSum _ (fun j _=>(integrable j).mul_const (coeff j)),Finset.mul_sum]
      apply sum_congr rfl;intro j _;rw [integral_mul_const];ring
    _ = _:=by rw [Finset.sum_comm];simp only [Finset.sum_mul]

theorem original (T:Test 2)(z:ℕ×ℕ)(a:Roster B h)(μ:ℝ)(k:ℕ)(i j:I):
    matrix R Q h T z a (basis h μ k) i j=joint R T z.1 z.2 (scene R.family.path z.1 z.2 z.1)
      (WilsonMatrixOriginalDeckRawPanel.registered R Q h z.1 z.2 (a.weights i) (a.clock i) (a.order i))
      (fun o U=>field R Q h μ k z.1 z.2 o U j):=by
  rw [←point R Q h μ k z.1 z.2 j];exact (WilsonMatrixOriginalDeckRawMoment.raw R h Q T z.1 z.2 _ (a.weights i) ((basis h μ k).weights j) _ μ _ k).symm

end YM.Integration.WilsonMatrixOriginalDeckPrescriptionPairing
