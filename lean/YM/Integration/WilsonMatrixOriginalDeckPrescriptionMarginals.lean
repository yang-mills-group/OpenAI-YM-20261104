import YM.Integration.WilsonMatrixOriginalDeckPrescriptionGram

/-! The same preperiod independent transfer for each genuine proper marginal and the centered signed measurement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescriptionMarginals
open PhysicalNext.Repeat.Legato Finset MeasureTheory Spec Table Lattice Wilson RG MS MS.Menus MS.Local.Physical
open Extraction Extraction.Order Next.UVStress Push.GridApprox OPE OPE.Therm Ward PhysMS RG17
open WilsonMatrixOriginalDeckRawMoment WilsonMatrixOriginalDeckRawAssay WilsonMatrixOriginalDeckPrescriptionFields
open WilsonMatrixOriginalDeckPrescriptionPairing WilsonMatrixOriginalDeckPrescriptionSeries
open scoped Classical BigOperators Matrix
variable {G:Gauge} (R:Run G)

theorem proper (T:Test 2)(N p:ℕ)(ρ:Measure (Config G (R.family.side N p))) [IsFiniteMeasure ρ]
    {A:Type*} [Fintype A] (X:SiteField R N p)(Y:A→SiteField R N p)(c:A→ℂ)
    (cy:∀j o,Continuous (Y j o)):
    separatedMeans R T N p ρ X (fun o U=>∑j,Y j o U*c j)=∑j,separatedMeans R T N p ρ X (Y j)*c j:=by
  unfold separatedMeans
  calc _=∑x:Var R.family.S 2 N p,∑j,
          (WilsonExternalMeshMass.charge R.family T x*((∫U,X (x 0) U ∂ρ)*(∫U,Y j (x 1) U ∂ρ)))*c j:=by
        apply sum_congr rfl;intro x _
        have integrable(j:A): Integrable (Y j (x 1)) ρ:=
          (cy j (x 1)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        rw [integral_finsetSum _ (fun j _=>(integrable j).mul_const (c j))]
        simp only [integral_mul_const,Finset.mul_sum];apply sum_congr rfl;intro j _;ring
       _ = _:=by rw [Finset.sum_comm];simp only [Finset.sum_mul]

variable {B:Deck G} (Q:MS.Land.Prescription B)(h:ℕ)
local notation "I"=>Glyph B h
local notation "row"=>WilsonMatrixOriginalDeckPrescriptionPairing.basis (B:=B) h

/-- The right side uses one and the same signed covariance, with both marginals taken in the original measure. -/
theorem measured (T:Test 2)(N p:ℕ)(ρ:Measure (Config G (R.family.side N p))) [IsFiniteMeasure ρ]
    (X:SiteField R N p)(cx:∀o,Continuous (X o))(μ ν:ℝ)(k:ℕ)(b:I):
    let high:=fun o U=>field R Q h ν k N p o U b
    let low:=fun (j:Fin (k+1)×I) o U=>field R Q h μ (k-j.1.val) N p o U j.2
    let c:=fun j:Fin (k+1)×I=>trial Q h μ ν j.1.val j.2 b
    separatedMeans R T N p ρ X high=∑j,separatedMeans R T N p ρ X (low j)*c j ∧
    joint R T N p ρ X high-separatedMeans R T N p ρ X high=
      ∑j,(joint R T N p ρ X (low j)-separatedMeans R T N p ρ X (low j))*c j:=by
  intro high low c
  have cy(j:Fin (k+1)×I)(o:Site (R.family.side N p)):Continuous (low j o):=by
    have pay:=continuousRaw R h Q N p ((row μ (k-j.1.val)).weights j.2) μ (k-j.1.val) o
    rw [point] at pay;exact pay
  have realized:high=(fun o U=>∑j,low j o U*c j):=by
    funext o U
    have paid:=congrFun (WilsonMatrixOriginalDeckPrescriptionReturn.measured R Q h μ ν k N p o U) b
    simpa only [Finset.sum_apply,Matrix.vecMul_apply_eq_sum,Fintype.sum_prod_type,high,low,c] using paid
  rw [realized,proper R T N p ρ X low c cy,linear R T N p ρ X low c cx cy]
  exact ⟨rfl,by simp only [sub_mul,Finset.sum_sub_distrib]⟩

end YM.Integration.WilsonMatrixOriginalDeckPrescriptionMarginals
