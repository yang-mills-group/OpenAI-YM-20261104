import YM.Integration.FVA1Physical.Round2.CP5StencilPassport
import YM.QuadraticLocal.Germ.Annual
import YM.Extra.MULTISOURCE_TRAJECTORIES.Initial

/-! Identify all physical marker coefficients, including the unmarked
coefficient, on the original group field. Tests may be independently
chosen in arbitrary real vector spaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.CP5
open Finset Lattice YM.Wilson Marker QuadraticLocal.Affinity Next.Foundations
open YM.Integration.FVA1Physical.Round2.Curvature
open scoped BigOperators Classical
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] {d:ℕ} {n:Side}
variable {E:I→Type} [∀ i,AddCommGroup (E i)] [∀ i,Module ℝ (E i)]

def fieldLog (R:Census I) (a:I → CoverLabel G d) (o:I→Site n) (test:∀ i,E i→ₗ[ℝ]ℂ)
    (A:∀ i,Set (E i)) (y:Wallet A) (V:Config G n) : Poly R :=
  ∑ i,Poly.send (R.fire i)
    (test i (y i).val*(localSection G (a i).1.val).places (Pi.single (a i).2 1) (o i) V)

theorem field_products (R:Census I) (a:I → CoverLabel G d) (o:I→Site n) (test:∀ i,E i→ₗ[ℝ]ℂ)
    (A:∀ i,Set (E i)) (y:Wallet A) (V:Config G n) (s:R.Mode) (vac:ℂ) :
    (vac • Poly.pass (fieldLog R a o test A y V)).part s =
      vac * (∏ i∈s.val,test i (y i).val) *
        ∏ i∈s.val,(localSection G (a i).1.val).places (Pi.single (a i).2 1) (o i) V := by
  rw [Poly.part_smul,fieldLog,Extra.Trajectories.pass_fire,Finset.prod_mul_distrib,mul_assoc]

theorem field_product_support (R:Census I) (a:I → CoverLabel G d) (o:I→Site n)
    (test:∀ i,E i→ₗ[ℝ]ℂ) (A:∀ i,Set (E i)) (y:Wallet A) (s:R.Mode) :
    LocalOn (↑(s.val.biUnion ((stencilPassport a o).support)))
      (fun V=>(Poly.pass (fieldLog R a o test A y V)).part s) := by
  intro U V agree
  change (Poly.pass (fieldLog R a o test A y U)).part s = (Poly.pass (fieldLog R a o test A y V)).part s
  simp only [fieldLog,Extra.Trajectories.pass_fire]
  apply prod_congr rfl
  intro i hi
  apply congrArg ((test i (y i).val)*·)
  apply stencil_field_local a o i U V
  apply agrees_mono agree
  exact coe_subset.mpr (subset_biUnion_of_mem _ hi)

end YM.Integration.FVA1Physical.Round2.CP5
