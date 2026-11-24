import YM.Integration.WilsonReporterWeightedOrdinary
import YM.Integration.WilsonPhysicalThermalWickFaces

/-! The very same group input is multiplied after its fitted thermal inverse.
The Wilson and prescribed tables multiply by the identical ordinary-face
scalar, including the unit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickStretched
open Lattice Wilson RG Function Finset MvPolynomial Source Cells Extraction Marker
open Next.Rank Next.Rank.Atlas Next.Rank.Normal Next.Rank.Station Next.Rank.Perch
open Glyph Exponential 
open WilsonReporterWeightedOrdinary (stretch)
open scoped BigOperators Classical
variable {G:Gauge}{C:Family G}{k l N p n:ℕ}{ch:AtlasData G C.S p}{d:Fin n→ℕ}

theorem booked (a:Fin n→ℝ)(u:(i:Fin n)→C.label (d i))(Z:(i:Fin n)→Heater C k (d i))
    (w:Fin n → YM.Lattice.Cover)(h:l≤k)(m:Chamber G C.S l p→ℂ)(S:modes (Fin n)):
    (Answer ch w h (fun i=>Z i (stretch C a u i)) m).part S=
      (∏i∈S.val,(a i:ℂ))*(Answer ch w h (fun i=>Z i (u i)) m).part S:=by
  rw [Answer_part,Answer_part]
  have words:pot S.val (fun i=>Z i (stretch C a u i))=
      (∏i∈S.val,(a i:ℂ))•pot S.val (fun i=>Z i (u i)):=by
    have heat (i:Fin n):Z i (stretch C a u i)=(a i:ℂ)•Z i (u i):=
      (Z i).map_smul _ _
    unfold pot
    simp_rw [heat,map_smul]
    simp only [Algebra.smul_def,map_prod,Finset.prod_mul_distrib]
  rw [words,map_smul,smul_eq_mul]

theorem charge (a:Fin n→ℝ)(v:(i:Fin n)→C.label (d i))(x:Points n)(S:modes (Fin n)):
    (Read.maxProfile C x (jointX (stretch C a v))).part S=
      (∏i∈S.val,(a i:ℂ))*(Read.maxProfile C x (jointX v)).part S:=by
  rw [WilsonReporterWeightedOrdinary.profile]
  congr 1
  have eq:(∏i,a ((Read.project S i).val))=∏i∈S.val,a i:=by
    rw [←Fintype.prod_equiv (Read.project S).symm (fun t:S.val=>a t.val) (fun i=>a ((Read.project S i).val))
      (fun i=>by simp)]
    exact Finset.prod_attach S.val a
  rw [eq]
  norm_cast

def rates (c:ℝ)(i:Fin 2):ℝ:=if i=1 then c else 1

theorem mask (c:ℝ)(S:Finset (Fin 2)):(∏i∈S,((rates c i:ℝ):ℂ))=if 1∈S then (c:ℂ) else 1:=by
  classical
  have e (i:Fin 2):((rates c i:ℝ):ℂ)=if i=1 then (c:ℂ) else 1:=by
    by_cases h:i=1 <;> simp [rates,h]
  simp only [e]
  exact Finset.prod_ite_eq' S 1 (fun _=>(c:ℂ))

end YM.Integration.WilsonPhysicalThermalWickStretched
end
