import YM.Integration.WilsonPhysicalCentralAddress
import YM.WilsonCoeffUV.Root.Post.Chain

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalCentralProgram
open Function Labels Lattice Source WilsonCoeffUV WilsonCoeffUV.Cosmos
open WilsonPhysicalCentralInversion WilsonPhysicalCentralAddress
open scoped BigOperators Classical
variable {G:Gauge}{h D:ℕ}

theorem signs (F:Frame G h):
    paintC F inversion=Matrix.diagonal (fun i=>(PowerSeries.C ((-1:ℝ)^(weight F i)):PowerSeries ℝ)) :=by
  ext i j : 1
  change PowerSeries.C (blueIn F inversion i j)=_
  rw [whole]
  by_cases e:i=j
  · subst j
    simp
  · simp [e,Matrix.diagonal]

theorem coefficients (F:Frame G h) (V:PatchPanel F D) (X:Thesis F D)
    (p:Chain F V X) (H:Hol G) (q:h<D) (i j:Alma F)
    (odd:Odd (weight F i)) (even:Even (weight F j)):
    prismata F X i j=0:=by
  have co:=congrArg (fun M:Coil F=>M i j) (p.commutes V X H q inversion)
  rw [signs] at co
  rw [Matrix.diagonal_mul,Matrix.mul_diagonal,odd.neg_one_pow,even.neg_one_pow] at co
  have twisted:-(prismata F X i j)=prismata F X i j:=by simpa using co
  ext n
  have en:=congrArg (PowerSeries.coeff n) twisted
  simp only [map_neg] at en
  simp only [map_zero]
  linarith

theorem five (F:Frame G h) (V:PatchPanel F D) (X:Thesis F D)
    (p:Chain F V X) (H:Hol G) (q:h<D) (i j:Alma F)
    (at_five:weight F i=5) (even:Even (weight F j)) (n:ℕ):
    PowerSeries.coeff n (prismata F X i j)=0:=by
  rw [coefficients F V X p H q i j (by rw [at_five]; decide) even,map_zero]

end YM.Integration.WilsonPhysicalCentralProgram
