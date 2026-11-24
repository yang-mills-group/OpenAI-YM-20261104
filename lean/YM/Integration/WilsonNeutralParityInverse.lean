import YM.Integration.WilsonNeutralParityReset
/-! Real coupling reversal on the complete signed source matrix. Its inverse
uses the same slot parities on the original finite label set. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralParityInverse
open FormalBulk08 Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series
open Jets Work.F03 Work.F05 PowerSeries Bank Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree
open Kemp Pose Glide Palm Wine Rial Roof
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical

def Mode (k:ℕ)(f:Pence):Prop:=∀ e,e%2≠k%2 → coeff e f=0

private def phase (k:ℕ):Pence:= PowerSeries.C ((-1:ℝ)^k)

private theorem phase_add (i j:ℕ):phase (i+j)=phase i*phase j:=by simp [phase,pow_add]
private theorem phase_square (i:ℕ):phase i*phase i=1:=by
  unfold phase;rw [←map_mul,←mul_pow];simp

private theorem reversal (k:ℕ)(f:Pence):Mode k f ↔ Wine.flipN f=phase k*f:=by
  constructor
  · intro mode;ext1 e
    simp only [Wine.flipN,coeff_rescale,phase,coeff_C_mul]
    by_cases even:e%2=0
    · rw [(Nat.even_iff.mpr even).neg_one_pow]
      by_cases other:k%2=0
      · rw [(Nat.even_iff.mpr other).neg_one_pow]
      · rw [mode e (by omega)];ring
    · rw [(Nat.odd_iff.mpr (by omega :e%2=1)).neg_one_pow]
      by_cases other:k%2=0
      · rw [mode e (by omega)];ring
      · rw [(Nat.odd_iff.mpr (by omega:k%2=1)).neg_one_pow]
  · intro equal e wrong
    have both:=congrArg (coeff e) equal
    simp only [Wine.flipN,coeff_rescale,phase,coeff_C_mul] at both
    by_cases even:e%2=0
    · rw [(Nat.even_iff.mpr even).neg_one_pow,
        (Nat.odd_iff.mpr (by omega:k%2=1)).neg_one_pow] at both;linarith
    · rw [(Nat.odd_iff.mpr (by omega:e%2=1)).neg_one_pow,
        (Nat.even_iff.mpr (by omega:k%2=0)).neg_one_pow] at both;linarith

variable {I:Type*}[Fintype I][DecidableEq I]
def Signed (s:I→ℕ)(A:Matrix I I Pence):Prop:=∀ i j,Mode (s i+s j) (A i j)
private def tag (s:I→ℕ):Matrix I I Pence:=Matrix.diagonal fun i=>phase (s i)

private theorem cancel_tag (s:I→ℕ):tag s * tag s=1:=by
  unfold tag;rw [Matrix.diagonal_mul_diagonal]
  simpa only [phase_square] using (Matrix.diagonal_one (n:=I) (α:=Pence))

private theorem conjugates (s:I→ℕ)(A:Matrix I I Pence):
    Signed s A ↔ (PowerSeries.rescale (-1:ℝ)).mapMatrix A=tag s*A*tag s:=by
  constructor
  · intro h;ext1 i j
    have one:= (reversal _ _).mp (h i j)
    simp only [RingHom.mapMatrix_apply,Matrix.map_apply,tag,Matrix.mul_diagonal,Matrix.diagonal_mul]
    change Wine.flipN (A i j)=_
    rw [one,phase_add];ring
  · intro h i j;apply (reversal _ _).mpr
    have one:=congrFun (congrFun h i) j
    simp only [RingHom.mapMatrix_apply,Matrix.map_apply,tag,Matrix.mul_diagonal,Matrix.diagonal_mul] at one
    change Wine.flipN (A i j)=_ at one
    rw [one,phase_add];ring

theorem inverse (s:I→ℕ)(A:Matrix I I Pence)(pay:IsUnit A.det)(ok:Signed s A):
    Signed s A⁻¹:=by
  let D:=tag s
  let φ : Matrix I I Pence →+* Matrix I I Pence := (PowerSeries.rescale (-1:ℝ)).mapMatrix
  have double:D*D=1:=cancel_tag s
  have left:φ A⁻¹*φ A=1:=by rw [←map_mul,Matrix.nonsing_inv_mul A pay,map_one]
  have right:(D*A*D)*(D*A⁻¹*D)=1:=calc
    _ = D*A*(D*D)*A⁻¹*D:=by simp only [mul_assoc]
    _ = D*(A*A⁻¹)*D:=by rw [double,mul_one];simp only [mul_assoc]
    _ = 1:=by rw [Matrix.mul_nonsing_inv A pay,mul_one,double]
  apply (conjugates s _).mpr
  change φ A⁻¹=D*A⁻¹*D
  have eq:φ A=D*A*D:=(conjugates s _).mp ok
  calc
    _ = φ A⁻¹*((D*A*D)*(D*A⁻¹*D)):=by rw [right,mul_one]
    _ = (φ A⁻¹*φ A)*(D*A⁻¹*D):=by rw [eq];simp only [mul_assoc]
    _ = _:=by rw [left,one_mul]

end YM.Integration.WilsonNeutralParityInverse
end
