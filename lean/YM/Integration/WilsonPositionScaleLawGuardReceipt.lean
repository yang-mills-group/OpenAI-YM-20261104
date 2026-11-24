import YM.Integration.WilsonPositionScaleLawGuardLipschitz
import YM.Integration.WilsonPositionScaleLawGuardSheet

/-! The four changes between the actual home matrices and the finite MS calculation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardReceipt
open PowerSeries WilsonPositionScaleLawGuardSheet WilsonPositionScaleLawGuardLipschitz
open scoped Polynomial Classical
variable {R:Type*}[NormedRing R]

private theorem three (a b c:R):‖a*(b*c)‖≤‖a‖*‖b‖*‖c‖:=by
  rw [mul_assoc]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))

private theorem five (a b c d e:R):‖a+b+c+d+e‖≤‖a‖+‖b‖+‖c‖+‖d‖+‖e‖:=by
  calc
    _≤‖a+b+c+d‖+‖e‖:=norm_add_le _ _
    _≤(‖a+b+c‖+‖d‖)+‖e‖:=add_le_add (norm_add_le _ _) le_rfl
    _≤((‖a+b‖+‖c‖)+‖d‖)+‖e‖:=add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _≤_:=add_le_add (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) le_rfl

variable [NormedAlgebra ℂ R]
def fee (p:Book R)(D:R)(q:ℕ)(z z':ℂ)(U h h':R):ℝ:=
  ‖D‖*‖U-atValue q p.position z‖*‖h'‖+
  ‖D‖*‖atValue q p.position z‖*‖h'-atValue q p.correction z'‖+
  ‖D‖*‖atValue q p.position z‖*(slope q p.correction*‖z'-(trunc (q+1) p.scalar).eval z‖)+
  ‖D‖*(‖z‖^(q+1)*total p q)+
  ‖atValue q p.correction z-h‖*‖D‖*‖atValue q p.homogeneous z‖

theorem original (p:Book R)(D:R)(paid:Quote p D)(q:ℕ)(z z':ℂ)(U h h':R)
    (hz:‖z‖≤1)(hz':‖z'‖≤1)(hw:‖(trunc (q+1) p.scalar).eval z‖≤1):
    ‖D*(U*h')-h*(D*atValue q p.homogeneous z)‖≤fee p D q z z' U h h':=by
  let w:=(trunc (q+1) p.scalar).eval z
  let B:=atValue q p.position z
  let N:=atValue q p.homogeneous z
  let A:=atValue q p.correction
  have eq:D*(U*h')-h*(D*N)=D*((U-B)*h')+D*(B*(h'-A z'))+D*(B*(A z'-A w))+
      (D*(B*A w)-A z*D*N)+(A z-h)*(D*N):=by simp only [mul_sub,sub_mul,mul_assoc];abel
  change ‖D*(U*h')-h*(D*N)‖≤_
  rw [eq]
  apply (five _ _ _ _ _).trans
  have lip:=WilsonPositionScaleLawGuardLipschitz.original q p.correction z' w hz' hw
  have changeFee:‖D*(B*(A z'-A w))‖≤‖D‖*‖B‖*(slope q p.correction*‖z'-w‖):=
    (three _ _ _).trans (mul_le_mul_of_nonneg_left lip (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  exact add_le_add (add_le_add (add_le_add (add_le_add (three _ _ _) (three _ _ _))
    changeFee) (paid q z hz)) (three _ _ _)

end YM.Integration.WilsonPositionScaleLawGuardReceipt
