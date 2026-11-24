import YM.Integration.WilsonPositionScaleLawGuardReceipt

/-! The numerical invoice reduces to exactly the measured field discrepancy,
the measured clock discrepancy and one order of independently purchased tail. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardCombine
open PowerSeries WilsonPositionScaleLawGuardSheet WilsonPositionScaleLawGuardLipschitz WilsonPositionScaleLawGuardReceipt
open scoped Polynomial Classical
variable {R:Type*}[NormedRing R][NormedAlgebra ℂ R]

def signal (p:Book R)(q:ℕ)(z z':ℂ)(U:R):ℝ:=
  ‖U-atValue q p.position z‖+‖z'-(trunc (q+1) p.scalar).eval z‖+‖z‖^(q+1)

structure Cover (p:Book R)(D:R)(q:ℕ)(z z':ℂ)(h h':R)(L:ℝ):Prop where
  positive:0≤L
  engine:‖D‖≤L
  position:‖atValue q p.position z‖≤L
  homogeneous:‖atValue q p.homogeneous z‖≤L
  slope:slope q p.correction≤L
  fringe:total p q≤L
  upper:‖h'‖≤L
  near:‖atValue q p.correction z-h‖≤L*‖z‖^(q+1)
  far:‖h'-atValue q p.correction z'‖≤L*‖z‖^(q+1)

private theorem triple {a b c A B C:ℝ}(ha:a≤A)(hb:b≤B)(hc:c≤C)
    (b0:0≤b)(c0:0≤c)(A0:0≤A)(B0:0≤B):a*b*c≤A*B*C:=
  mul_le_mul (mul_le_mul ha hb b0 A0) hc c0 (mul_nonneg A0 B0)

theorem original (p:Book R)(D:R)(q:ℕ)(z z':ℂ)(U h h':R){L:ℝ}(v:Cover p D q z z' h h' L):
    fee p D q z z' U h h'≤(2*L^2+3*L^3)*signal p q z z' U:=by
  let f:=‖U-atValue q p.position z‖
  let c:=‖z'-(trunc (q+1) p.scalar).eval z‖
  let w:=‖z‖^(q+1)
  let E:=signal p q z z' U
  have f0:0≤f:=norm_nonneg _
  have c0:0≤c:=norm_nonneg _
  have w0:0≤w:=pow_nonneg (norm_nonneg _) _
  have sum:E=f+c+w:=rfl
  have E0:0≤E:=sum.symm ▸ add_nonneg (add_nonneg f0 c0) w0
  have fE:f≤E:=by linarith
  have cE:c≤E:=by linarith
  have wE:w≤E:=by linarith
  have s0:0≤ slope q p.correction:=Finset.sum_nonneg fun i _=>mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have t0:0≤total p q:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have wf:=mul_le_mul_of_nonneg_left wE v.positive
  have cf:=mul_le_mul v.slope cE c0 v.positive
  have t:=mul_le_mul wE v.fringe t0 E0
  calc
    _≤L*E*L+L*L*(L*E)+L*L*(L*E)+L*(E*L)+(L*E)*L*L:=
      add_le_add (add_le_add (add_le_add (add_le_add
        (triple v.engine fE v.upper f0 (norm_nonneg _) v.positive E0)
        (triple v.engine v.position (v.far.trans wf) (norm_nonneg _) (norm_nonneg _) v.positive v.positive))
        (triple v.engine v.position cf (norm_nonneg _) (mul_nonneg s0 c0) v.positive v.positive))
        (mul_le_mul v.engine t (mul_nonneg w0 t0) v.positive))
        (triple (v.near.trans wf) v.engine v.homogeneous (norm_nonneg _) (norm_nonneg _) (mul_nonneg v.positive E0) v.positive)
    _=_:=by ring

end YM.Integration.WilsonPositionScaleLawGuardCombine
