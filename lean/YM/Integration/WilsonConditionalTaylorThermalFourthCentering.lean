import YM.Integration.WilsonConditionalTaylorThermalSecondProduct
import YM.Integration.WilsonConditionalTaylorThermalCentralDivision

/-! At the next even coupling order the true vacuum denominator contributes
three disconnected subtractions to the one-insertion score. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalFourthCentering
open PowerSeries WilsonConditionalTaylorThermalDivision
open WilsonConditionalTaylorThermalCentralDivision

def centers (F G Q FQ H T U : ℝ) := F*U+G*Q+FQ*H-T-2*F*Q*H

theorem original {O N V S Z : PowerSeries ℝ} {w : ℕ} {m F G Q FQ H T U : ℝ}
    (mpos : m≠0) (v0 : coeff 0 V=m) (one : coeff 1 V=0) (v2 : coeff 2 V=m*H)
    (hO : zeroBefore O w) (orig : O*V=N) (n0 : coeff w N=m*F) (n2 : coeff (w+2) N=m*G)
    (hS : zeroBefore S (w+2)) (s2 : coeff (w+2) S=m*FQ) (s4 : coeff (w+4) S=m*T)
    (hZ : zeroBefore Z 2) (z2 : coeff 2 Z=m*Q) (z3 : coeff 3 Z=0) (z4 : coeff 4 Z=m*U) :
    coeff (w+4) (direction O V S Z) = centers F G Q FQ H T U := by
  let L := direction O V S Z
  have free (B : PowerSeries ℝ) : zeroBefore B 0 := by intro i hi;omega
  have hL : zeroBefore L (w+2) := by
    have cut : zeroBefore (O*Z-S) (w+2) := by
      intro i hi;simp only [map_sub,productLower hO hZ i hi,hS i hi,sub_zero]
    simpa only [L,direction,Nat.add_zero] using productLower cut (free V⁻¹)
  have ld : L*V=O*Z-S := WilsonConditionalTaylorThermalInteractionDivision.normalized (v0.trans_ne mpos)
  have oe := productFirst hO (free V)
  simp only [Nat.add_zero,orig,n0,v0] at oe
  have old : coeff w O=F := mul_right_cancel₀ mpos (oe.symm.trans (mul_comm ..))
  have next := WilsonConditionalTaylorThermalSecondProduct.series hO (free V)
  simp only [Nat.zero_add,orig,n2,v0,old,one,mul_zero,add_zero,v2] at next
  have old2 : coeff (w+2) O=G-F*H := by
    apply mul_right_cancel₀ mpos
    nlinarith only [next]
  have first := productFirst hL (free V)
  have ins := productFirst hO hZ
  simp only [Nat.add_zero,ld,map_sub,ins,s2,z2,v0,old] at first
  have start : coeff (w+2) L=F*Q-FQ := by
    apply mul_right_cancel₀ mpos
    nlinarith only [first]
  have finish := WilsonConditionalTaylorThermalSecondProduct.series hL (free V)
  have varied := WilsonConditionalTaylorThermalSecondProduct.series hO hZ
  simp only [Nat.zero_add,ld,map_sub,varied,s4,old,old2,z2,z3,z4,one,mul_zero,
    add_zero,v0,start,v2] at finish
  change coeff (w+4) L=_
  apply mul_right_cancel₀ mpos
  unfold centers
  nlinarith only [finish]

end YM.Integration.WilsonConditionalTaylorThermalFourthCentering
