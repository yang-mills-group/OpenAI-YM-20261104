import YM.WilsonCoeffUV.Series.Components.RealSlot
import YM.WilsonCoeffUV.Series.Covariance

/-! Operator transport for canonical padding and restricting. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Matrix Function PowerSeries
open scoped BigOperators
variable {U V X' R: Type*} [Fintype U] [Fintype V] [Fintype X']
-- quadratic in projected space
def orbC (K:Matrix U U ℝ) : Ink U := C (paint 2 (orbQ K))
lemma body_orb [DecidableEq U][DecidableEq V] (K:Matrix U U ℝ): loom (leftFlag U V) (orbC K)=bodyQ V K := by
  have h (i:U) : loom (leftFlag U V) (path i)=path (.inl i) := by rw [loom_pin,Finset.sum_eq_single (Sum.inl i)]<;> simp +contextual [leftFlag]
  have he (r:ℝ)(p:POL U) : C (r•p)=r • C p := by rw [Algebra.smul_def,map_mul,Algebra.smul_def,real_alg, MvPolynomial.algebraMap_eq]; rfl
  rw [orbC,orb_paint]; simp only [he,map_sum,map_mul,loom_smul,bodyQ,slopeQ,(fun x:U=>show C (MvPolynomial.X x)=path x from rfl),h,Finset.mul_sum,mul_smul_comm]
lemma body_orb_C [DecidableEq U][DecidableEq V] (K:Matrix U U ℝ): bodyQ V K=C (cord (leftFlag U V) (paint 2 (orbQ K))) := by
  rw [← body_orb,orbC,loom,map_C]; rfl

omit [Fintype U] [Fintype V] in
lemma coeff_proj {P: Ink (U⊕V)} (h:constantCoeff P=0): constantCoeff (projectZero P)=0 := by rw [← coeff_zero_eq_constantCoeff_apply,projectZero,coeff_map,coeff_zero_eq_constantCoeff_apply,h,map_zero]
lemma wick_log {P:ℕ→Gen ℝ (U⊕V)}(h:shellK 2 P)(z:P 0=0)(p:∀ i,Pure (P i))(G:Matrix U U ℝ) : logOf (Wick V G (raiseE (flash P)))=projectZero (stopF 1 (ramp (abr (fillSlots V G) P) 2)) := by
  have he : constantCoeff (stopF 1 (ramp (abr (fillSlots V G) P) 2))=0 := by rw [←coeff_zero_eq_constantCoeff_apply,stopF, coeff_map,coeff_zero_eq_constantCoeff_apply,rolls_clean _ z,map_zero]
  rw [Wick,as_normal_exp (fillSlots V G) h z p, raise_map _ (by simp [projectZero]) he]
  apply raise_inj (constantCoeff_logOf (raise_one (coeff_proj he))) (coeff_proj he); exact raising_log (raise_one (coeff_proj he))
lemma wick_product {P:ℕ→Gen ℝ (U⊕V)}(h:shellK 2 P)(z:P 0=0)(p:∀ i,Pure (P i)){l}{Q:ℕ→Gen ℝ (U⊕V)}(v:shellK l Q)(w:∀ i,Pure (Q i))(G:Matrix U U ℝ) :
    Wick V G (raiseE (flash P)*flash Q) = Wick V G (raiseE (flash P))*projectZero (stopF 1 (ramp (bul (fillSlots V G) (abr (fillSlots V G) P) Q) l)) := by rw [Wick,as_column _ h z p v w,map_mul]

variable [DecidableEq U][DecidableEq V][DecidableEq X']
def bridgeM (K:Matrix U V ℝ) (X':Type*) [DecidableEq X'] := Matrix.fromBlocks K 0 0 (1:Matrix X' X' ℝ)
omit [Fintype U] [DecidableEq U] [DecidableEq V] in
lemma bridge_rail (K:Matrix U V ℝ) : loom (bridgeM K X')= railCov K (path (U:=X')) := by
  have hp i : loom (bridgeM K X') (path i)=railCov K (path (U:=X')) (path i) := by
    cases i with
    | inl i=> rw [loom_pin,rail_pin, Fintype.sum_sum_type]; simp [bridgeM, noiseLine]
    | inr i=> rw [loom_pin,rail_aux,Fintype.sum_sum_type,up_var]; simp only [bridgeM,fromBlocks_apply₂₁,fromBlocks_apply₂₂,Matrix.zero_apply, zero_smul, Finset.sum_const_zero,zero_add]; rw [Finset.sum_eq_single i]; · simp
              · intro a _ ha; rw [Matrix.one_apply_ne ha.symm,zero_smul]
              simp
  rw [rail (f:=loom (bridgeM K X')) (by simp [loom]) (fun i=>loom_real _ i),rail (f:=railCov K (path (U:=X'))) (by simp [railCov]) (fun i=>rail_zero ..)]
  simp_rw [hp]
lemma flag_cast (X:Type*) [Fintype X][DecidableEq X] (K:Matrix U V ℝ):
    leftFlag U X * bridgeM K X= K * leftFlag V X ∧ rightFlag U X * bridgeM K X=rightFlag V X := by
  have he (p:Lawn (V⊕X)): leftArm ((bridgeM K X)*ᵥ p)=K*ᵥ leftArm p ∧ rightArm ((bridgeM K X)*ᵥ p)=rightArm p := by
    constructor
    · funext i; simp only [leftArm,bridgeM,mulVec,dotProduct]; rw [Fintype.sum_sum_type]; simp
    funext i; simp only [rightArm,bridgeM,mulVec,dotProduct]; rw [Fintype.sum_sum_type]; simp only [fromBlocks_apply₂₂, fromBlocks_apply₂₁, Matrix.zero_apply,zero_mul, Finset.sum_const_zero,zero_add]; exact congr_fun (one_mulVec (rightArm p)) i
  constructor
  · apply Matrix.toLin'.injective; apply LinearMap.ext; intro u
    change _*ᵥ u= _*ᵥ u
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,left_hit,left_hit]; exact (he u).1
  apply Matrix.toLin'.injective; apply LinearMap.ext; intro u; change _*ᵥ u=_*ᵥ u
  rw [← Matrix.mulVec_mulVec,right_hit,right_hit]; exact (he u).2
end YM.WilsonCoeffUV.Blue
