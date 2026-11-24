import YM.FormalBulk08.Orb.Triplet
import YM.FormalBulk08.Wick.Tips

/-! Combined alphabet (all variables as potential slots). Covariance row zero on EVERY external parameter. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Orb
open Series Wick Matrix
open scoped BigOperators
variable {V I : Type*} [Fintype V] [DecidableEq V]

open MvPolynomial
variable (T : Saddle ℝ V)
def emer (V I : Type*) := sumAlgEquiv ℝ V I
def aqua : (V⊕I)→ (V⊕I)→ℝ := Sum.elim (fun i => Sum.elim (fun j=>T.q i j) (fun _=>0)) (fun _ _=>0)
lemma aqua_symm (i j: V⊕I) : aqua T i j = aqua T j i := by cases i <;> cases j <;> (first|exact T.ok _ _|rfl)
variable [Fintype I]
lemma press_aqua (F : TypeR (V⊕I)) : emer V I (press (aqua T) F)=press (variation T I).q (emer V I F) := by
   simp only [press_eq,emer,pderiv_sumAlgEquiv, Fintype.sum_sum_type]; simp [aqua,halve,variation]
lemma hearth_aqua (F : TypeR (V⊕I)) : emer V I (hearth (aqua T) F)=hearth (variation T I).q (emer V I F) := by
    have h : Polynomial.map (emer V I).toRingEquiv.toRingHom (bake (aqua T) F)=bake (variation T I).q (emer V I F) := by
       ext1 n
       simp only [Polynomial.coeff_map,bake_coeff, RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
       simp_rw [smul_eq_C_mul,map_mul,emer,sumAlgEquiv_C_inl, ounce_map];congr 1
       induction n with
       | zero => simp only [pow_zero,Module.End.one_apply]
       | succ n ih => rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply,← show emer V I=sumAlgEquiv ℝ V I from rfl,press_aqua]; unfold emer; rw [ih]
    simp [hearth_def,← h]

omit [Fintype I] in
def aftEval (V I : Type*) := MvPolynomial.aeval (R:=ℝ) (Sum.elim (0 : V→TypeR I) MvPolynomial.X)
lemma moment_aqua (F : Pap (V⊕I)) :
     beam (variation T I).call (PowerSeries.map (emer V I).toRingEquiv.toRingHom F) = PowerSeries.map (aftEval V I).toRingHom (late (smoke (aqua T) F)) := by
   rw [rack_finish]; ext1 n
   simp_rw [coeff_beam, PowerSeries.coeff_map, Saddle.call, moment_eq]; change MvPolynomial.aeval (R:=TypeR I) (0:V→TypeR I) (hearth (variation T I).q (emer V I _))= aftEval V I _
   rw [coeff_beam,← hearth_aqua]; generalize hearth (aqua (I:=I) T) _=z
   induction z using MvPolynomial.induction_on with
   | C c=>simp [aftEval,emer]
   | add p q hp hq=> simp only [map_add,hp,hq]
   | mul_X p i hi=> simp_rw [map_mul,hi];congr 1; cases i <;> simp [aftEval,emer]
end YM.FormalBulk08.Orb
