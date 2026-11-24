import YM.WilsonCoeffUV.Step.Rotation.Impact
/-!
# Rebase from earthy measure to the skybridge motion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue.Freedom
open Matrix Function PowerSeries
open scoped BigOperators
variable {U V : Type*}[Fintype U][DecidableEq U][Fintype V]
section geom

local notation "VLaw"=> Ink (U⊕V)
structure Bend (P P' E E' J J': Ink (U⊕V)) (B:Ink V) (θ:Lawn (U⊕V)→Lawn U) (K N:Matrix U U ℝ): Prop where
  T₀: θ 0=0
  analytic: Green θ
  det: |(edgeM θ 0).det|=1
  Z0: constantCoeff J=0
  Z1: constantCoeff J'=0
  P0: constantCoeff P=0
  P1: constantCoeff P'=0
  pre: P+E= J+(holdUp U B+bodyQ V K)
  post: P'+E'=J'+(holdUp U B+bodyQ V N)
  traverse: E=reroll path (spool θ) E'
  haar: (motionJ (spool θ)).det * raiseE (reroll path (spool θ) J')=realS ((edgeM θ 0).det)*raiseE J

variable {P P' E E' J J': Ink (U⊕V)}{B: Ink V}{θ:Lawn (U⊕V)→ Lawn U}{K N:Matrix U U ℝ}
variable (W:Bend P P' E E' J J' B θ K N)
local notation "ρ"=> reroll path (spool θ)
local notation "δ"=> edgeM θ 0

include W
lemma Bend.slip : IsUnit (edgeM θ 0).det := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  have he:=W.det; rw [h] at he; simp at he
lemma Bend.tall (h:K.transpose=K)(hz:IsUnit K.det)(h':N.transpose=N) :
    K=(δ).transpose*N*δ ∧ ∀ i, constantCoeff (spool θ i)=constantCoeff (noiseLine δ i):= by
  apply both_leading path θ W.analytic W.T₀ K N h h' hz _ rfl W.slip B B
  have he:= congrArg constantCoeff W.pre
  have hg:= congrArg constantCoeff (congrArg ρ W.post)
  simp only [map_add,reroll_up,train_id,RingHom.id_apply,floor_pres (reroll_X _ _) W.P1, floor_pres (reroll_X _ _) W.Z1, W.P0,W.Z0,zero_add, ← W.traverse] at he hg ⊢
  rw [add_comm,← he, hg,add_comm]
omit W [Fintype V] in
private lemma carry_cov (A T R: Matrix U U ℝ)(h:A=R.transpose*T*R)(hr:IsUnit R.det): T⁻¹=R*A⁻¹*R.transpose:= by
  rw [h, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.mul_assoc,Matrix.mul_nonsing_inv R hr,one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (by simpa using hr),Matrix.mul_one]
lemma Bend.sky (h:K.transpose=K)(hz:IsUnit K.det)(h':N.transpose=N)
   (A A':Ink (U⊕V))(e:A=ρ A') : Wick V K⁻¹ (raiseE P * A)=Wick V N⁻¹ (raiseE P'*A') := by
  obtain ⟨ha,hb⟩:= W.tall h hz h'
  let F:=bodyQ V K-ρ (bodyQ V N)
  let D:=motionJ (spool θ)
  have hg:=W.haar
  have hs:F+ρ P'+J=P+ρ J' := by
    have ht:=congrArg ρ W.post
    simp only [map_add,reroll_up,train_id,RingHom.id_apply,← W.traverse] at ht
    rw [eq_sub_of_add_eq W.pre,eq_sub_of_add_eq ht]; unfold F; abel
  have hx: constantCoeff F=0:=local_zero_roll δ path hb ha
  have hv: raiseE F*raiseE (ρ P')*raiseE J=raiseE P*raiseE (ρ J') := by
    rw [←raise_add hx (floor_pres (reroll_X _ _) W.P1), ←raise_add (by rw [map_add,hx,floor_pres (reroll_X _ _) W.P1,zero_add]) W.Z0,hs, raise_add W.P0 (floor_pres (reroll_X _ _) W.Z1)]
  have hm: D.det*(raiseE F*ρ (raiseE P' * A'))=realS (δ).det*(raiseE P*A) := by
    rw [map_mul, raise_map _ (by rw [reroll_X]; simp) W.P1, ← e, ←mul_assoc (raiseE F), ←mul_assoc D.det, ← mul_assoc (realS _)]
    apply congrArg (· * A)
    apply (raise_unit W.Z0).mul_left_inj.mp
    rw [mul_assoc D.det,hv,show D.det*(raiseE P*raiseE (ρ J'))=(motionJ (spool θ)).det*raiseE (ρ J')*raiseE P by change D.det*_=D.det*_*_; ring, hg]; ring
  have hh : K⁻¹.transpose=K⁻¹ := by rw [transpose_nonsing_inv,h]
  have hh' : N⁻¹.transpose=N⁻¹ := by rw [transpose_nonsing_inv,h']
  apply ((W.slip.map (realS (U:=V))).mul_right_inj).mp
  have hy:= W_covariance hh h (Matrix.mul_nonsing_inv K hz) hh' (raiseE P'*A') δ W.slip ha (carry_cov K N δ ha W.slip) (spool θ) path hb
  rw [hm,train_id,RingHom.id_apply,←real_alg,←Algebra.smul_def,W_smul,Algebra.smul_def,real_alg] at hy; exact hy
end geom
end YM.WilsonCoeffUV.Blue.Freedom
