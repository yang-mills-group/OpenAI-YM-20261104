import YM.WilsonCoeffUV.Step.Ward.Background
/-! Algebraic formal invariance consumer. H/J with equal measure and
shared push-stencil slope. Holds also insertion: one mark carried once. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Matrix Function PowerSeries
open scoped BigOperators

variable {U V Y : Type*}[Fintype U][DecidableEq U][Fintype V][Fintype Y]

/-- insert σR multiplier and Haar exponential on given log coordinates. -/
structure BridgeK (u w:V→Ink Y)(θ:Lawn (U⊕Y)→Lawn U) (K:Matrix U U ℝ) (B:Ink V)(J E P:Ink (U⊕V)) : Prop where
  z0 : θ 0=0
  gr : Green θ
  J0 : constantCoeff J=0
  P0 : constantCoeff P=0
  total : P=J-E+(holdUp U B+bodyQ V K)
  same : fanWest u E=reroll w (spool θ) E
  eqW : (motionJ (spool θ)).det*raiseE (reroll w (spool θ) J) = realS ((edgeM θ 0).det)*raiseE (fanWest u J)
  orient : IsUnit (edgeM θ 0).det

section
variable {u w:V→Ink Y}{θ:Lawn (U⊕Y)→Lawn U} {K:Matrix U U ℝ} {B:Ink V}{J E P:Ink (U⊕V)}
variable (C:BridgeK u w θ K B J E P)
local notation "ι"=> fanWest (X:=U) u
local notation "κ"=> reroll w (spool θ)
local notation "D"=> edgeM θ 0
local notation "M"=> Matrix.det (motionJ (spool θ))
omit [Fintype V] [Fintype Y] in
lemma fan_x (u:V→Ink Y) : fanWest (X:=U) u X=X:= by rw [fan_reroll,reroll_X]
include C
omit [Fintype V] in
private lemma mode : ι P+ι E=ι J+holdUp U (train u B)+bodyQ Y K ∧
      κ P + κ E=κ J+holdUp U (train w B)+ κ (bodyQ V K) := by
  have h:= C.total; rw [h];
  have hx : fanWest (X:=U) u (holdUp U B)=holdUp U (train u B):= by rw [fan_reroll,reroll_up]
  simp_rw [map_add,map_sub,hx,body_tee u K,reroll_up]; constructor<;> abel

lemma BridgeK.leading (h:K.transpose=K)(hk:IsUnit K.det): K=(Matrix.transpose D)*K*D ∧ ∀ i,constantCoeff (spool θ i)=constantCoeff (noiseLine D i) := by
  apply strike_leading w θ C.gr C.z0 K h hk D rfl C.orient (train u B) (train w B)
  have h₁:=congrArg constantCoeff (mode C).1
  have h₂:=congrArg constantCoeff (mode C).2
  simp only [map_add] at *
  rw [floor_pres (fan_x u) C.P0,floor_pres (fan_x u) C.J0,zero_add,zero_add,C.same] at h₁
  rw [floor_pres (reroll_X _ _) C.P0,floor_pres (reroll_X _ _) C.J0, zero_add, zero_add] at h₂
  rw [add_comm, ← h₁, h₂,add_comm]
lemma BridgeK.balance (h:K.transpose=K)(hk:IsUnit K.det): constantCoeff (train w B - train u B)=0 := by
  obtain ⟨he,hp⟩:= BridgeK.leading C h hk
  have hl := local_zero_roll D w hp he
  have hu:= congrArg constantCoeff (mode C).1; have hv:= congrArg constantCoeff (mode C).2
  rw [map_sub] at hl; replace hl := sub_eq_zero.mp hl
  simp only [map_add,floor_pres (fan_x u) C.P0,floor_pres (reroll_X _ _) C.P0,floor_pres (fan_x u) C.J0,floor_pres (reroll_X _ _) C.J0,zero_add, C.same,←hl] at hu hv
  have hr : Equal 1 (holdUp U (train w B)) (holdUp U (train u B)) := by
    intro i hi; rw [show i=0 by omega]; simpa only [coeff_zero_eq_constantCoeff_apply] using! add_right_cancel (hv.symm.trans hu)
  rw [map_sub]; apply sub_eq_zero.mpr; simpa only [project_up,coeff_zero_eq_constantCoeff_apply] using filtered (ξ:=projectZero) (by simp [projectZero]) hr 0 (by simp)

omit C [Fintype Y] in
private lemma exp_move {A b c d e f:Ink Y} (hA:constantCoeff A=0)(hb:constantCoeff b=0)(hc:constantCoeff c=0)(hd:constantCoeff d=0)(he:constantCoeff e=0)(hf:constantCoeff f=0)
    {x y:Ink Y} (h:x*raiseE e=y*raiseE f)(eq:A+b+f=c+d+e): x*(raiseE A*raiseE b)=y*(raiseE c*raiseE d) := by
  have ht : raiseE A*raiseE b*raiseE f=raiseE c*raiseE d*raiseE e := by rw [← raise_add hA hb,←raise_add hc hd,← raise_add (by simp [hA,hb]) hf,←raise_add (by simp [hc,hd]) he,eq]
  -- equation orientation? A+b+f=c+d+e, substitute x*e= y*f
  apply (raise_unit hf).mul_left_inj.mp
  conv_lhs => rw [mul_assoc x,ht]
  calc x*(raiseE c*raiseE d*raiseE e) = (x*raiseE e)*(raiseE c*raiseE d) := by ring
       _ = _ := by rw [h]; ring

omit C [Fintype Y] [Fintype V] in
private lemma kinetic_transport (T:Matrix U U ℝ)(A:Matrix U U ℝ)(h:A=T.transpose*A*T)(ht:IsUnit T.det)(_ha:IsUnit A.det):
    A⁻¹=T*A⁻¹*T.transpose := by
  let I : Matrix U U ℝ:=1
  calc
    _ = T * (T⁻¹ * A⁻¹ * (T.transpose)⁻¹)*T.transpose:= by simp only [← Matrix.mul_assoc]; rw [Matrix.mul_nonsing_inv T ht,one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (by simpa using ht), Matrix.mul_one]
    _ = _:= by congr 2; conv_rhs=> arg 1; rw [h];
               rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]

-- Multiplying source insertion after exp without assuming source not degenerate.
lemma BridgeK.move (h:K.transpose=K)(hk:IsUnit K.det) (A A':Ink (U⊕V))(e:ι A= κ A') :
     train w (Wick V K⁻¹ (raiseE P*A'))=
       raiseE (train w B-train u B) * train u (Wick V K⁻¹ (raiseE P*A)) := by
  obtain ⟨he,hp⟩:= BridgeK.leading C h hk; let F:= bodyQ Y K-κ (bodyQ V K); let s:=train w B-train u B
  have hF : constantCoeff F=0 := local_zero_roll D w hp he
  have hS : constantCoeff s=0:= BridgeK.balance C h hk
  have hu := mode C
  have hy : M*(raiseE F*κ (raiseE P*A'))=realS (Matrix.det D)*( holdUp U (raiseE s) * ι (raiseE P*A)) := by
    have hc : constantCoeff (holdUp U s)=0:= floor_pres hold_X' hS
    have hv : F+κ P+ι J = holdUp U s+ι P+κ J := by
      obtain ⟨ha,hb⟩:= hu; rw [←C.same] at hb
      have hh:= eq_sub_of_add_eq ha; have h':= eq_sub_of_add_eq hb
      rw [hh,h']; simp only [F,s,map_sub]; abel
    rw [map_mul κ,map_mul ι,e, raise_map _ (by rw [reroll_X];simp) C.P0,raise_map _ (by rw [fan_x]; simp) C.P0,raise_map _ (by rw [hold_X'];simp) hS]; simp only [←mul_assoc];
    apply congrArg (· * κ A'); rw [mul_assoc M, mul_assoc (realS (Matrix.det D))];
    exact exp_move hF (floor_pres (reroll_X _ _) C.P0) hc (floor_pres (fan_x _) C.P0) (floor_pres (reroll_X _ _) C.J0) (floor_pres (fan_x _) C.J0) C.eqW hv
  have hh : K⁻¹.transpose=K⁻¹ := by rw [transpose_nonsing_inv,h]
  have hz := W_covariance hh h (Matrix.mul_nonsing_inv K hk) hh (raiseE P*A') D C.orient he
    (kinetic_transport D K he C.orient hk) (spool θ) w hp
  -- hz leading determinant factor
  apply ((C.orient.map (realS (U:=Y))).mul_right_inj).mp
  rw [←hz,hy,←real_alg,←Algebra.smul_def,W_smul,Algebra.smul_def,mul_comm (holdUp U _),W_param,param_int u hh,mul_comm (train u _),real_alg]

lemma BridgeK.read (h:K.transpose=K)(hk:IsUnit K.det)(hv:constantCoeff (Wick V K⁻¹ (raiseE P))=1) :
    train u (B-logOf (Wick V K⁻¹ (raiseE P)))=train w (B-logOf (Wick V K⁻¹ (raiseE P))) := by
  let U':= Wick V K⁻¹ (raiseE P)
  have he : constantCoeff (train w U')=1:= floor_const (train_X _) hv
  have hf : constantCoeff (train u U')=1:= floor_const (train_X _) hv
  have hz := BridgeK.move C h hk 1 1 (by rw [map_one,map_one]); rw [mul_one] at hz
  let s:= train w B-train u B
  have hg: logOf (train w U')=s+logOf (train u U') := by
    have hv':= BridgeK.balance C h hk
    apply raise_inj (constantCoeff_logOf he) (by rw [map_add,show constantCoeff s=0 from hv',constantCoeff_logOf hf,zero_add]);
    rw [raise_add hv' (constantCoeff_logOf hf), raising_log he, raising_log hf]; apply hz
  rw [map_sub,map_sub, floor_Exp (train_X _) hv, floor_Exp (train_X _) hv]; change _=train w B-logOf (train w U')
  rw [hg]; unfold s U'; abel
end
end YM.WilsonCoeffUV.Blue
