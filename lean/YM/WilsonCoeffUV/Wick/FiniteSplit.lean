import YM.WilsonCoeffUV.Wick.Fourier
import YM.WilsonCoeffUV.Vacuum.Recursion
/-!
# Finite conditional split EXACT on curl covariance => Wick top on horizontal symbols
- harmonic-zero kernel here is a computational lift (which doesn't agree
on nonzero harmonic-ending input jets; the Wick test will periodize
horizontal zero-harmonic inputs). No real path gauge measures. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Carp
open Set Function Filter Lattice RG Laurent Exterior Bloch Metric Next.Free Precision
open Further.FreeCovariance.KP (Episode.covering_roots)
open Matrix FreeResolvent
open Next.Rank.Radian (addr)
open scoped Topology ContDiff BigOperators ComplexConjugate
variable {G:Gauge}{j k m N:ℕ}{n:Side} {s:ℝ} (k':ℝ)(v:Train j)
lemma stellar_tribute (n:Side)(x:Cover)(a b:TypeFace 1): finiteStar k' v x a b n=(stageVolume n)⁻¹*∑ p:Site n,mode (mon p) x*loomM k' v (mon p) a b:=by
  unfold finiteStar tableU; simp only [Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_inv, inv_pow, Complex.ofReal_natCast]; unfold stageVolume; apply congr_arg; apply Finset.sum_congr rfl; intro i _; rw [frost, indicator_of_mem (by exact (PertExtension.LatticePT.Converter.centered_lift n _).mpr (congr_arg lift (wrap_lift i))), mnode]
lemma stellar_wrap (x y : Cover)(p: wrap n x=wrap n y)(a b:TypeFace 1): finiteStar k' v x a b n=finiteStar k' v y a b n:= by rw [stellar_tribute,stellar_tribute]; simp_rw [show ∀i:Site n, mode (mon i) x=mode (mon i) y from fun i=>Bloch.respects i x y p]
private lemma hermP (hk:0<k') (p:Site n) : (loomM k' v (mon p))ᴴ=loomM k' v (mon p):=by
   unfold loomM; split; simp
   have hc : star (scaleD 1 k' v (mon p))=scaleD 1 k' v (mon p):= funext (fun i=> (fieldD_silver _ _ hk _ (real_frequency p) i).fixed)
   unfold fieldD; rw [mask_adj,hc]
private lemma stellar_real (hk:0<k')(x:Cover)(a b:TypeFace 1):conj (finiteStar k' v x a b n)=finiteStar k' v x a b n:=by
  let f p:=mode (mon (n:=n) p) x * loomM k' v (mon p) a b
  have hP i: conj (f i)= f (-i):=by
     obtain ⟨y,hy⟩:= Episode.covering_roots i
     have he:= mode_adjoint (mon i) x; rw [real_frequency,mode_opposite,←mode_inverse,hy,mode_phase,mode_periodic,mul_one] at he
     have hx := (shade_D 1 k' hk v (real_frequency i)).1
     unfold shade at hx
     unfold f; rw [map_mul,show conj (mode (mon i) x)=mode (mon (-i)) x from he]; congr 1
     unfold loomM; by_cases hm:i=0
     · subst i; simp
     have ht: -i≠0:= neg_ne_zero.mpr hm
     rw [if_neg (mt mnode0.mp hm),if_neg (mt mnode0.mp ht)]; rw [hy] at hx
     unfold fieldD at *; rw [fieldD_period] at hx; exact congr_fun (congr_fun hx a) b
  rw [stellar_tribute,map_mul]; change conj (stageVolume n)⁻¹* conj (∑ i,f i)=_
  rw [map_sum]; simp_rw [hP]; rw [show ∑ i:Site n,f (-i)=∑ i:Site n,f i from Equiv.sum_comp (Equiv.neg _) f]; simp [f,stageVolume]

def unitStar (n:Side) : Matrix (Body 1 n) (Body 1 n) ℝ:=of fun x y=> (finiteStar k' v (lift x.1-lift y.1) x.2 y.2 n).re
def ColorStar (G:Gauge)(n:Side): Matrix (Woods G n) (Woods G n) ℝ:= tensor G (unitStar k' v n)
lemma unitS_fiber (hk:0<k')(n:Side): Runs (rotations n (TypeFace 1)) (rotations n (TypeFace 1)) (unitStar k' v n) (solo n (loomM k' v)):= by
   let R:=rotations n (TypeFace 1)
   let F:= solo n (loomM k' v)
   have ht : approached (unitStar k' v n)=(stageVolume n)⁻¹ • (R*F*Rᴴ):=by
      ext ⟨x,a⟩ ⟨y,b⟩
      rw [approached, Matrix.map_apply]; change ((finiteStar k' v _ a b n).re:ℂ)=_
      rw [Complex.conj_eq_iff_re.mp (stellar_real k' v hk _ _ _),stellar_tribute]
      unfold R F solo; rw [Matrix.smul_apply, smul_eq_mul,Matrix.mul_apply,Fintype.sum_prod_type]; simp_rw [rot_fiber]; apply congr_arg; apply Finset.sum_congr rfl; intro p _; rw [show mode (mon p) (lift x-lift y)=cell p x*star (cell p y) from (by rw [sub_eq_add_neg,mode_shift,mode_opposite,Complex.star_def,cell_bar]; rfl)]; simp [rotations,apply_ite star,mul_ite,mul_right_comm]
   change approached (unitStar k' v n)*R=R*F
   rw [ht,Matrix.smul_mul, Matrix.mul_assoc (R*F), (rotations_crew n _).2.2,Matrix.mul_smul,Matrix.mul_one,smul_smul, inv_mul_cancel₀ (stage_ne n),one_smul]
lemma unitS_symmetric (hk:0<k')(n:Side) : (unitStar k' v n).transpose=unitStar k' v n:=by
    have hh:= unitS_fiber k' v hk n; have ht := hh.back (rotations_crew n _) (rotations_crew n _)
    unfold solo at *; rw [div_self (stage_ne n),one_smul,fiber_H] at ht; simp_rw [hermP _ _ hk] at ht; exact ht.lands hh (rotations_crew n _)

lemma colorS_sym (hk:0<k')(n:Side): (ColorStar k' v G n).transpose=ColorStar k' v G n:=by rw [ColorStar,tensor_transpose,unitS_symmetric _ _ hk]
lemma unitS_fold (hk:0<k')(hj:4≤j)(n:Side): let H:=Precision.K ((record (pulse k' v)).acts n); H*unitStar k' v n*H=H:=by
  intro H; have hx := runs_rotor k' hk hj v n
  have ht:= (hx.product (unitS_fiber k' v hk n)).product hx
  unfold solo at *; simp only [fiber_mult] at ht
  have hh (p:Site n): rotor 1 k' v (mon p)*loomM k' v (mon p)*rotor 1 k' v (mon p)=rotor 1 k' v (mon p):=by
      unfold loomM; split
      next he=> rw [he]; simp [rotor,mirage,signal,wedge,tripQ]
      next hp=> rw [rotor_after _ _ hk _ (base_subset_realCube zone_pos (mon_mem n p)) hp, Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,(rotor_immunity ..).2,Matrix.mul_zero,sub_zero]
  simp_rw [hh] at ht; exact ht.lands hx (rotations_crew n _)
lemma colorFold (hk:0<k')(hj:4≤j)(n:Side): let H:= precisionC G n (record (pulse k' v)); H*ColorStar k' v G n*H=H:=by
    intro H; unfold H precisionC ColorStar; rw [←tensor_mul,←tensor_mul]; exact congr_arg _ (unitS_fold k' v hk hj n)

section generic
variable {α β:Type*}[Fintype α][Fintype β]
private theorem countA (K:Matrix α α ℝ)(J:Matrix β β ℝ)(P:Matrix α α ℝ)(R:Matrix β β ℝ)(Q:Matrix β α ℝ)(E: Matrix α β ℝ)(I: Matrix α α ℝ) (k:ℝ)
   (hK: Kᵀ=K)(hJ:Jᵀ=J)(hp:K*P*K=K)(hr:J*R*J=J)(hi:K*I*(K+k • (Qᵀ*Q))=K) (he:K*E=Qᵀ*J)(hx:(K+k • (Qᵀ*Q))*E=k • Qᵀ):
    K*(I+E*R*Eᵀ)*K = K*P*K:=by
   have hv:Eᵀ*K=J*Q := by have hh:= congr_arg Matrix.transpose he; rw [Matrix.transpose_mul,Matrix.transpose_mul,hK,hJ,Matrix.transpose_transpose] at hh; exact hh
   have hu : K*(E*R*Eᵀ)*K=K*E*Q := by
      simp only [← Matrix.mul_assoc]; rw [he]; rw [Matrix.mul_assoc (_*_),hv]; simp only [Matrix.mul_assoc] at *; rw [← Matrix.mul_assoc _ J Q,← Matrix.mul_assoc J (R*J) Q,hr]
   have hh : K*E= K*I*(k • Qᵀ):= by rw [←hx,← Matrix.mul_assoc _ _ E, hi]
   rw [Matrix.mul_add, Matrix.add_mul,hu, hh, hp]; rw [Matrix.mul_add] at hi
   rw [Matrix.mul_assoc (K*I),Matrix.smul_mul]; exact hi
end generic
section tor
variable {f c:Side}(S:StepData c f)(F : Tree.Forest S.ratio)(K Y: FaceRow)(Q:Matrix (Body 1 f) (Body 1 c) ℝ)
lemma midLinks (_hs:(K.acts f).transpose=K.acts f)(hsY:(Y.acts c).transpose=Y.acts c)(hQ:Inputs S Q (K.acts f) (Y.acts c))(e:ℝ)(he:0<e)(hp:Gap (K.acts f) e)(H:Bid.Larger (G:=G) S)
   (P:Matrix (Woods G f) (Woods G f) ℝ)(R:Matrix (Woods G c) (Woods G c) ℝ)(h₁:precisionC G f K * P * precisionC G f K=precisionC G f K)(h₂:precisionC G c Y*R*precisionC G c Y=precisionC G c Y): let D:= precisionC G f K; let E:=extractV G S F Q; D*(covariance G S F K+E*R*Eᵀ)*D=D*P*D:=by
    intro D E; let W:=pressM G S; let I:= covariance G S F K
    have hD:D=tensor G (Exterior.d 1 f).transpose*tensor G (K.acts f)*tensor G (Exterior.d 1 f):= by unfold D precisionC Precision.K; rw [tensor_mul,tensor_mul]
    have hx : D*I*(fullMatrix G S K)=D:=by
        apply Matrix.ext_iff_mulVec.mpr; intro x; rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]; unfold I; rw [block_solve F K H he hp, representative, Matrix.mulVec_add, gradient,Matrix.mulVec_mulVec, show D * tensor G (Exterior.d 0 f)=0 by rw [hD, Matrix.mul_assoc, ← tensor_mul (d 1 f) (d 0 f),Exterior.closed,tensor_zero,Matrix.mul_zero], Matrix.zero_mulVec,add_zero]
    have hy : D*E=Wᵀ*precisionC G c Y:=by unfold D E precisionC extractV W pressM; rw [tensor_transpose,←tensor_mul,←tensor_mul,(stationed F Q _ _ hQ).2]
    rw [full_write] at hx
    apply countA D (precisionC G c Y) P R W E I S.kernel.penalty (kinetic_sym _hs) (kinetic_sym hsY) h₁ h₂ hx hy
    rw [Matrix.add_mul,show D*E=S.kernel.penalty • Wᵀ * _ from (taken G S F K Y Q hQ).1]; rw [Matrix.smul_mul,Matrix.smul_mul, ← smul_add]; apply congr_arg
    change Wᵀ*(1-W*E)+ _ = Wᵀ
    rw [Matrix.mul_assoc Wᵀ W E,← Matrix.mul_add,sub_add_cancel,Matrix.mul_one]
end tor
end YM.WilsonCoeffUV.Bank.Carp
