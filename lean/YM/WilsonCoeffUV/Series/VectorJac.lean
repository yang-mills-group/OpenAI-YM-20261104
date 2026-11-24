import YM.WilsonCoeffUV.Series.FormalWick
import YM.WilsonCoeffUV.Series.Piola

/-!
# Gaussian formal vector density identity

For substitution of the internal variables; spectators may also be
substituted in arbitrarily, but *independently* of the noise. X-adic,
already divide out the factor exp(-free coarse Q).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Matrix Function PowerSeries
open scoped BigOperators
variable {U Y Z : Type*} [Fintype U][DecidableEq U]

section Q
variable (Y)
def slopeQ (K:Matrix U U ℝ)(i:U) : Ink (U⊕Y) := ∑ j,K i j • path (.inl j)
def bodyQ (K:Matrix U U ℝ) : Ink (U⊕Y) := (1/2 : ℝ) • ∑ i,path (.inl i) * slopeQ Y K i
variable {Y}
lemma real_kill (i:Y)(c:ℝ) : brush i (realS c)=0 := by rw [←real_alg]; simp
lemma slope_derived (K:Matrix U U ℝ)(i j:U): brush (Sum.inl (β:=Y) i) (slopeQ Y K j) = realS (K j i) := by
  classical
  simp_rw [slopeQ,map_sum, Derivation.map_smul]
  rw [Finset.sum_eq_single i];
  · rw [brush_path]; simp [Algebra.smul_def,real_alg]
  · intro k _ hk; rw [brush_path,if_neg (by simpa)]; simp
  simp
lemma body_derived (K:Matrix U U ℝ)(hK:K.transpose=K)(i:U): brush (Sum.inl (β:=Y) i) (bodyQ Y K) = slopeQ Y K i := by
  classical
  rw [bodyQ,Derivation.map_smul,map_sum];
  simp_rw [Derivation.leibniz,slope_derived, brush_path,smul_eq_mul, Finset.sum_add_distrib]
  have he: ∑ j : U, path (Sum.inl (β:=Y) j)* realS (K j i) = slopeQ Y K i := by
    unfold slopeQ; apply Finset.sum_congr rfl; intro b _
    rw [mul_comm,←real_alg, ←Algebra.smul_def,show K b i=K i b from congr_fun (congr_arg (fun M:Matrix U U ℝ=>M i) hK) b]
  rw [he,Finset.sum_eq_single i];
  · simp
    rw [←add_smul]; norm_num
  · intro b _ hb; rw [if_neg (by simpa)]; ring
  simp
lemma body_aux (y:Y)(K:Matrix U U ℝ): brush (.inr y) (bodyQ Y K)=0 := by
  classical
  simp_rw [bodyQ,slopeQ, Derivation.map_smul, map_sum, Derivation.leibniz, map_sum, Derivation.map_smul,
    brush_path]; simp
-- matrix posterior
omit [DecidableEq U] in
lemma form_rotate (W:Y→Ink Z){A K :Matrix U U ℝ}(R:Matrix U U ℝ)(hK:K=R.transpose*A*R) : railCov R W (bodyQ Y A)=bodyQ Z K := by
  classical
  have hP (r:ℝ)(u:Ink (U⊕Y)) : railCov R W (r • u)= r • railCov R W u := train_smul ..
  subst K
  rw [bodyQ,bodyQ,hP]; congr 1
  simp only [slopeQ,hP,map_sum,map_mul,rail_pin, noiseLine,Matrix.mul_apply, Matrix.transpose_apply,Finset.smul_sum,Finset.sum_smul,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,smul_smul]
  -- index ordering
  conv_lhs => enter [2,i,2,j]; rw [Finset.sum_comm]
  conv_lhs => enter [2,i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
  conv_lhs => enter [2,w]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro w _; rw [Finset.sum_comm]; simp only [mul_comm,mul_left_comm]
end Q

section Span
variable [Fintype Z]
lemma IBP {H K : Matrix U U ℝ}(hH:H.transpose=H)(hK:K.transpose=K)(e:K*H=1)(i:U)(F:Ink (U⊕Z)) :
    Wick Z H (brush (.inl i) F-brush (.inl i) (bodyQ Z K)* F)=0 := by
  have he : Wick Z H (brush (.inl i) (bodyQ Z K)*F)=Wick Z H (brush (.inl i) F) := by
    rw [body_derived K hK]; simp_rw [slopeQ, Finset.sum_mul,smul_mul_assoc, mul_comm (path _),W_sum,W_smul,W_var H hH,Finset.smul_sum, smul_smul];
    rw [Finset.sum_comm];
    simp_rw [←Finset.sum_smul,←Matrix.mul_apply,e]
    rw [Finset.sum_eq_single i];
    · simp
    · intro b _ hb; rw [Matrix.one_apply_ne hb.symm,zero_smul]
    simp
  unfold Wick at *; rw [map_sub,map_sub,he,sub_self]
end Span

section Motion
variable (W:Y→ Ink Z)(θ:U→ Ink (U⊕Z))(t:Z)
def reroll := train (U:=U⊕Y) (Sum.elim θ (holdUp _ ∘ W))
def motionJ : Matrix U U (Ink (U⊕Z)) := of fun i j=> brush (.inl j) (θ i)
omit [Fintype U] [DecidableEq U] in
lemma rolled (i:U) : reroll W θ (path (.inl i))=θ i := by rw [reroll, train_path]; rfl
variable {W θ t}
variable [Fintype Y][Fintype Z]
private def stream (θ : U→ Ink (U⊕Z))(t:Z) : U→ Ink (U⊕Z) := (motionJ θ).adjugate *ᵥ fun i=>brush (.inr t) (θ i)
omit [Fintype Z] in
private lemma chainH (θ:U→ Ink (U⊕Z))(t) : ∑ i, brush (.inl i) (stream θ t i) = brush (.inr t) (motionJ θ).det ∨ ¬IsUnit (motionJ θ).det := by
  by_cases h:IsUnit (motionJ θ).det
  · left
    simp_rw [stream,Matrix.mulVec, dotProduct,map_sum,Derivation.leibniz,smul_eq_mul, Finset.sum_add_distrib,Ddet]
    have H : ∑ i : U,∑ j : U,(brush (.inr t) (θ j)) * brush (.inl i) ((motionJ θ).adjugate i j)=0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro j _; rw [← Finset.mul_sum, piol _ _ h _ j, mul_zero]; intros; apply brush_comm
    rw [H,add_zero]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; exact congrArg (fun x:Ink (U⊕Z)=> (motionJ θ).adjugate i j*x) (brush_comm (Sum.inl i) (Sum.inr t) (θ j))
  exact Or.inr h
omit [Fintype U] [Fintype Y] [Fintype Z] [DecidableEq U] in
private lemma chainT (ht:∀ i,brush t (W i)=0) : ∀ i, brush (Sum.inr (α:=U) t) (holdUp U (W i))=0 := by
  intro i
  apply PowerSeries.ext; intro n
  have hx : MvPolynomial.pderiv t (coeff n (W i))=0 := by rw [←blot_apply (d:=MvPolynomial.pderiv _), show blot _ _=0 from ht i,map_zero]
  simp only [brush, blot_apply,holdUp,coeff_map,map_zero]
  change MvPolynomial.pderiv _ (MvPolynomial.rename Sum.inr _) = _
  rw [MvPolynomial.pderiv_rename Sum.inr_injective,hx,map_zero]
set_option maxHeartbeats 600000 in
omit [Fintype Z] in
private lemma chainS (θ:U→ Ink (U⊕Z))(ht:∀ i,brush t (W i)=0)(p: Ink (U⊕Y)) :
    ∑ i:U, stream θ t i*brush (.inl i) (reroll W θ p)=(motionJ θ).det * brush (.inr t) (reroll W θ p) := by
  let A:= motionJ θ; let u i:= brush (.inr t) (θ i)
  have he x : ∑ i : U,A x i* stream θ t i = (motionJ θ).det*brush (.inr t) (θ x) := by
    change (A*ᵥ (A.adjugate*ᵥ u)) x= A.det*u x
    rw [Matrix.mulVec_mulVec,A.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]; rfl
  simp_rw [reroll,reroutes,Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,chainT ht, up_vacant,zero_mul,Finset.sum_const_zero,add_zero, Finset.mul_sum]
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
  rw [←mul_assoc,←he j,Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _
  rw [← mul_assoc, mul_comm (stream θ t i)]; rfl
/-- local closed-form density: Piola current with background `E` included. -/
theorem W_density {H K A :Matrix U U ℝ}(hH:H.transpose=H)(hK:K.transpose=K)(h:K*H=1)(p: Ink (U⊕Y))(t:Z)
    (θ:U→ Ink (U⊕Z))(W:Y→ Ink Z)
    (hL: IsUnit (motionJ θ).det)
    (ht:∀ i,brush t (W i)=0)
    (hx:constantCoeff (bodyQ Z K-reroll W θ (bodyQ Y A))=0) :
    brush t (Wick Z H ((motionJ θ).det*(raiseE (bodyQ Z K-reroll W θ (bodyQ Y A))*reroll W θ p)))=0 := by
  let k:= bodyQ Z K; let q:= bodyQ Y A; let B:=motionJ θ; let f:=reroll W θ p; let r:=reroll W θ q; let u:=stream θ t
  let v:=raiseE (k-r); let F:= v*f
  have R j : brush j v=v*(brush j k-brush j r) := by unfold v; rw [show brush j _ =_ from raise_diff hx (MvPolynomial.pderiv j), map_sub]
  have P j : brush j F=v*((brush j k-brush j r)*f+brush j f) := by rw [show F=v*f from rfl, Derivation.leibniz,R]; ring
  have Q (i : U) : brush (.inl i) (u i*F)-brush (.inl i) k * (u i*F) =
      brush (.inl i) (u i)*F+ v*(u i*brush (.inl i) f-f*(u i*brush (.inl i) r)) := by rw [Derivation.leibniz,P]; unfold F; ring
  have hx' : ∑ i,brush (.inl i) (u i*F)-∑ i:U,brush (.inl i) k * (u i*F)=brush (.inr t) (B.det*F) := by
    rw [← Finset.sum_sub_distrib]; simp_rw [Q,Finset.sum_add_distrib, ← Finset.mul_sum,←Finset.sum_mul,Finset.sum_sub_distrib,←Finset.mul_sum];
    rw [show ∑ i,brush (.inl i) (u i) = brush (.inr t) B.det from (chainH θ t).resolve_right (by simp [hL]), show ∑ i : U,u i*brush (.inl i) f = _ from chainS θ ht p, show ∑ i : U,u i*brush (.inl i) r = _ from chainS θ ht q]
    rw [Derivation.leibniz, P, show brush (.inr t) k=0 from body_aux t K]; ring
  change brush t (Wick Z H (B.det*F))=0; rw [←W_D,← hx',← Finset.sum_sub_distrib,W_sum]
  exact Finset.sum_eq_zero fun i _=> IBP hH hK h _ _
end Motion
end YM.WilsonCoeffUV.Blue
