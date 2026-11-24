import YM.OPE.Compatible.Lake.Sprint
/-!
# Projection repair of approximate reads
Use min singular from on-shell fields and silence of exact catalog erasures. These hypotheses still to discharge from genuine physical and virtual calculations. Do not require that official vacuum counterterms name the representation-identifiable perturbative matrices via a second scheme. Just a theorem about prices on physical quotient from approximate tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof Next.Extract Dash Extra.Histories
open Next.Rank Next.Rank.Price Extraction ContinuousLinearMap Treaty
open scoped Topology Classical BigOperators
variable {G:Gauge} {d:ℕ}{C:Family G} {S:Table C.book} {I J V:Type} [NormedAddCommGroup I] [NormedAddCommGroup J] [NormedSpace ℂ I] [NormedSpace ℂ J] [NormedAddCommGroup V][NormedSpace ℂ V]
section module
variable [FiniteDimensional ℂ V][FiniteDimensional ℂ J]
variable {a:I→L[ℂ]J}{b:J→L[ℂ]I}{f:I→L[ℂ]V}{U ε:ℝ}(ha:‖a‖≤U)(hb:‖b‖≤U)
 (h:a.comp b=ContinuousLinearMap.id ..)(ht:Module.finrank ℂ V=Module.finrank ℂ J)
 (hs:0≤ε)(hc:ε*U<1/2)(hz:∀ x,f x=0→ ‖a x‖≤ε *‖x‖)
include ha hb ht h hs hc hz
lemma spansElite : ∃ v : J≃L[ℂ] V,v.toContinuousLinearMap=f.comp b ∧ ‖v.symm.toContinuousLinearMap.comp f‖≤2*(U+ε) ∧
   ‖a - v.symm.toContinuousLinearMap.comp f‖ ≤ ε*(1+U*(2*(U+ε))):=by
    let z:= f.comp b; have hu : 0 ≤ U:= (norm_nonneg _).trans ha
    have he (x): a (b x)=x:= by change (a.comp b) x=_; rw [h]; rfl
    have hi: Injective z:=by
        apply (LinearMap.ker_eq_bot (f:=z.toLinearMap)).mp
        apply LinearMap.ker_eq_bot'.2; intro x hx
        change f (b x)=0 at hx; apply norm_le_zero_iff.mp
        have hZ:= hz _ hx; rw [he] at hZ; have hg: ‖x‖ ≤ ε*U*‖x‖:= hZ.trans (le_trans (mul_le_mul_of_nonneg_left ((b.le_opNorm _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))) hs) (mul_assoc ..).symm.le)
        by_contra! hh; linarith only [hg,mul_lt_mul_of_pos_right hc hh,hh]
    let H:= LinearEquiv.ofBijective z.toLinearMap ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ht.symm).mp hi⟩; let P:= H.toContinuousLinearEquiv
    let J' := P.symm.toContinuousLinearMap.comp f
    have hj': P.toContinuousLinearMap=z:= by ext1; rfl
    have hx (x): f (x-b (J' x))=0:=by rw [_root_.map_sub]; change _-z (J' x) =_; rw [← hj']; simp [J']
    have hy (x): ‖a x-J' x‖ ≤ ε*(‖x‖+U*‖J' x‖):=by
       have ht:= hz _ (hx x); rw [_root_.map_sub,he] at ht; apply ht.trans; apply mul_le_mul_of_nonneg_left _ hs; apply (norm_sub_le ..).trans; apply add_le_add le_rfl; exact (b.le_opNorm _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    have hM (x): ‖J' x‖ ≤ 2*(U+ε)*‖x‖:=by
       have hγ:= hy x; rw [norm_sub_rev] at hγ
       linarith only [norm_sub_norm_le (J' x) (a x),hγ,mul_le_mul_of_nonneg_right hc.le (norm_nonneg (J' x)),(a.le_opNorm x).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg x))]
    have hc:‖J'‖ ≤ 2*(U+ε):= opNorm_le_bound _ (by positivity) hM
    refine ⟨P,hj',hc,opNorm_le_bound (a-J') (by positivity) (fun x=>?_ )⟩; change ‖a x-J' x‖≤_
    have ht:=mul_le_mul_of_nonneg_left (hM x) (mul_nonneg hs hu); linarith only [ht,hy x]
end module
section inverse
variable (F R : I≃L[ℂ]I) {L r:ℝ}(hr:‖R.symm.toContinuousLinearMap‖≤L)(hh:‖F.toContinuousLinearMap-R.toContinuousLinearMap‖≤ r)(hk:r*L≤1/2)
include hr hh hk
lemma inverse_diff : ‖F.symm.toContinuousLinearMap-R.symm.toContinuousLinearMap‖≤2*L^2*r:=by
   let p:= F.symm.toContinuousLinearMap; let q:=R.symm.toContinuousLinearMap; let x:=F.toContinuousLinearMap; let y:=R.toContinuousLinearMap
   have hp:= (norm_nonneg _).trans hr; have hc:= (norm_nonneg _).trans hh
   have hv: p-q= p.comp ((y-x).comp q):=by ext1; simp only [p,q,y,x];simp
   have he : ‖p-q‖≤ ‖p‖*(r*L):=by
      rw [hv]; apply (opNorm_comp_le ..).trans; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (opNorm_comp_le ..).trans; rw [norm_sub_rev]; exact mul_le_mul hh hr (norm_nonneg _) hc
   calc
     _ ≤ _:= he
     _ ≤ 2*L*(r*L):=by apply mul_le_mul_of_nonneg_right ?_ (mul_nonneg hc hp); linarith only [he,norm_sub_norm_le p q,hr,mul_le_mul_of_nonneg_left hk (norm_nonneg p)]
     _ = _ := by ring
end inverse
end YM.OPE.Lake
