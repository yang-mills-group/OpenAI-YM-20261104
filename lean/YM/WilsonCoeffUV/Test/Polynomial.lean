import YM.WilsonCoeffUV.Test.Monomials

/-! Joint test stencil: compact, no order loss step. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Embroider
open Filter Function Set Lattice RG Analysis
open scoped Topology BigOperators ContDiff
variable {D d h k:ℕ}

def claim (D) (v:Knob D) (w:Chamber): Vote D :=
    let f:Volume D →ₗ[ℝ] ℝ:={
                                toFun p:= p.val v w
                                map_add' _ _:= rfl
                                map_smul' _ _:=rfl }
    f.mkContinuous 1 (fun a=>by rw [one_mul]; exact registry a v w)
@[simp] lemma claim_take (p:Volume D)(v:Knob D)(w:Chamber): claim D v w p=p.val v w:=rfl
lemma nib (p:Scroll D)(hi:k ≤ D)(v:Fin k→Axis)(w:Chamber): claim D ⟨⟨k,Nat.lt_succ_of_le hi⟩,v⟩ w (page D p)=crease p v w.val:=rfl

-- polynomial head on fine-address pull of order h from any F

def flowering (h:ℕ)(F:Scroll D):Scroll D := ∑ a:Spiral h, crease F (knurl a) 0 • testa D a.val
lemma flowering_at (F:Scroll D)(_hh:h ≤ D)(v:Fin k→Axis)(hk:k≤D)(x:Chamber):
    crease (flowering h F) v x.val=∑ a:Spiral h, crease F (knurl a) 0 * crease (testa D a.val) v x.val:=by
   unfold flowering; rw [← nib _ hk,map_sum,map_sum]; exact Finset.sum_congr rfl fun i _=>by rw [map_smul,map_smul,nib _ hk]; rfl
lemma flair (F:Scroll D)(hh:h ≤ D)(v:Fin d→Axis)(hv:d≤h): crease (flowering h F) v 0=crease F v 0:=by
   let a:Spiral h:= ⟨twists v,by rw [twists_card]; exact hv⟩
   change crease _ _ zeroC.val=_; rw [show crease _ _ _= _ from flowering_at F hh v (le_trans hv hh) zeroC, Finset.sum_eq_single a]
   · change crease F (knurl a) _*crease (testa D (twists v)) v 0=_
     rw [coinage,if_pos rfl,mul_one]
     suffices hg: ∀ m, m ≤ D → ∀ u:Fin m → Axis,twists u=twists v → crease F u 0=crease F v 0 by exact hg _ (a.property.trans hh) _ (knurls a)
     intro m ht u he
     have hj:m=d:= by simpa only [twists_card] using congr_arg Multiset.card he
     subst m; exact creased_for_twist u v he F ht _
   · intro b _ hb; change _*crease (testa D b.val) _ 0=_; rw [coinage,if_neg (mt Subtype.ext hb),mul_zero]
   simp
lemma flowery_high (F:Scroll D)(hh:h ≤ D)(v:Fin d→Axis)(hp:d≤ D)(he:h<d)(x:Chamber): crease (flowering h F) v x.val=0:=by
   rw [flowering_at _ hh v hp x]; exact Finset.sum_eq_zero fun a _=> by rw [coins_empty a.val _ (lt_of_le_of_lt a.property he),mul_zero]
private lemma reglued {s:ℕ}(h:s≤D)(p q:Scroll D)(v:Fin s→Axis)(w:Chamber): crease (p-q) v w.val=crease p v w.val-crease q v w.val:=by simp_rw [← nib _ h,map_sub]
lemma zero_low (F:Scroll D)(hh:h ≤ D)(v:Fin d→Axis)(hp:d≤h): crease (F-flowering h F) v 0=0:=by change crease _ _ zeroC.val=0; rw [show crease _ _ _=_ from reglued (le_trans hp hh) F (flowering h F) v zeroC]; change crease F v 0-crease _ _ 0=_; rw [flair F hh v hp]; ring
private lemma smoth (f:Scroll D) (hp:d<D) (v:Fin d→Axis)(x:E): DifferentiableAt ℝ (crease f v) x :=
     (ContinuousMultilinearMap.apply ℝ (fun _:Fin d => E) ℝ (dot ∘ v)).differentiableAt.comp x ((scribble f le_rfl).contDiffAt.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr hp))
private lemma fecon (f:Scroll D)(hp:d<D)(v:Fin d→Axis)(x:E)(i:Axis): fderiv ℝ (crease f v) x (dot i)=crease f (Fin.cons i v) x:=by
     unfold crease; rw [show dot ∘ Fin.cons i v=Fin.cons (dot i) (dot ∘ v) from funext fun i=>Fin.cases rfl (fun _=>rfl) i]; exact (cons_jet (f:=f.val) (scribble f (Nat.succ_le_iff.mpr hp)).contDiffAt (dot i) _).symm
private lemma tip {M:ℝ} (h:0 ≤ M) (f:Scroll D) (v:Fin d→Axis)(hp:d<D)(x:Chamber) (hf:∀ i:Axis,‖crease f (Fin.cons i v) x.val‖≤ M): ‖fderiv ℝ (crease f v) x.val‖ ≤ 4*M := by
     apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro a
     let L:=fderiv ℝ (crease f v) x.val
     have he : ∑ i:Axis, a i • dot i=a:=by funext j; simp [dot, Finset.sum_apply,Pi.single_apply]
     change ‖L a‖≤ _; nth_rw 1 [← he]; rw [map_sum]; refine le_trans (norm_sum_le ..) ?_
     refine le_trans (Finset.sum_le_sum (f:=fun i:Axis => ‖L (a i • dot i)‖) (g:=fun _=> ‖a‖*M) (fun i _=> ?_)) (le_of_eq (by simp [Axis]; ring))
     rw [map_smul,norm_smul, show L (dot i)=_ from fecon f hp v _ i]; exact mul_le_mul (norm_le_pi_norm a _) (hf i) (norm_nonneg _) (norm_nonneg _)

lemma assemble {h:ℕ}(he:h<D){F:Scroll D}{M:ℝ}(hm:0≤ M)(hf:∀ i, h < i → i≤D → ∀ v:Fin i→Axis, ∀ w:Chamber, ‖crease F v w.val‖≤ M)(hl:∀ i≤h,∀ v:Fin i→Axis, crease F v 0=0): ‖page D F‖ ≤ 4^(h+1)*M:=by
    have hx (d i:ℕ)(hr:i+d=h+1)(v:Fin i→Axis)(x:Chamber): ‖crease F v x.val‖≤4^d*M:=by
       induction d generalizing i x with
       | zero=> simp; exact hf i (by omega) (by omega) v x
       | succ d ih=>
           let U:=crease F v
           have hk: ∀ x∈Doll, ‖fderiv ℝ U x‖≤4^(d+1)*M:=by
              intro y hy; rw [pow_succ',mul_assoc]; exact tip (by positivity) F v (by omega) ⟨y,hy⟩ (fun a=> ih (i+1) (by omega) _ _)
           have hp:= (convex_closedBall (0:E) ((2:ℝ)⁻¹)).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (fun z _=>smoth F (by omega) v z) hk zeroC.property x.property
           have hq:crease F v zeroC.val=0:= hl i (by omega) _
           rw [hq, show zeroC.val=(0:E) from rfl, sub_zero,sub_zero] at hp
           apply hp.trans; exact mul_le_of_le_one_right (by positivity) ((c_norm _).trans (by norm_num))
    refine pledge F (by positivity) (fun i hi v x=> ?_)
    by_cases hk:i≤ h
    · exact le_trans (hx (h+1-i) i (by omega) v x) (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hm)
    exact (hf i (by omega) hi v x).trans (le_mul_of_one_le_left hm (one_le_pow₀ (by norm_num)))

variable (P:Patch)(w:Site P.L)
def halo (a : Multiset Axis) (F:Scroll D):= creaAux a (growWord P w D F)
where creaAux a p:= crease p (present a).choose 0
lemma shining (F:Scroll D)(p:Scroll D): (growWord P w D F - p)+p=growWord P w D F:= by abel
lemma tiling (F:Scroll D)(hh:h < D): ‖page D (growWord P w D F-flowering h (growWord P w D F))‖≤4^(h+1)*(speck P^(h+1)*‖page D F‖):=by
   let t:=growWord P w D F
   apply assemble hh (by positivity [speck_pos P]); swap; · exact fun i hi v=> zero_low t hh.le _ hi
   intro i hi hv v x; rw [reglued hv, flowery_high _ hh.le _ hv hi,sub_zero, narrow _ _ _ _ hv,norm_mul,norm_pow, Real.norm_eq_abs, abs_of_pos (speck_pos _)]
   exact mul_le_mul (pow_le_pow_of_le_one (speck_pos P).le (speck_le _) (by omega)) (creased F hv v ⟨_,tucks_enter ..⟩) (norm_nonneg _) (by positivity [speck_pos P])
lemma halo_bound (F:Scroll D)(a:Multiset Axis)(he:a.card ≤ D): ‖halo P w a F‖≤speck P ^ a.card * ‖page D F‖:=by
    unfold halo halo.creaAux; rw [narrow _ _ _ _ he,norm_mul,norm_pow,Real.norm_eq_abs,abs_of_pos (speck_pos _)]; exact mul_le_mul_of_nonneg_left (creased F he _ ⟨_,tucks_enter P w zeroC⟩) (by positivity [speck_pos P])
lemma flower_hint (F:Scroll D)(h:ℕ): flowering h (growWord P w D F)=∑ i:Spiral h, halo P w i.val F • testa D i.val:=rfl

lemma emboss (a:Spiral h)(H:h < D): page D (growWord P w D (testa D a.val))=page D (flowering a.val.card (growWord P w D (testa D a.val))):=by
    let f:=growWord P w D (testa D a.val)
    let i:= a.val.card
    have he:i < D:= lt_of_le_of_lt a.property H
    apply sub_eq_zero.mp; rw [←map_sub]; refine norm_le_zero_iff.mp ((assemble (F:=f-flowering i f) he (M:=0) le_rfl ?_ (fun d t v=> zero_low f he.le v t)).trans_eq (mul_zero _))
    intro d t z v x; unfold f; rw [reglued z,flowery_high _ he.le v z t,sub_zero,narrow _ _ _ _ z, coins_empty a.val _ t,mul_zero,norm_zero]
-- top test evaluates at all addresses; independent preimage
lemma crest (a:Multiset Axis)(x y:E)(v:Fin d→ Axis)(he:d=a.card)(hv:d<D) : crease (testa D a) v x=crease (testa D a) v y:= by
     apply is_const_of_fderiv_eq_zero (𝕜:=ℝ); · exact fun x=> smoth _ hv v _
     intro z; ext u
     let F:=fderiv ℝ (crease (testa D a) v) z
     have hF (i:Axis): F (dot i)=0:= (fecon (testa D a) hv v _ _).trans (coins_empty _ _ (by omega) _)
     have hh: ∑ i:Axis,u i • dot i=u := by ext j; simp [dot,Finset.sum_apply,Pi.single_apply]
     change F u=0; rw [←hh,map_sum]; simp [hF]
lemma lap (a:Spiral h)(F:Scroll D)(_E:h<D): halo P w a.val F= speck P ^ a.val.card * crease F (knurl a) (offset P w):= by unfold halo halo.creaAux; rw [narrow _ _ _ _ (le_trans a.property _E.le)]; simp [knurl,tucks]; left; rfl
lemma denim {P:Patch}(a b:Multiset Axis)(w:Site P.L)(hv:a.card=b.card)(hp:b.card<D) : halo P w a (testa D b)=speck P ^ b.card * (if a=b then 1 else 0):=by
    unfold halo halo.creaAux; rw [narrow _ _ _ _ (hv ▸ hp.le),crest _ _ (0:E) _ hv (by omega),coinage, (present _).choose_spec,hv]; simp only [eq_comm (a:=a) (b:=b)]
end YM.WilsonCoeffUV.Embroider
