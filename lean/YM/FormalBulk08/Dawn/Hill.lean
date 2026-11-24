import YM.FormalBulk08.Dawn.Val

/-! Turning the body and the canon. Enforced transformation: evaluating a
column c on pulled links and pulled test `φ(s·slot)` equals evaluation
of the turned-column packet. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dawn
open Filter Set Function Lattice Chapel Tensor Planned.PrimaryIntegral295
open scoped Topology BigOperators ENNReal ContDiff Classical
variable {D j:ℕ} {L : Side}

def spoke (s : Signed): E4 →L[ℝ]E4:= (Ortho.motion s.ortho).toContinuousLinearMap
def airs (s:Signed)(A: Garden D) : Garden D:= ⟨A.val ∘ spoke s,(show ContDiff ℝ D A.val from A.property).comp (spoke s).contDiff⟩
def crest (s : Signed)(x:Pier):Pier:= ⟨spoke s x.val,by rw [Metric.mem_closedBall,dist_zero_right,show ‖spoke s x.val‖=‖x.val‖ from Ortho.move_norm ..]; exact still _⟩
def signP (s:Signed)(i:Axis):ℝ:= if s.flip i then -1 else 1
lemma spoke_axes (s: Signed)(a:Axis) : spoke s (basis a)=signP s a • basis (s.perm a):= by
    apply PiLp.ext; intro i; change M4.move s.ortho.val (basis a) i= _; rw [M4.move_basis]; unfold Signed.ortho
    by_cases h:s.perm a=i
    · subst i; cases h:s.flip a <;> simp [h, Signed.matrix_at,signP]
    simp [h,Ne.symm h,Signed.matrix_at,basis_eq]
def spinFlag (s:Signed)(k: Brush D): Brush D:=⟨k.1,s.perm ∘ k.2⟩
lemma airs_at (s:Signed)(A:Garden D)(k:Brush D)(x:Pier): (portrait D (airs s A)).val k x=(∏ i : Fin k.1.val,signP s (k.2 i))*(portrait D A).val (spinFlag s k) (crest s x) := by
   change iteratedFDeriv ℝ k.1.val (A.val ∘ spoke s) _ (basis ∘ k.2)= _
   rw [(spoke s).iteratedFDeriv_comp_right (tends A k.1) _ le_rfl,ContinuousMultilinearMap.compContinuousLinearMap_apply]
   simp_rw [Function.comp_apply,spoke_axes,ContinuousMultilinearMap.map_smul_univ]; rfl

def breezed (s:Signed)(p:Studio D) := portrait D (airs s (portrayed D p).choose)
lemma breeze_at (s:Signed)(p:Studio D)(k:Brush D)(x:Pier): (breezed s p).val k x=(∏ i : Fin k.1.val, signP s (k.2 i))*p.val (spinFlag s k) (crest s x) := by unfold breezed; rw [airs_at,(portrayed D _).choose_spec]
def froth (s:Signed)(D:ℕ) : Studio D→ₗ[ℝ]Studio D where
   toFun:=breezed s
   map_add':=fun p q=>by
      apply Subtype.ext; ext1 k; ext1 x; change ((breezed s (p+q)).val k x)=_; rw [breeze_at]; change _*(p.val _ _+q.val _ _) =(breezed s p).val k x+(breezed s q).val k x; rw [breeze_at, breeze_at,mul_add]
   map_smul':=fun a p=> by
      apply Subtype.ext; ext1 k; ext1 x; change (breezed s (a • p)).val k x=_; rw [breeze_at]; change _*(a*p.val _ _)=a*((breezed s p).val k x); rw [breeze_at];ring
lemma froth_airs (s:Signed)(T:Garden D): froth s D (portrait D T)=portrait D (airs s T):= by
    apply Subtype.ext; ext1 k; ext1 x; rw [airs_at]; exact breeze_at ..
lemma froth_walk (s t: Signed) (p:Studio D): froth (s*t) D p=froth t D (froth s D p):=by
    obtain ⟨f,rfl⟩:=portrayed D p; rw [froth_airs,froth_airs,froth_airs]; apply congr_arg; apply Subtype.ext; funext x
    change f.val (Ortho.move (s*t).ortho _)=f.val (Ortho.move s.ortho (Ortho.move t.ortho x)); rw [show (s*t).ortho = _ from Signed.inclusionO.map_mul s t,Ortho.move_mul];rfl
lemma froth_self (p:Studio D) : froth 1 D p=p:= by
   obtain ⟨f,rfl⟩:=portrayed D p; rw [froth_airs]; apply congr_arg; apply Subtype.ext; funext x; change f.val (Ortho.move (1:Signed).ortho x)=_;rw [show (1:Signed).ortho=1 from Signed.inclusionO.map_one,Ortho.move_one]
lemma froth_inter (s:Signed)(x:Site L)(hp:Odd L.val)(h:2≤L.val)(p:Studio D) : throughW x D h (froth s D p)=froth s D (throughW (s.act x) D h p):= by
    obtain ⟨f,rfl⟩:=portrayed D p; rw [froth_airs,through_show,through_show,froth_airs]; apply congr_arg; apply Subtype.ext; funext y; change f.val (spoke s (bay x y))=f.val (bay (s.act x) (spoke s y)); rw [bay,map_add,map_smul,pith,map_smul,bay,pith,Ratio.lift_signed_of_odd hp];
    apply congr_arg f.val; suffices e:(spoke s) (Place.seat (lift x))=Place.seat (s.act (lift x)) by rw [e]
    apply PiLp.ext; intro i; change Ortho.move s.ortho (Place.seat (lift x)) i = _; rw [Signed.ortho_move]; obtain ⟨k,rfl⟩:=s.perm.surjective i; simp only [Signed.act_at, Place.seat_apply]; cases s.flip k <;> simp

-- canonical monomial transformation from v to `φ∘s`.
def breeze (p:Seasons)(s:Signed): Seasons:=p ∘ s.perm
lemma breeze_h (p:Seasons)(s: Signed): upper (breeze p s)=upper p:= Fintype.sum_equiv s.perm _ _ fun _=>rfl
lemma spunk (p:Seasons)(s t:Signed):breeze p (s*t)=breeze (breeze p s) t:=rfl
lemma spin_word (s: Signed)(b: Brush D): word (spinFlag s b)= breeze (word b) s⁻¹:=by
   ext i; change (∑ j, grain (s.perm (b.2 j))) i= (∑ j, grain (b.2 j)) (s.perm.symm i);rw [Finset.sum_apply,Finset.sum_apply]; refine Finset.sum_congr rfl fun a _=>?_; simp only [grain,Equiv.symm_apply_eq];congr

def tone (p:Seasons)(s:Signed):ℝ:=∏ i:Axis, signP s i ^ breeze p s i
lemma moved (s:Signed)(v:E4)(i:Axis): spoke s v (s.perm i)= signP s i*v i:=by
   change Ortho.move s.ortho _ _ = _; rw [Signed.ortho_move]; change s.act (WithLp.ofLp v) (s.perm i)=_; rw [Signed.act_at]; cases h:s.flip i <;> simp [signP,h]
lemma tone_norm (p:Seasons)(s:Signed): ‖tone p s‖=1:=by unfold tone; rw [norm_prod]; simp [signP,apply_ite (‖·‖)]
lemma breezy (p:Seasons)(s:Signed): froth s D (cone D p)=tone p s • cone D (breeze p s):= by
   rw [cone,cone,froth_airs,←map_smul]; apply congr_arg;apply Subtype.ext;funext x
   change (∏ i,petal i (p i) (spoke s x))=tone p s *∏ i,petal i (breeze p s i) x
   unfold tone;rw [←Finset.prod_mul_distrib]; symm; refine Fintype.prod_equiv s.perm _ _ fun i=>?_; unfold breeze petal; simp only [moved,mul_pow,Function.comp_apply];ring

lemma spun (p: Seasons)(hp : upper p≤D)(s:Signed)(T:Studio D): notch p hp (froth s D T)=tone (breeze p s⁻¹) s * notch (breeze p s⁻¹) ((breeze_h p s⁻¹).trans_le hp) T := by
    let k:= finger hp; let B:=spinFlag s k;let η:=breeze p s⁻¹; have he: word k=p:= (draw_any p hp).choose_spec; have hb : word B=η:=by unfold B η; rw [spin_word,he]
    let z:=tone η s
    have h' (A:Studio D): notch p hp (froth s D A)=(∏ i:Fin k.1.val, signP s (k.2 i))* notch η ((breeze_h p s⁻¹).trans_le hp) A := by
       rw [notched hp _ k he,notched _ _ B hb]; rw [show (froth s D A).val _ _= _ from breeze_at s A k origin]; have h:crest s origin=origin:= Subtype.ext ((spoke s).map_zero); rw [h]
    have hv:= h' (cone D η); rw [breezy,_root_.map_smul,show breeze η s=p by unfold η; rw [←spunk,inv_mul_cancel];rfl, notch_basis,notch_basis] at hv; simp only [↓reduceIte,smul_eq_mul,mul_one] at hv
    rw [h',←hv]
end YM.FormalBulk08.Dawn
