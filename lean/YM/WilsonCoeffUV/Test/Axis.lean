import YM.WilsonCoeffUV.Test.Polynomial

/-! Signed turns intertwine projection test basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Embroider
open Filter Function Set Lattice RG Analysis
open scoped Topology BigOperators ContDiff
variable {D d h k:ℕ}

def dip (s:Signed) (i:Axis):ℝ:= if s.flip i then -1 else 1
lemma priceDip (s:Signed)(i:Axis): |dip s i|=1:= by unfold dip; split<;>simp

def compass (s:Signed): E→L[ℝ]E:= LinearMap.toContinuousLinearMap {
    toFun:= s.act
    map_add':= s.act_add
    map_smul':= fun a x=> by
       funext i; obtain ⟨j,rfl⟩:= s.perm.surjective i; simp }
lemma cardC (s:Signed)(w:Chamber): compass s w.val∈ Doll:=by
   change s.act w.val∈ Doll; rw [Metric.mem_closedBall, dist_zero_right]; refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr ?_; intro i; obtain ⟨j,rfl⟩:=s.perm.surjective i; rw [s.act_at]; split <;> (try rw [norm_neg]) <;> exact ((norm_le_pi_norm w.val j).trans (c_norm w))
lemma polar (s:Signed)(i): compass s (dot i)=dip s i • dot (s.perm i):=by
   funext j; obtain ⟨k,rfl⟩:= s.perm.surjective j; change s.act (dot i) (s.perm k)=_
   rw [s.act_at]; by_cases h:i=k
   · subst k; split <;> simp [dot,dip, *]
   simp [dip,dot, Ne.symm h]

def spinWord (s:Signed)(D):Scroll D →ₗ[ℝ] Scroll D where
    toFun f:=⟨f.val ∘ compass s, (show ContDiff ℝ (↑D) (f.val ∘ compass s) from (scribble f le_rfl).comp (compass s).contDiff)⟩
    map_add' _ _:= rfl
    map_smul' _ _:= rfl

lemma pencil (s t:Signed)(F:Scroll D): spinWord s D (spinWord t D F)= spinWord (t*s) D F:= Subtype.ext (funext fun _=>congr_arg F.val (Signed.act_mul ..).symm)
lemma recurs (s:Signed)(F:Scroll D): spinWord s⁻¹ D (spinWord s D F)=F:= Subtype.ext (funext fun _=> congr_arg F.val (Signed.act_inv ..))
lemma thaw (s:Signed)(f:Scroll D)(v:Fin k→Axis)(hk:k≤ D)(x:E): crease (spinWord s D f) v x=(∏ i, dip s (v i))*crease f (s.perm∘ v) (s.act x):=by
    unfold crease; rw [show (spinWord s D f).val= f.val ∘ compass s from rfl, ContinuousLinearMap.iteratedFDeriv_comp_right _ (scribble f le_rfl) _ (Nat.cast_le.mpr hk), ContinuousMultilinearMap.compContinuousLinearMap_apply]; simp_rw [Function.comp_apply,polar]; exact (iteratedFDeriv ℝ k f.val _).map_smul_univ ..
lemma spin_paid (s:Signed)(D): ∃ T:Volume D→L[ℝ]Volume D,(∀ f:Scroll D,T (page D f)=page D (spinWord s D f))∧‖T‖ ≤ 1:=by
    refine factoring (page D) (LinearMap.comp (page D) (spinWord s D)) (submitted (D:=D)) _ zero_le_one (fun f=>?_)
    rw [one_mul]; refine pledge (spinWord s D f) (norm_nonneg _) ?_; intro i h v w; rw [thaw _ _ _ h, norm_mul]; have he : ‖∏ j,dip s (v j)‖=1:=by simp [Real.norm_eq_abs, priceDip];
    rw [he,one_mul]; exact creased _ h _ ⟨_,cardC s w⟩
def spinV (s:Signed)(D): Volume D→L[ℝ]Volume D:= (spin_paid s D).choose
lemma chronic (s:Signed)(f:Scroll D): spinV s D (page D f)=page D (spinWord s D f):= (spin_paid ..).choose_spec.1 _
lemma pence (s:Signed)(D): ‖spinV s D‖ ≤ 1:= (spin_paid ..).choose_spec.2
lemma vrecurs (s:Signed)(x:Volume D): spinV s⁻¹ D (spinV s D x)=x:= by obtain ⟨f,rfl⟩:=submitted x; rw [chronic,chronic,recurs]

lemma encloses (s:Signed)(P:Patch)(w:Site P.L)(x:E): s.act (tucks P w x)=tucks P (s.act w) (s.act x):=by
    unfold tucks offset; rw [s.act_add]; congr 1; swap; · exact map_smul (compass s) ..

    rw [Ratio.lift_signed_of_odd P.odd_side]
    ext i; obtain ⟨a,rfl⟩:=s.perm.surjective i; rw [s.act_at]; split <;> simp [*]
lemma envy (s:Signed)(P:Patch)(w:Site P.L)(x:Volume D): foldWord P w D (spinV s D x)= spinV s D (foldWord P (s.act w) D x):=by
   obtain ⟨x,rfl⟩:= submitted x
   rw [chronic,observed,observed,chronic]; apply congr_arg (page D); exact Subtype.ext (funext fun i=> congr_arg x.val (encloses ..))

def spindle (s:Signed)(w:Spiral h):Spiral h:= ⟨w.val.map s.perm,by rw [Multiset.card_map]; exact w.property⟩
lemma spun_card (s:Signed)(w:Spiral h): rankS (spindle s w)=rankS w:= Multiset.card_map ..
def hue (s:Signed)(w:Multiset Axis):ℝ:= (w.map (dip s)).prod
lemma scarlet (s:Signed)(v:Fin d→Axis): hue s (twists v)=∏ i,dip s (v i):=by
    simp [hue,twists,List.map_ofFn,List.prod_ofFn]
lemma needle (s:Signed)(w:Fin d→Axis): (twists w).map s.perm=twists (s.perm ∘ w):=by simp [twists,List.map_ofFn]
lemma chargeV (s:Signed)(j:Multiset Axis): |hue s j|=1:=by
   obtain ⟨u,hu⟩:=present j
   calc
      _ = |hue s (twists u)|:= congr_arg abs (congr_arg _ hu.symm)
      _ = 1:=by simp [scarlet,Finset.abs_prod,priceDip]
lemma circle (s:Signed)(φ:Scroll D)(u:Spiral h)(hp:h≤D): crease (spinWord s D φ) (knurl u) 0=
     hue s u.val*crease φ (knurl (spindle s u)) 0:=by
   rw [thaw s φ (knurl u) (show rankS u ≤ D from le_trans u.property hp),s.act_zero,←scarlet,knurls]; congr 1
   let P:= spindle s u
   have he m (w:Fin m→Axis) (hk:twists w=P.val) : crease φ w 0= crease φ (knurl P) 0:= by
      have hv :m=rankS P:=by rw [←twists_card w,hk]; rfl
      subst m; exact creased_for_twist _ _ (hk.trans (knurls P).symm) φ (le_trans P.property hp) _
   exact he _ _ (by rw [←needle,knurls]; rfl)
lemma unspindle (s:Signed)(u:Spiral h): spindle s⁻¹ (spindle s u)=u:= Subtype.ext (by change (u.val.map _).map _=_; simp)

-- tests themselves spin with same matrix; use high coinage from Thaw.
theorem turning (s:Signed)(w:Spiral h)(H:h < D): spinV s D (page D (testa D (spindle s w).val)) = hue s w.val • page D (testa D w.val):=by
   let a:=spinWord s D (testa D (spindle s w).val)
   let b:=hue s w.val • testa D w.val
   rw [chronic,←map_smul]; change page D a=page D b
   apply sub_eq_zero.mp; rw [← map_sub]; apply norm_le_zero_iff.mp
   refine (assemble (F:=a-b) H (M:=0) le_rfl (fun i hi hp v x=> ?_) (fun i hi v=> ?_)).trans_eq (mul_zero _)
   · rw [←nib _ hp,map_sub,map_sub,nib _ hp]; unfold b; rw [map_smul,map_smul,nib _ hp]; unfold a; rw [thaw _ _ _ hp,coins_empty _ _ (lt_of_le_of_lt w.property hi), coins_empty _ _ (lt_of_le_of_lt (spindle s w).property hi),mul_zero,smul_eq_mul,mul_zero,sub_self,norm_zero]
   let t: Spiral h:=⟨twists v,by rw [twists_card]; exact hi⟩
   have hq (x:Scroll D): crease x v 0=crease x (knurl t) 0:=by
      have hk (m:ℕ)(p:Fin m→Axis)(hf:twists p=twists v): crease x p 0=crease x v 0:=by
          have hr : m=i :=by simpa only [twists_card] using congr_arg Multiset.card hf
          subst m; exact creased_for_twist _ _ hf x (le_trans hi H.le) _
      exact (hk _ _ (knurls t)).symm
   have he: rankS t≤D:= le_trans t.property H.le
   rw [hq]; change crease _ _ zeroC.val=0; rw [←nib _ he,map_sub,map_sub,nib _ he]; unfold b; rw [map_smul,map_smul,nib _ he]; change crease a _ 0- hue s _ • crease _ _ 0=0; unfold a; rw [circle _ _ _ H.le, coinage,coinage,knurls,knurls]
   by_cases hd:t=w
   · rw [hd]; simp
   rw [if_neg (fun ht=> hd (by have u:= congr_arg (spindle (h:=h) s⁻¹) (show spindle s t=spindle s w from Subtype.ext ht.symm); simpa only [unspindle] using u)),if_neg (fun h=>hd (Subtype.ext h.symm))]; simp
end YM.WilsonCoeffUV.Embroider
