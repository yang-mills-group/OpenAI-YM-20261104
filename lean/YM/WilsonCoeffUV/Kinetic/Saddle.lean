import YM.WilsonCoeffUV.Kinetic.Whiten
/-!
# Active/external arrays in auxiliary finite saddle lane
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue.Cameo
open Matrix Function PowerSeries Filter
open scoped Topology ContDiff BigOperators
variable {U V : Type*} [Fintype U][DecidableEq U][Fintype V][DecidableEq V]
variable {f g : Lawn (U ⊕ V)→ℝ}
omit [Fintype U] in
lemma jBasis (p:Lawn V): (rightFlag U V).transpose *ᵥ p=Sum.elim (0:Lawn U) p:=by
    ext1 i; cases i with
    | inl i=> simp [rightFlag,mulVec,dotProduct]
    | inr i=> simp [rightFlag,mulVec,dotProduct,ite_mul]
def piIn (p:Lawn V) : Lawn (U⊕V):= Sum.elim (0:Lawn U) p
def baseP (f:Lawn (U⊕V)→ℝ): Lawn V→ℝ:= f ∘ piIn
lemma immersion : Green (piIn (U:=U) (V:=V)):=by rw [show piIn=fun p:Lawn V=> (rightFlag U V).transpose *ᵥ p from funext fun p=> (jBasis p).symm]; exact board _
lemma immersed (p:Green f): Green (baseP f) := by
    unfold baseP; apply ContDiffAt.comp _ _ immersion; rw [show piIn (U:=U) (0:Lawn V) =0 from funext fun x=>by cases x<;>rfl]; exact p
omit [Fintype U] in
lemma inkBasis : loom ((rightFlag U V).transpose)=projectZero:=by
   apply serial_ext (by simp [loom]) _ (by simp [loom,projectZero]); intro p; induction p using MvPolynomial.induction_on with
   | C a=> change loom ((rightFlag U V).transpose) (realS a)=projectZero (realS a); rw [loom_real]; simp [projectZeroPoly,projectZero,realS]
   | add p q h t=> simp_rw [map_add,h,t]
   | mul_X p i h=> simp only [map_mul,h]; congr 1; cases i with
                   | inl i=> rw [show C _=path _ from rfl,loom_pin,project_var]; simp [rightFlag]
                   | inr i=> rw [show C _=path _ from rfl,loom_pin,project_ext]; simp [rightFlag,ite_smul]
lemma projectBasis (h:Green f): projectZero (jet f)=jet (baseP f):=by
    rw [←inkBasis,loom_jet _ _ h]; simp_rw [jBasis]; rfl
lemma liftBasis {g:Lawn V →ℝ} (h:Green g):holdUp U (jet g)=jet (g ∘ rightArm (U:=U)):=by rw [← hold_loom,loom_jet _ _ h]; simp_rw [right_hit]; rfl
omit [Fintype U] [DecidableEq U] in
lemma snakeX (i:U)(P:Ink U) : brush i (X^2*P)= X^2*brush i P:= by rw [pow_two, mul_assoc,brush_X,brush_X,←mul_assoc]
omit [DecidableEq U] [Fintype V] [DecidableEq V] in
lemma moonRub (i:U)(P:Matrix U U ℝ) : projectZero (slopeQ V P i)=0 := by unfold slopeQ; rw [map_sum]; simp_rw [project_smul]; simp_rw [project_var]; simp
omit [DecidableEq U] [Fintype V] [DecidableEq V] in
lemma moonZero (P:Matrix U U ℝ) : projectZero (bodyQ V P)=0:=by unfold bodyQ; rw [project_smul,map_sum]; simp_rw [map_mul,project_var]; simp

def retool (θ:Lawn (U⊕V)→ Lawn U): Ink (U⊕V)→+* Ink (U⊕V):=reroll path (spool θ)
def spider (θ:Lawn (U⊕V)→ Lawn U) (x:Lawn (U⊕V)): Lawn (U⊕V):= Sum.elim (θ x) (rightArm x)
lemma spider_green {θ:Lawn (U⊕V)→Lawn U}(h:Green θ) : Green (spider θ):= sumGreen h rightGreen
omit [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] in
lemma spider_zero {θ:Lawn (U⊕V)→Lawn U}(h:θ 0=0): spider θ 0=0:=by ext1 i; unfold spider; rw [h]; cases i<;> rfl
omit [DecidableEq U] [DecidableEq V] in
lemma pivot (θ:Lawn (U⊕V)→ Lawn U): retool θ= train (spool (spider θ)):=by
    have he : Sum.elim (spool θ) (holdUp U ∘ (path (U:=V)))=spool (spider θ):=by
       funext i; cases i with
       | inl i=> rfl
       | inr i=>
          rw [Sum.elim_inr,Function.comp_apply,up_var]; ext1 k; rw [spool, coeff_mk]; change coeff k _=coeff (k+1) (jet (fun x:Lawn (U⊕V)=>x (.inr i))); simp_rw [jet_arg,coeff_succ_X_mul]
    exact congr_arg train he
omit [DecidableEq U] [DecidableEq V] in
lemma retire (θ:Lawn (U⊕V)→Lawn U) : constantCoeff (retool θ X)=0:= by unfold retool; rw [reroll_X]; simp
omit [DecidableEq U] [DecidableEq V] in
lemma retool_tall (θ:Lawn (U⊕V)→Lawn U)(P:Ink V) : retool θ (holdUp U P)= holdUp U P:= by rw [retool,reroll_up,train_id,RingHom.id_apply]
-- project rub and H sector
lemma shake (h:Green f)(i:U) : projectZero (brush (.inl i) (jet f))= X*jet (baseP (rub f (.inl i))) :=by rw [sap h,map_mul, show projectZero (X:Ink (U⊕V))=X by simp [projectZero],projectBasis (rubbed h _)]
lemma shook (h:Green f)(i j:U): projectZero (brush (.inl i) (brush (.inl j) (jet f)))=X^2 *jet (baseP (rub (rub f (.inl j)) (.inl i))):= by rw [sap h,brush_X,map_mul, show projectZero (X:Ink (U⊕V))=X by simp [projectZero], shake (rubbed h _),←mul_assoc,pow_two]
-- exact initial Hess from unwhitened derivative: second hit in rotation. θ needn't have diagonal slope a priori.
omit [DecidableEq V] in
lemma rake (K:Matrix U U ℝ)(θ:Lawn (U⊕V)→ Lawn U)(hk:K.transpose=K)(j:U): brush (.inl j) (retool θ (bodyQ V K))=∑ i:U, brush (.inl j) (spool θ i)*∑ b: U,K i b • spool θ b :=by
    unfold retool reroll; rw [reroutes,Fintype.sum_sum_type]; simp only [Sum.elim_inl,Sum.elim_inr,Function.comp_apply, up_vacant,zero_mul, Finset.sum_const_zero,add_zero]; exact Finset.sum_congr rfl (fun i _=>by rw [body_derived K hk]; change _*reroll path (spool θ) _=_; rw [moment_const])

omit [DecidableEq V] in
lemma p0_motion {θ:Lawn (U⊕V)→Lawn U}(h:Green θ)(hz:θ 0=0)(u:edgeM θ 0=1)(i j:U):
    constantCoeff (brush (.inl j) (spool θ i))= (1 : Matrix U U (POL (U⊕V))) i j:=by rw [spool_ext θ i h hz,jet_lead]; change MvPolynomial.C (edgeM θ 0 i j)=_; rw [u]; simp only [Matrix.one_apply]; split <;> first | rw [map_zero] | rw [map_one]

omit [DecidableEq V] in
lemma pulse_cc {θ:Lawn (U⊕V)→ Lawn U}(h:Green θ)(hz:θ 0=0)(p:edgeM θ 0=1)(K:Matrix U U ℝ)(hk:K.transpose=K)(i j:U):
    constantCoeff (brush (.inl i) (brush (.inl j) (retool θ (bodyQ V K))))= MvPolynomial.C (K j i):=by
    have hx (P:Ink (U⊕V))(i:U): constantCoeff (brush (.inl i) P)= MvPolynomial.pderiv (.inl i) (constantCoeff P):=by rw [←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply,brush,blot_apply]
    have hb x: constantCoeff (brush (.inl i) (brush (.inl j) (spool θ x)))=0:=by
        rw [hx,p0_motion h hz p]; rw [Matrix.one_apply]; split<;>simp
    rw [rake K θ hk,map_sum]; simp_rw [Derivation.leibniz,smul_eq_mul,map_sum,map_add,map_mul,Derivation.map_smul,map_sum,hb, constantCoeff_smul,p0_motion h hz p,mul_zero,add_zero]
    rw [Finset.sum_eq_single j];
    · simp only [Matrix.one_apply_eq,one_mul]; rw [Finset.sum_eq_single i];
      · simp [Algebra.smul_def]
      · intro x _ hx; rw [Matrix.one_apply_ne hx,smul_zero]
      simp
    · intro b _ h; rw [Matrix.one_apply_ne h,zero_mul]
    simp
omit [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V] in
lemma cc_proj {f g:Ink (U⊕V)}(h:constantCoeff f=constantCoeff g): constantCoeff (projectZero f)=constantCoeff (projectZero g):=by rw [← coeff_zero_eq_constantCoeff_apply,projectZero, ←coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_map]; simp_rw [coeff_zero_eq_constantCoeff_apply,h]
lemma cc_equal {U:Type*}{f g: Ink U}(h:constantCoeff f=constantCoeff g)(i:U): constantCoeff (brush i f)=constantCoeff (brush i g):=by simp_rw [←coeff_zero_eq_constantCoeff_apply,brush,blot_apply]; simp only [coeff_zero_eq_constantCoeff_apply,h]
-- receipt when first motion not known centered horizontally.
def avenue (f:Lawn (U⊕V)→ℝ) (i:U):=baseP (rub f (.inl i))
def sandH (f:Lawn (U⊕V)→ℝ) (x:Lawn V) : Matrix U U ℝ:= of fun i j=> baseP (rub (rub f (.inl j)) (.inl i)) x

structure Fathom (f:Lawn (U⊕V)→ℝ) (θ:Lawn (U⊕V)→Lawn U) (E: Ink (U⊕V)) :Prop where
     θo : θ 0=0
     θp : Green θ
     ea : edgeM θ 0=1
     sta: Green f
     snap i: jet (avenue f i)=0
     shine: X^2*retool θ E=jet f
lemma centerK {E:Ink (U⊕V)}{B:Ink V}{θ} (K:Matrix U U ℝ)(h:Fathom f θ E) (hk:K.transpose=K)(p:constantCoeff E=constantCoeff (bodyQ V K+holdUp U B)) : sandH f 0=K:=by
    ext1 i j
    have he : constantCoeff (retool θ E)=constantCoeff (retool θ (bodyQ V K)+holdUp U B):=by
        rw [← retool_tall θ,← map_add]
        simp_rw [←coeff_zero_eq_constantCoeff_apply]; exact filtered (retire θ) (k:=1) (fun i hi=>by rw [show i=0 by omega]; simpa only [coeff_zero_eq_constantCoeff_apply]) 0 (by omega)
    have ht: projectZero (brush (.inl i) (brush (.inl j) (retool θ E))) = jet (baseP (rub (rub f (.inl j)) (.inl i))):=by
        have H:=shook h.sta i j; rw [← h.shine,snakeX,snakeX,map_mul,map_pow,show projectZero (X:Ink (U⊕V))=X by simp [projectZero]] at H; exact mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) H
    have hz:=cc_proj (cc_equal (cc_equal he (.inl j)) (.inl i)); rw [ht, jet_lead,map_add,up_vacant, add_zero] at hz
    rw [projectZero,←coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_zero_eq_constantCoeff_apply,pulse_cc h.θp h.θo h.ea K hk] at hz; simp [projectZeroPoly,MvPolynomial.algebraMap_eq] at hz
    change _ = K i j
    rw [← show K j i=K i j from congr_fun (congr_arg (fun M:Matrix U U ℝ=>M i) hk) j]; exact hz

-- polynomial gap at Hess

def loomK (K:Matrix U U ℝ)(x:Lawn (U⊕V)):= (1/2:ℝ)*∑ i,leftArm x i * (K*ᵥ leftArm x) i
omit [DecidableEq U] [DecidableEq V] in
lemma loomK_green (K:Matrix U U ℝ): Green (loomK (V:=V) K):=by
    unfold Green loomK leftArm Matrix.mulVec dotProduct; fun_prop
lemma flare (K:Matrix U U ℝ) : jet (loomK (V:=V) K)= X^2*bodyQ V K:= by
    let g (i:U) (x:Lawn (U⊕V)):=x (.inl i); have hf i:Green (g i) := contDiffAt_apply ..
    let u (i:U): Lawn (U⊕V)→ℝ := fun x=> (K *ᵥ leftArm x) i
    have hu i : Green (u i):= ((contDiffAt_apply ℝ ℝ ..).comp _ (((K.mulVecLin).toContinuousLinearMap.contDiff.contDiffAt).comp _ (leftGreen (X:=U) (Y:=V))))
    have he i:jet (u i)= X * slopeQ V K i:=by
       rw [show u i =∑ j,(fun _:Lawn (U⊕V)=> K i j)*g j from funext fun x=> by rw [Finset.sum_apply]; rfl,slopeQ,jet_sum _ (fun j=> (fun _:Lawn (U⊕V)=>K i j)*g j) (fun j _=>ContDiffAt.mul contDiffAt_const (hf j)),Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [jet_mul (g:=g j) (f:=fun _=>K i j) contDiffAt_const (hf j),jet_const, show jet (g j)=_ from jet_arg (.inl j : U⊕V),Algebra.smul_def,real_alg]; ring
    let T: Lawn (U⊕V)→ℝ:= ∑ i,g i*u i
    have hw i:Green (g i*u i):= (hf i).mul (hu i)
    have ht:Green T:=by unfold T Green; rw [show (∑ i,g i*u i)=fun x=> ∑ i,g i x*u i x from funext fun x=> by rw [Finset.sum_apply]; rfl]; exact ContDiffAt.sum (fun i _=> (hf i).mul (hu i))
    rw [show loomK (V:=V) K=(fun _ => (1/2:ℝ))*T from funext fun x=> by unfold loomK; simp only [T,Pi.mul_apply,Finset.sum_apply]; rfl,jet_mul (f:=fun _=> (1/2:ℝ)) contDiffAt_const ht, jet_const,bodyQ]; unfold T; rw [jet_sum _ _ (fun i _=>hw i),Algebra.smul_def,real_alg,mul_left_comm (X^2),Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [jet_mul (hf i) (hu i),show jet (g i)=_ from jet_arg (.inl i : U⊕V),he]; ring

variable {E:Ink (U⊕V)}{θ:Lawn (U⊕V)→Lawn U}
lemma sandbar (h:Fathom f θ E)(K:Matrix U U ℝ)(u:K.transpose=K){k:ℕ}(p:∀ i j, Equal k (jPrint (sandH f) i j) (realS (K j i))):
    let g:=f-(baseP f ∘ rightArm)-loomK K
    projectZero (jet g)=0 ∧ (∀ i:U,projectZero (jet (rub g (.inl i)))=0)∧∀ i j:U, Dark k (projectZero (jet (rub (rub g (.inl j)) (.inl i)))):=by
    intro g
    have hg: Green g:= ContDiffAt.sub (ContDiffAt.sub h.sta ((immersed h.sta).comp (f:=rightArm) 0 rightGreen)) (loomK_green _)
    have he: jet g=jet f-holdUp U (jet (baseP f))-X^2*bodyQ V K:=by
        have he: Green (baseP f ∘ rightArm (U:=U)):= (immersed h.sta).comp (f:=rightArm) 0 rightGreen
        rw [liftBasis (immersed h.sta),jet_sub (f:=f-(baseP f ∘ rightArm)) (h.sta.sub he) (loomK_green _),jet_sub h.sta he,flare]
    have hx : projectZero (X:Ink (U⊕V))=X:=by simp [projectZero]
    constructor
    · rw [he,map_sub,map_sub, map_mul,projectBasis h.sta,project_up,sub_self, moonZero,mul_zero,sub_zero]
    constructor
    · intro i; apply mul_left_cancel₀ (a:=X) X_ne_zero
      rw [projectBasis (rubbed hg (.inl i)), ← shake hg, he, map_sub,map_sub, snakeX,map_sub (brush _),up_vacant,sub_zero, shake h.sta, body_derived K u,map_mul, moonRub, show jet (baseP (rub f (.inl i)))=0 from h.snap i]; simp
    intro i j; rw [projectBasis (rubbed (rubbed hg _) _)]
    have hv:= shook hg i j; rw [he] at hv
    simp only [map_sub,up_vacant] at hv
    rw [shook h.sta, snakeX, snakeX,body_derived K u, slope_derived, map_mul,map_pow,hx] at hv
    have ht : projectZero (realS (U:=U⊕V) (K j i))=realS (K j i):= by simp [realS,projectZero,projectZeroPoly]
    rw [ht,map_zero,map_zero, sub_zero,← mul_sub] at hv
    rw [← mul_left_cancel₀ (a:=X^2) (pow_ne_zero 2 X_ne_zero) hv]; exact scotch (p i j)

abbrev deficit (K:Matrix U U ℝ)(f:Lawn (U⊕V)→ℝ): Lawn (U⊕V)→ℝ := f-(baseP f∘rightArm)-loomK K
def faintRest (K:Matrix U U ℝ)(E:Ink (U⊕V)) : Ink (U⊕V):= E-(holdUp U (projectZero E)+bodyQ V K)
lemma deficit_green (v:Green f)(K:Matrix U U ℝ) : Green (deficit K f):= by
    refine ContDiffAt.sub (ContDiffAt.sub v ?_) (loomK_green _); exact ContDiffAt.comp (f:=rightArm) (g:=baseP f) 0 (by rw [rightZero]; exact immersed v) rightGreen
lemma faint_origin (K:Matrix U U ℝ)(u:E*X^2=jet f)(h:Green f): X^2*faintRest K E = jet (deficit K f):=by
    have he:=congr_arg projectZero u; rw [map_mul,map_pow,show projectZero (X:Ink (U⊕V))=X by simp [projectZero],projectBasis h] at he
    have ht:= liftBasis (U:=U) (immersed h); rw [←he] at ht; rw [map_mul,map_pow,hold_X'] at ht
    unfold deficit faintRest; rw [jet_sub (f:=f-(baseP f ∘ rightArm)) (by apply ContDiffAt.sub h; exact (immersed h).comp (f:=rightArm) 0 rightGreen) (loomK_green _),jet_sub h (g:=baseP f ∘ rightArm) (by exact (immersed h).comp (f:=rightArm) 0 rightGreen),flare,← ht,←u]; ring
set_option maxHeartbeats 600000 in
lemma funded {B:Ink V}(h:Fathom f θ E)(K:Matrix U U ℝ)(p:K.transpose=K)(hk:IsUnit K.det)(hc:constantCoeff E=constantCoeff (bodyQ V K+holdUp U B)) :
    let W:=retool θ E
    constantCoeff W=constantCoeff (bodyQ V K+holdUp U B) ∧ ∀ i, constantCoeff (spool θ i)=constantCoeff (noiseLine (1:Matrix U U ℝ) i):=by
    intro W
    have he:= h.shine
    let X₁:= projectZero W; let Q:= faintRest K W
    let f':=deficit K f
    have hf:= deficit_green h.sta K
    have hz : Muted 3 3 f':= by
       obtain ⟨a,b,c⟩:= sandbar h K p (k:=1) (fun i j v hv=>by
           interval_cases v; simp_rw [coeff_zero_eq_constantCoeff_apply]; unfold jPrint; simp only [of_apply,jet_lead,centerK K h p hc]; unfold realS; simp only [RingHom.coe_comp,Function.comp_apply, constantCoeff_C]; rw [← show K j i=K i j from congr_fun (congr_arg (fun M:Matrix U U ℝ=>M i) p) j])
       intro l v; cases l with
       | nil=> rw [List.map_nil,tapping,a]; exact Equal.refl _ _
       | cons i l=> cases l with
          | nil=> rw [List.map_cons,List.map_nil,tapping,tapping,sap hf,map_mul,b,mul_zero]; exact Equal.refl _ _
          | cons j l=> cases l with
              | nil=> rw [List.map_cons,List.map_cons,List.map_nil,tapping,tapping,tapping,sap hf,brush_X,sap (rubbed hf _),← mul_assoc,←pow_two,map_mul,map_pow,show projectZero (X:Ink (U⊕V))=X by simp [projectZero]]; exact (c _ _).turf 2
              | cons _ _=> simp at v; omega
    have hQ: constantCoeff Q=0:=by
       have hT:X^2*Q=jet f':=faint_origin K (by rw [mul_comm]; exact he) h.sta
       have h' := Dark.off (n:=1) (f:=Q) (Dark.came (by rw [hT]; exact hz.still hf)) (by omega:0<1); simpa only [coeff_zero_eq_constantCoeff_apply] using h'
    have hw:constantCoeff W = constantCoeff (bodyQ V K+holdUp U X₁):=by unfold Q faintRest at hQ; rw [map_sub,sub_eq_zero] at hQ; rw [add_comm]; exact hQ
    have hy : Equal 1 E (bodyQ V K+holdUp U B):= fun i p=> show coeff i E=coeff i (bodyQ V K+holdUp U B) from
          (by rw [show i=0 by omega]; simpa only [coeff_zero_eq_constantCoeff_apply])
    have ht : constantCoeff W=constantCoeff (reroll path (spool θ) (bodyQ V K)+holdUp U B):=by rw [← coeff_zero_eq_constantCoeff_apply, show reroll (path (U:=V)) (spool θ) (bodyQ V K)+ holdUp U B=retool θ (bodyQ V K+holdUp U B) from (by rw [map_add,retool_tall]; rfl),←coeff_zero_eq_constantCoeff_apply]; exact filtered (retire θ) hy 0 one_pos
    have hv:= strike_leading path θ h.θp h.θo K p hk (1:Matrix U U ℝ) h.ea.symm (by rw [Matrix.det_one]; exact isUnit_one) _ _ (hw.symm.trans ht)
    have hx:= local_zero_roll (1: Matrix U U ℝ) path hv.2 (show K=(1:Matrix U U ℝ).transpose*K*1 by simp)
    rw [map_sub,sub_eq_zero] at hx
    exact ⟨ht.trans (by rw [map_add,map_add,hx]),hv.2⟩
end YM.WilsonCoeffUV.Blue.Cameo
