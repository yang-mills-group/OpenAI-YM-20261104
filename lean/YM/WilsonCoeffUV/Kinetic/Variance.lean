import YM.WilsonCoeffUV.Kinetic.Saddle
/-!
# Recenter axis and tails; actual saddle slice rather than arbitrary df
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue.Cameo
open Matrix Function PowerSeries Filter
open scoped Topology ContDiff BigOperators
variable {U V : Type} [Fintype U][DecidableEq U][Fintype V][DecidableEq V]
variable {f g : Lawn (U ⊕ V)→ℝ}{M:Lawn V→Matrix U U ℝ}
variable {K:Matrix U U ℝ}

-- calculus helper

def barL (i:Lawn V)(u:Lawn U) : Lawn (U⊕V):=Sum.elim u i
def dotCL : Lawn U→L[ℝ]Lawn (U⊕V):= LinearMap.pi (Sum.elim (fun i:U=>LinearMap.proj (R:=ℝ) (φ:=fun _=>ℝ) i) (fun _:V=>0))|>.toContinuousLinearMap
omit [DecidableEq U] [Fintype V] [DecidableEq V] in
lemma edge_bar (i:Lawn V)(u:Lawn U): barL i u= dotCL u + piIn i:=by funext j; cases j with
                                                                           | inl j=> change u j=u j+0; simp
                                                                           | inr j=> change i j=0+i j; simp
omit [DecidableEq U] [DecidableEq V] in
lemma edge_has (x:Lawn V): ContDiff ℝ ω (barL (U:=U) x) := by simp_rw [funext (edge_bar x)]; exact ((dotCL (U:=U) (V:=V)).contDiff).add contDiff_const
omit [Fintype V] [DecidableEq V] in
lemma edge_site (i:U) : dotCL (V:=V) (pebble i)= pebble (.inl i):=by
    funext v; cases v with
    | inl v=> change pebble i v= _; by_cases he:v=i; subst v; simp [pebble]
              simp [pebble,he]
    | inr v=> change 0=_; simp [pebble]
omit [DecidableEq V] in
lemma edge_snap (x:Lawn V)(i:U)(v:Lawn U)(h:DifferentiableAt ℝ f (barL x v)) : rub (f ∘ barL x) i v = rub f (.inl i) (barL x v) := by
    have hx:fderiv ℝ (barL x) v=dotCL:= by rw [funext (edge_bar x)]; exact ((dotCL (U:=U) (V:=V)).hasFDerivAt.add_const _).fderiv
    rw [rub,fderiv_comp v h ((edge_has x).differentiable (by simp) v),hx]; exact (congr_arg (fderiv ℝ _ _) (edge_site i))
omit [DecidableEq V] in
lemma rubble (x:Lawn V)(i j:U)(h:ContDiffAt ℝ ω f (piIn x)): sandH f x i j= iteratedFDeriv ℝ 2 (f ∘ barL x) 0 ![pebble i,pebble j] :=by
    have hy:ContDiffAt ℝ ω (rub f (.inl j)) (piIn x):= ContDiffAt.comp (f:=fderiv ℝ f) _ ((ContinuousLinearMap.apply ℝ ℝ (pebble (.inl j : U⊕V))).contDiff.contDiffAt) (h.fderiv_right (by simp))
    rw [sandH,Matrix.of_apply,baseP,Function.comp_apply, ← show barL x (0:Lawn U)=piIn x from rfl, ← edge_snap x i (0:Lawn U) (hy.differentiableAt (by simp))]
    have hg:= (show ContDiffAt ℝ ω (f∘barL x) (0:Lawn U) from h.comp (f:=barL x) 0 ((edge_has x).contDiffAt))
    let v:Lawn U→ℝ:= f ∘ barL x
    have he := (edge_has (U:=U) x).continuous.tendsto 0
    have hu : (rub f (.inl j) ∘ barL x)=ᶠ[𝓝 0] rub v j:= (he.eventually (show _ from h.eventually (by simp))).mono (fun u hu=> (edge_snap x j u (hu.differentiableAt (by simp))).symm)
    let p:= ContinuousLinearMap.apply ℝ ℝ (pebble j)
    change fderiv ℝ (rub f (.inl j) ∘ barL x) 0 _= _; rw [hu.fderiv_eq]
    rw [show rub v j=p ∘ fderiv ℝ v from rfl,fderiv_comp 0 p.differentiableAt ((ContDiffAt.fderiv_right (m:=ω) (f:=v) hg (by simp)).differentiableAt (by simp)), p.fderiv]; rw [iteratedFDeriv_two_apply]; rfl
lemma sand_sym (p:Green f): ∀ᶠ v:Lawn V in 𝓝 0,(sandH f v).transpose=sandH f v:=by
    have he:= immersion (U:=U) (V:=V)|>.continuousAt.tendsto
    rw [show piIn (U:=U) (0:Lawn V)=0 from funext fun i=>by cases i<;>rfl] at he
    filter_upwards [he.eventually (p.eventually (by simp))] with v hv
    have ht:Green (f ∘ barL v):=hv.comp (f:=barL v) 0 ((edge_has v).contDiffAt)
    ext1 i j; rw [Matrix.transpose_apply, rubble v j i hv,rubble v i j hv]; apply Work.F03.hessian_symmetric (ht.of_le (by simp))
lemma sand_green (h:Green f): MGreen (sandH f):= fun i j=> immersed (rubbed (rubbed h (.inl j)) (.inl i))
-- whiten

def caulk (M:Lawn V→Matrix U U ℝ)(x:Lawn (U⊕V)):= M (rightArm x)*ᵥ leftArm x
omit [DecidableEq U] [Fintype V] [DecidableEq V] in
lemma caulk_zero (M:Lawn V→Matrix U U ℝ):caulk M 0=0:= by unfold caulk; rw [leftZero,Matrix.mulVec_zero]
lemma caulkG (h:MGreen M): Green (caulk M):= by
    let J:= Lawn (U⊕V)
    apply contDiffAt_pi.mpr; intro i; unfold caulk Matrix.mulVec dotProduct; apply ContDiffAt.sum; intro j _
    exact ((h i j).comp (f:=rightArm) 0 (rightGreen (X:=U) (Y:=V))).mul ((contDiffAt_apply ℝ ℝ j 0).comp 0 leftGreen)
omit [DecidableEq U] [Fintype V] [DecidableEq V] in
lemma caul_bar (p:Lawn U)(w:Lawn V)(M:Lawn V→Matrix U U ℝ): spider (caulk M) (barL w p) = barL w (M w*ᵥ p):= rfl
omit [DecidableEq U] [Fintype V] [DecidableEq V] in
lemma caul_spin (M:Lawn V→Matrix U U ℝ)(w:Lawn V) : spider (caulk M) (piIn w)= piIn w:=by rw [show piIn w=barL w (0:Lawn U) from rfl,caul_bar, Matrix.mulVec_zero]
lemma caul_d (h:MGreen M)(p:M 0=1): edgeM (caulk M) 0=1:=by
    rw [edge_fder _ 0 ((caulkG h).differentiableAt (by simp))]; rw [show (fun s=>caulk M (Sum.elim s (rightArm (0:Lawn (U⊕V)))))=id from funext fun s=> by change M (rightArm (Sum.elim s _))*ᵥ s= s; change M 0*ᵥ s= s; rw [p,Matrix.one_mulVec],fderiv_id]; exact LinearMap.toMatrix'_id
lemma caul_fee (g:MGreen M): ∀ᶠ x in 𝓝 0,(edgeM (caulk M) x).det=(M (rightArm x)).det:=by
    filter_upwards [(caulkG g).eventually (by simp)] with x hx
    rw [edge_fder _ x (hx.differentiableAt (by simp))]
    let R:=M (rightArm x)
    let L:= LinearMap.toContinuousLinearMap (Matrix.mulVecLin R)
    rw [show (fun s=>caulk M (Sum.elim s (rightArm x)))=L from rfl, L.fderiv]; congr 1; ext1 i j; rw [LinearMap.toMatrix'_apply]; change dotProduct (R i) (Pi.single j 1) = R i j; rw [dotProduct_single, mul_one]
-- derivatives for twisted variation. no constant perturbation
lemma sailM_green (h: MGreen M)(p:Green f) : Green (f ∘ spider (caulk M)) := by
    refine (ContDiffAt.comp 0 ?_ (spider_green (caulkG h))); rw [spider_zero (caulk_zero _)]; exact p
lemma lights_c (h:Green f)(i:U)(g:MGreen M): ∀ᶠ w:Lawn V in 𝓝 0, avenue (f ∘ spider (caulk M)) i w = ∑ j: U,M w j i * avenue f j w:=by
    have he:=immersion (U:=U) (V:=V)|>.continuousAt.tendsto; rw [show piIn (U:=U) (0:Lawn V)=0 from funext fun i=>by cases i <;>rfl] at he
    filter_upwards [he.eventually (h.eventually (by simp)),he.eventually ((sailM_green g h).eventually (by simp))] with w hf hx
    set f':=f∘barL w; set R:=M w; let L:= R.mulVecLin.toContinuousLinearMap
    have hh : ContDiffAt ℝ ω f' 0:= hf.comp (f:=barL w) 0 ((edge_has w).contDiffAt)
    rw [show avenue _ i w = rub ((f∘spider (caulk M))∘barL w) i 0 from (edge_snap w i 0 (hx.differentiableAt (by simp))).symm,show (f∘_)∘ barL w=f' ∘ L from rfl]
    rw [rub,fderiv_comp 0 (f:=L) (by rw [map_zero];exact hh.differentiableAt (by simp)) L.differentiableAt, L.fderiv,ContinuousLinearMap.comp_apply,map_zero];
    rw [redeploy (L (pebble i)), map_sum]; apply Finset.sum_congr rfl; intro j _; rw [map_smul]; change (L (pebble i)) j*rub f' j 0=_; rw [edge_snap (f:=f) w j 0 (hf.differentiableAt (by simp))];
    have he : (L (pebble i)) j=M w j i:=by
        change dotProduct (R j) (pebble i)= R j i; rw [show pebble i=Pi.single i 1 by ext a; by_cases h:i=a<;>simp_all [pebble,eq_comm],dotProduct_single,mul_one]
    rw [he]; rfl
lemma sailH (h:Green f)(p:MGreen M): ∀ᶠ x:Lawn V in 𝓝 0,sandH (f ∘ spider (caulk M)) x=(M x).transpose*sandH f x*M x:=by
    have he:=immersion (U:=U) (V:=V)|>.continuousAt.tendsto; rw [show piIn (U:=U) (0:Lawn V)=0 from funext fun i=>by cases i <;>rfl] at he
    filter_upwards [he.eventually (h.eventually (by simp)),he.eventually ((sailM_green p h).eventually (by simp))] with w hf hx
    let R:=M w; let L:= R.mulVecLin.toContinuousLinearMap
    have hg:Green (f ∘ barL w):=hf.comp (f:=barL w) 0 ((edge_has w).contDiffAt)
    let H:=iteratedFDeriv ℝ 2 (f ∘ barL w) 0
    have ht (i:U) (k): L (pebble i) k =M w k i := by
        change dotProduct (R k) (pebble i)= R k i
        rw [show pebble i=Pi.single i 1 by funext j; by_cases h:i=j<;>simp [pebble,eq_comm, *],dotProduct_single, mul_one]
    ext1 i j
    rw [rubble w i j hx,show (f∘_)∘ barL w=(f ∘ barL w) ∘ L from rfl, Stationary.wired L ?_, map_zero]; swap; · rw [map_zero]; exact hg.analyticAt
    have hK: L ∘ ![pebble i,pebble j] = ![L (pebble i),L (pebble j)]:= by ext l; fin_cases l <;>rfl
    rw [hK]
    let W (v:Fin 2)(u:U):=(L ((![pebble i,pebble j]:Fin 2→ Lawn U) v)) u • pebble u
    change H _=_
    have hp: ![L (pebble i), L (pebble j)]=(fun v=> ∑ u:U, W v u):= by ext1 v; fin_cases v; exacts [redeploy (L (pebble i)), redeploy (L (pebble j))]
    rw [hp,show H (fun v=>∑ i:U,W v i)= ∑ x:Fin 2→U,H (fun v=> W v (x v)) from H.toMultilinearMap.map_sum W]
    -- coercion
    rw [← Equiv.sum_comp (finTwoArrowEquiv U).symm, Fintype.sum_prod_type]; simp_rw [Matrix.mul_apply, Finset.sum_mul,transpose_apply,rubble _ _ _ hf]
    conv_rhs=> rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _=> Finset.sum_congr rfl fun t _=>?_
    let a:= (finTwoArrowEquiv U).symm (u,t)
    change H (fun i=>W i (a i)) = _ * H _ * _
    unfold W; rw [H.map_smul_univ]; rw [Fin.prod_univ_two]
    have hb:a 0=u:=rfl; have hh:a 1=t:=rfl
    rw [hb,hh];
    simp only [smul_eq_mul, Matrix.cons_val_zero,Matrix.cons_val_one,ht]
    rw [show (fun v=>pebble (a v))= ![pebble u,pebble t] from funext (fun i=> by fin_cases i<;>rfl)]; ring

lemma polarized (v:Green f)(p:∀ i,jet (avenue f i)=0)(h:MGreen M): ∀ i, jet (avenue (f ∘ spider (caulk M)) i)=0:=by
    intro i
    rw [jet_congr (lights_c v i h), show (fun x=>∑ j,M x j i *avenue f j x)=∑ j,(fun x=>M x j i)*avenue f j from funext fun v=> by rw [Finset.sum_apply]; rfl,jet_sum _ (fun j=>(fun x=>M x j i)*avenue f j) (fun j _=> (h j i).mul (immersed (rubbed v _)))]
    exact Finset.sum_eq_zero fun j _=>by rw [jet_mul (f:=fun x=>M x j i) (g:=avenue f j) (h j i) (immersed (rubbed v _)), p, mul_zero]

abbrev caulH (K:Matrix U U ℝ)(f:Lawn (U⊕V)→ℝ):= caulk (polarH K (sandH f))
variable {θ:Lawn (U⊕V)→Lawn U}{E:Ink (U⊕V)}{B:Ink V}
lemma fathomed (h:Fathom f θ E)(p:sandH f 0=K):
    Fathom (f ∘ spider (caulH K f)) (caulH K f) (retool θ E):=by
    let M:= polarH K (sandH f); have hp:=polar_green K (sand_green h.sta)
    refine ⟨caulk_zero _,caulkG hp,caul_d hp (polar_one p),sailM_green hp h.sta,polarized h.sta h.snap hp,?_⟩
    have he := traveling _ (spider_green (caulkG hp)) (spider_zero (caulk_zero _)) f h.sta
    rw [← he,← pivot]; rw [← h.shine]
    rw [map_mul,map_pow, show retool (caulk (polarH K (sandH f))) X=X from train_X _]
set_option maxHeartbeats 700000 in
lemma fath_mask {K:Matrix U U ℝ}(h:Fathom f θ E)(p:sandH f 0=K)(hK:IsUnit K.det): let a:= caulH K f; let v:=spider a; let W:= retool a (retool θ E)
    Muted 3 5 (deficit K (f ∘ v)) ∧ BrushGrade (faintRest K W):=by
    intro a v W
    let h':=fathomed h p
    have hp:= polar_green K (sand_green h.sta)
    have ht : K.transpose=K:=p ▸ (sand_sym h.sta).self_of_nhds
    have hz i j : Equal 3 (jPrint (sandH (f ∘ v)) i j) (realS (K j i)):=by
        have hh : jPrint (sandH (f ∘ v))= jPrint (fun x=>(polarH K (sandH f) x).transpose*sandH f x*polarH K (sandH f) x):= by
           ext1 i j; exact jet_congr ((sailH h.sta hp).mono (fun w h=>show sandH (f ∘ v) w i j= _ from congr_fun (congr_arg (fun M:Matrix U U ℝ=> M i) h) j))
        rw [hh, show K j i=K i j from congr_fun (congr_arg (fun M:Matrix U U ℝ=>M i) ht) j,← show jPrint (fun _:Lawn V=>K) i j=realS (K i j) from jet_const _]
        exact polar_image _ _ (sand_green h.sta) p (sand_sym h.sta) hK i j
    let F':= f ∘ v; let Y:= deficit K F'; have H:Green F':= h'.sta; have he:=deficit_green H K
    obtain ⟨c,d,u⟩:= sandbar h' K ht hz
    have hw:= plateau Y he (by change Dark 5 (projectZero (jet (deficit K (f ∘ spider (caulH K f))))); rw [c]; exact Equal.refl _ _) (fun i=> by rw [d]; exact Equal.refl _ _) u
    exact ⟨hw, BrushGrade.tar _ he hw (faint_origin K (by rw [mul_comm]; exact h'.shine) H) ⟩
end YM.WilsonCoeffUV.Blue.Cameo
