import YM.SchemeRG11.Saddle.Heads
/-! Hard Landau (linear divergence slice) regulator path. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.SchemeRG11.Sway
open scoped Classical ContDiff Topology Matrix.Norms.Frobenius
open Function Filter Lattice Pert.Orb PertExtension.Orb LocalH MeasureTheory Precision Push.Loops
variable {G:Gauge}{n:Side}

def TransV (G:Gauge)(n:Side):Submodule ℝ (Potential G n):= LinearMap.ker dLin
abbrev Land(G:Gauge)(n:Side):= ↥(TransV G n)
abbrev g0(G:Gauge)(n:Side): Land G n →L[ℝ] Potential G n:= (TransV G n).subtypeL
abbrev divL(G:Gauge)(n:Side): Potential G n→L[ℝ] ↥(Flow G n):= (dLin (G:=G) (n:=n)).toContinuousLinearMap
abbrev along (G:Gauge)(n:Side):↥(Flow G n)→L[ℝ] Potential G n:= gZ.toContinuousLinearMap ∘L (spanLink G n).symm.toContinuousLinearMap
lemma div_trans (u:Land G n): divL G n u.val=0:=u.property
lemma div_along (h: ↥(Flow G n)): divL G n (along G n h)=h:= (spanLink G n).apply_symm_apply _
def projectL(G:Gauge)(n:Side): Potential G n→L[ℝ] Land G n :=
   
    ((ContinuousLinearMap.id ℝ _-(along G n).comp (divL G n)).codRestrict (TransV G n) (fun a=>by change divL G n (a-along G n ((divL G n) a))=0; rw [map_sub,div_along,sub_self]))
lemma projectL_coe (a:Potential G n): (projectL G n a).val=a-(along G n) (dLin a):=rfl
lemma projectL_mem(a:Potential G n)(ha:divL G n a=0): (projectL G n a).val=a:=by rw [projectL_coe,show dLin a=0 from ha,map_zero,sub_zero]

def transverse(G:Gauge)(n:Side): Potential G n≃L[ℝ]Land G n × ↥(Flow G n):=
 let L:= (projectL G n).prod (divL G n)
 let H:= (g0 G n).coprod (along G n)
 { L with
   toFun:=L
   invFun:=H
   left_inv:=fun a=>by
      change (projectL G n a).val+along G n (dLin a)=a; rw [projectL_coe,sub_add_cancel]
   right_inv:=fun p=>by
      rcases p with ⟨h,y⟩
      change (projectL _ _ (h.val+along _ _ y),divL _ _ _)=_
      have hi:divL G n (h.val+along G n y)=y:=by rw [map_add,div_trans,div_along,zero_add]
      exact Prod.ext (Subtype.ext (by change (projectL _ _ _).val=h.val; rw [projectL_coe,show dLin _=y from hi,add_sub_cancel_right])) hi
   continuous_invFun:= H.continuous }

def steeple(hp:Even n.val)(A:Dir G n): Land G n:= projectL _ _ (graze hp (A,0))
lemma steeple_smooth(hp:Even n.val): ContDiffAt ℝ ω (steeple (G:=G) hp) 0:=by
 let W:=ContinuousLinearMap.inl ℝ (Dir G n) ↥(Flow G n)
 let V:=projectL G n
 have h: ContDiffAt ℝ ω (graze hp ∘ W) 0:= ContDiffAt.comp (f:=W) 0 (by rw [map_zero]; exact graze_smooth G hp) W.contDiff.contDiffAt
 have hi: ContDiffAt ℝ ω (V ∘ (graze hp ∘ W)) 0:= ContDiffAt.comp _ (show ContDiffAt ℝ ω (fun a=>V a) _ from ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Potential G n) (F:=Land G n) V |>.contDiffAt) h
 exact hi
lemma steeple_flat(hp:Even n.val): steeple (G:=G) hp 0=0:=by rw [steeple,show graze hp ((0:Dir G n),0)=0 from graze_flat G hp,map_zero]
lemma steeple_eq(hp: Even n.val):∀ᶠ A:Dir G n in 𝓝 0,(steeple hp A).val= graze hp (A,0):= by
 have h:Tendsto (fun A:Dir G n=>(A,(0: ↥(Flow G n)))) (𝓝 0) (𝓝 0):=tendsto_id.prodMk_nhds tendsto_const_nhds
 filter_upwards [h.eventually (graze_div G hp)] with A hi; exact projectL_mem _ hi
lemma steeple_rate (hp:Even n.val):∀ᶠ A:Dir G n in 𝓝 0, let v:Whole G n:=(A,0)
      let L:Whole G n→L[ℝ]Land G n × ↥(Flow G n):=(transverse G n).toContinuousLinearMap ∘L fderiv ℝ (graze (G:=G) hp) v
      (∀ p:Whole G n,(L p).2=p.2) ∧ ∀ t:Dir G n, (L (t,0)).1= fderiv ℝ (steeple (G:=G) hp) A t:=by
 have h:Tendsto (fun A:Dir G n=>(A,(0: ↥(Flow G n)))) (𝓝 0) (𝓝 0):=tendsto_id.prodMk_nhds tendsto_const_nhds
 filter_upwards [h.eventually (down_rate hp),h.eventually ((graze_smooth G hp).eventually (by simp))] with A he hd
 intro v L; change (∀ _, _ ) ∧ _ at he -- infer?
 refine ⟨fun p=>he.1 p,fun t=>?_⟩
 let U:= ContinuousLinearMap.inl ℝ (Dir G n) ↥(Flow G n)
 have hm : fderiv ℝ (steeple (G:=G) hp) A= (ContinuousLinearMap.fst ℝ _ _) ∘L (L ∘L U):=by
    let S:=transverse G n
    have hv: HasFDerivAt (fun p=> S (graze hp p)) L (U A):=by
       exact (ContinuousLinearEquiv.hasFDerivAt (E:=Potential G n) (F:=Land G n × ↥(Flow G n)) S).comp (U A) (hd.differentiableAt (by simp)).hasFDerivAt
    let H := ContinuousLinearMap.fst ℝ (Land G n) ↥(Flow G n)
    have hu: HasFDerivAt ((fun p=> S (graze hp p)) ∘ U) (L ∘L U) A:= HasFDerivAt.comp (g:=fun p=> S (graze hp p)) A hv U.hasFDerivAt
    have hj: HasFDerivAt (fun p=> (S (graze hp (U p))).1) (H ∘L (L ∘L U)) A:=by
       exact (HasFDerivAt.comp (𝕜:=ℝ) (E:=Dir G n) (F:=Land G n × ↥(Flow G n)) (G:=Land G n) (f':=L ∘L U) (g':=H) (g:=Prod.fst (α:=Land G n) (β:= ↥(Flow G n))) (f:=(fun p=> S (graze hp p)) ∘ U) A (by exact ContinuousLinearMap.hasFDerivAt (𝕜:=ℝ) (E:=Land G n × ↥(Flow G n)) (F:=Land G n) H) hu)
    exact hj.fderiv
 rw [hm];rfl
lemma steeple_good (hn:Admissible n){hp:Even n.val}: (fderiv ℝ (steeple (G:=G) hp) 0).IsInvertible:=by
 let L:= (transverse G n).toContinuousLinearMap ∘L fderiv ℝ (graze (G:=G) hp) 0
 let k:= fderiv ℝ (steeple (G:=G) hp) 0
 obtain ⟨e,he⟩:=graze_good (G:=G) hn (hp:=hp)
 have hi:L=(e.trans (transverse G n)).toContinuousLinearMap:= by unfold L; rw [← he]; rfl
 have hv: Bijective L:=by rw [hi]; exact (e.trans _).bijective
 have ht:(∀ p:Whole G n,(L p).2=p.2) ∧ ∀ t:Dir G n,(L (t,0)).1=k t:=by
    exact mem_of_mem_nhds (s:={A:Dir G n| let v:Whole G n:=(A,0); let L:= (transverse G n).toContinuousLinearMap ∘L fderiv ℝ (graze (G:=G) hp) v;(∀ p:Whole G n,(L p).2=p.2) ∧ ∀ t:Dir G n, (L (t,0)).1= fderiv ℝ (steeple (G:=G) hp) A t}) (steeple_rate (G:=G) hp)
 have hb: Bijective k:=by
     have hU(A:Dir G n): L (A,0)=(k A,0):= Prod.ext (ht.2 A) (ht.1 (A,0))
     refine ⟨fun a b h=> congrArg Prod.fst (hv.1 ((hU a).trans (show _=L (b,0) from by rw [h,hU b]))),?_⟩
     intro b; obtain ⟨⟨a,t⟩,ha⟩:= hv.2 (b,0)
     have hq: t=0:=(ht.1 (a,t)).symm.trans (congrArg Prod.snd ha); rw [hq,hU] at ha; exact ⟨a,congrArg Prod.fst ha⟩
 let i: Dir G n ≃L[ℝ] Land G n:= LinearEquiv.toContinuousLinearEquiv (E:=Dir G n) (F:=Land G n) (LinearEquiv.ofBijective k.toLinearMap hb)
 refine ⟨i,?_⟩; apply ContinuousLinearMap.ext; intro t; rfl

def OuterCost(e:Dir G n≃L[ℝ] Land G n)(hp:Even n.val)(A:Dir G n):= cost (e.symm.toContinuousLinearMap ∘L fderiv ℝ (steeple (G:=G) hp) A)
lemma transfer_cost (hn:Admissible n){hp:Even n.val}(e:Dir G n≃L[ℝ] Land G n): ∃ C>0,∀ᶠ A:Dir G n in 𝓝 0,
   (Jacob (steeple hp A).val * FP (steeple hp A).val) * OuterCost e hp A=C * cost (submerge A):=by
 let P:= transverse G n; let Q:= packing G hp
 let R:= e.symm.prodCongr (ContinuousLinearEquiv.refl ℝ ↥(Flow G n)); let S:= Q.trans (P.trans R)
 let f(A:Dir G n): Whole G n:=(A,0)
 have ht:Tendsto f (𝓝 0) (𝓝 0):=tendsto_id.prodMk_nhds tendsto_const_nhds
 refine ⟨cost S.toContinuousLinearMap,cost_posit S,?_⟩
 filter_upwards [steeple_eq (G:=G) hp, steeple_rate (G:=G) hp, ht.eventually (graze_key hn (hp:=hp))] with A ha hm hc
 let L:= P.toContinuousLinearMap ∘L fderiv ℝ (graze (G:=G) hp) (f A)
 let V:= R.toContinuousLinearMap ∘L L
 have hv:V= S.toContinuousLinearMap ∘L (Q.symm.toContinuousLinearMap ∘L fderiv ℝ (graze (G:=G) hp) (f A)):=by
    apply ContinuousLinearMap.ext; intro i; change R (P (fderiv ℝ _ _ _))= R (P (Q (Q.symm _))); rw [Q.apply_symm_apply];rfl
 have hd: cost V= OuterCost e hp A:=by
    change (∀ p:Whole G n,(L p).2=p.2) ∧ _ at hm
    rw [cost_up V (e.symm.toContinuousLinearMap ∘L fderiv ℝ (steeple (G:=G) hp) A) (ContinuousLinearMap.id ℝ _) (fun x=>Prod.ext (congrArg e.symm (hm.2 x)) (hm.1 (x,0))) (fun y=>hm.1 (0,y)),cost_id,mul_one]; rfl
 rw [ha,← hd,hv,cost_com,mul_left_comm]; exact congrArg (cost S.toContinuousLinearMap*·) hc
lemma steeple_key(hn:Admissible n){hp:Even n.val}(e:Dir G n≃L[ℝ] Land G n)(he:e.toContinuousLinearMap=fderiv ℝ (steeple (G:=G) hp) 0): ∀ᶠ A:Dir G n in 𝓝 0,
   (Jacob (steeple hp A).val * FP (steeple hp A).val) * OuterCost e hp A= cost (submerge A):=by
 obtain ⟨C,hC,ht⟩:= transfer_cost hn (hp:=hp) e
 have hv: e.symm.toContinuousLinearMap ∘L fderiv ℝ (steeple (G:=G) hp) 0=ContinuousLinearMap.id ℝ (Dir G n):= by rw [← he]; ext1 t; exact e.symm_apply_apply _
 have hc:C=1:=by
    have hi:(Jacob (steeple hp 0).val*FP (steeple hp 0).val)*OuterCost e hp 0=C*cost (submerge (0:Dir G n)):=mem_of_mem_nhds (s:={A:Dir G n|(Jacob (steeple hp A).val*FP (steeple hp A).val)*OuterCost e hp A=C*cost (submerge A)}) ht
    simpa only [OuterCost,hv,cost_id,steeple_flat,Submodule.coe_zero,jacobian_flat,FP_flat,submerge_flat,mul_one] using hi.symm
 simpa only [hc,one_mul] using ht
end YM.SchemeRG11.Sway
