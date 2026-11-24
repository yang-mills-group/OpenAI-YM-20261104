import YM.SchemeRG11.Saddle.Wing
/-! Faddeev cost before any passing to a Leibniz or asymptotic series. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SchemeRG11.Sway
open scoped Classical ContDiff Topology Matrix.Norms.Frobenius
open Function Filter Lattice Pert.Orb PertExtension.Orb LocalH MeasureTheory Precision Push.Loops
variable {G:Gauge}{n:Side}

def TraceCost (hn:Even n.val)(x:Whole G n):= cost ((packing G hn).symm.toContinuousLinearMap ∘L fderiv ℝ (graze (G:=G) hn) x)
lemma vine_cost (hn:Admissible n){hp:Even n.val}: ∀ᶠ x:Whole G n in 𝓝 0,
    cost ((combine G hp).symm.toContinuousLinearMap ∘L vine hp x) = Jacob (graze hp x) * TraceCost hp x:=by
 have ht:Tendsto (graze (G:=G) hp) (𝓝 0) (𝓝 0):=Eq.subst (motive:=fun a=>Tendsto _ _ (𝓝 a)) (graze_flat G hp) (graze_smooth G hp).continuousAt.tendsto
 filter_upwards [ht.eventually (cost_road hn)] with x hx
 let a:= graze hp x; let s:=swing G hp x
 let L:= combine G hp; let V:= (packing G hp).symm.toContinuousLinearMap ∘L fderiv ℝ (graze (G:=G) hp) x
 have he: L.symm.toContinuousLinearMap ∘L vine hp x=(L.symm.toContinuousLinearMap ∘L (ravel s ∘L road a) ∘L L.toContinuousLinearMap) ∘L V :=by
    apply ContinuousLinearMap.ext; intro t
    let v:= fderiv ℝ (graze (G:=G) hp) x t
    change L.symm (ravel _ (road _ (twin hp v))) = L.symm (ravel s (road a (L (L.symm (twin hp v)))))
    rw [L.apply_symm_apply]
 rw [he,cost_com,show cost (L.symm.toContinuousLinearMap ∘L (ravel s ∘L road a) ∘L L.toContinuousLinearMap)=cost (ravel s ∘L road a) from cost_conj L.symm _,cost_com,cost_ravel,hx,one_mul]; rfl
lemma graze_key (hn:Admissible n){hp:Even n.val}: ∀ᶠ x:Whole G n in 𝓝 0, (Jacob (graze hp x) * FP (graze hp x)) * TraceCost hp x= cost (submerge x.1):=by
 have ht:Tendsto (graze (G:=G) hp) (𝓝 0) (𝓝 0):=Eq.subst (motive:=fun a=>Tendsto _ _ (𝓝 a)) (graze_flat G hp) (graze_smooth G hp).continuousAt.tendsto
 filter_upwards [vine_cost hn (hp:=hp),valve_rate (G:=G) hp, ht.eventually coat_cost] with x hx hi hc
 let a:=graze hp x; let s:=swing G hp x
 let V:= vine hp x; let R:=stream hp x; let W:=spanLink G n
 change (∀ h, FPDeriv a (R ((0:Dir G n),h))=_) ∧ _ at hi
 let j: ↥(Flow G n)→L[ℝ]Parameter G n:=R ∘L ContinuousLinearMap.inr ℝ (Dir G n) ↥(Flow G n)
 let b:= FPDeriv a; let Z:= b ∘L (R ∘L ContinuousLinearMap.inl ℝ _ _)
 let L:=j ∘L W.toContinuousLinearMap; let P: Parameter G n→L[ℝ] Parameter G n:= resetFP a
 have he : P ∘L L =ContinuousLinearMap.id ℝ (Parameter G n):=by
    ext1 v; change W.symm (FPDeriv a (R (0,W v)))=v; rw [hi.1,W.symm_apply_apply]
 have h0: FP a * cost L=1:=by rw [← hc,← cost_com, he,cost_id]
 have hP: Injective P:=(LinearMap.injective_iff_surjective (f:=P.toLinearMap)).2 (fun u=>⟨L u,DFunLike.congr_fun he u⟩)
 have hR(t: Whole G n): R (t.1,0)= j (Z t.1):= hP <| by change W.symm (Z t.1)= W.symm (FPDeriv a (R (0,Z t.1))); rw [hi.1]
 let H:Whole G n→L[ℝ]Whole G n:= (ContinuousLinearMap.fst ℝ _ _).prod (ContinuousLinearMap.snd ℝ _ _-Z ∘L ContinuousLinearMap.fst ℝ _ _)
 have hH(p:Whole G n): H p=(p.1,p.2-Z p.1):=rfl
 let Y: Whole G n→L[ℝ]Whole G n:= (combine G hp).symm.toContinuousLinearMap ∘L V
 have ht': cost H=1:=by
    rw [cost_down H (ContinuousLinearMap.id ℝ (Dir G n)) (ContinuousLinearMap.id ℝ ↥(Flow G n)) (fun z=> rfl) (fun v=>by rw [hH]; change ((0:Dir G n),v-Z 0)=_; rw [map_zero,sub_zero];rfl),cost_id,cost_id,mul_one]
 have hi' (p:Whole G n): (Y p).2= W (undress s (R p)):=by
    change (crest G hp).symm (vine hp x p).2=W _
    rw [(hi.2 p).1]; change W ((stem hp).symm (stem hp _))= _; rw [ContinuousLinearEquiv.symm_apply_apply]
 let M:= W.toContinuousLinearMap ∘L (undress s ∘L L) ∘L W.symm.toContinuousLinearMap
 have hd: cost Y= cost (submerge x.1) * cost L:= calc
    cost Y=cost (Y ∘L H):=by rw [cost_com, ht',mul_one]
    _=cost (submerge x.1) *cost M:=by
      apply cost_up
      · intro z; let p:Whole G n:=(z,0)
        have hz: H p=(z,-Z z):=by rw [hH]; simp [p]
        have hv: R (H p) = 0:=by
           rw [hz,show (z,-Z z)=p-(0,Z z) by simp [p],map_sub]; exact sub_eq_zero.mpr (hR p)
        refine Prod.ext ?_ ?_
        · ext1 i; change (vine hp x (H p)).1 i =submerge x.1 z i
          rw [(hi.2 _).2 i]; change submerge x.1 z _+ (undress s (R (H p))).val _ - G.adjoint _ ((undress s (R (H p))).val _)=_; rw [hv]; simp
        change (Y (H p)).2=0;rw [hi',hv]; simp
      intro v
      change (Y (H (0,v))).2=M v; rw [hi',hH]; change W (undress _ (R (0,v-Z 0)))= W (undress _ (j (W (W.symm v)))); rw [map_zero,sub_zero,W.apply_symm_apply];rfl
    _=_:=by rw [show cost M= cost (undress s ∘L L) from cost_conj W (undress s ∘L L),cost_com,cost_undress,one_mul]
 calc
    _= FP a * cost Y:=by rw [show cost Y=_ from hx]; ring
    _=_:=by rw [hd,mul_left_comm,h0,mul_one]
lemma graze_good (hn:Admissible n){hp:Even n.val}: (fderiv ℝ (graze (G:=G) hp) 0).IsInvertible:=by
 let L:=fderiv ℝ (graze (G:=G) hp) 0
 have h:= graze_key (G:=G) hn (hp:=hp)
 have he: cost ((packing G hp).symm.toContinuousLinearMap ∘L L)=1:=by
    have hv: _= _:= mem_of_mem_nhds (s:={x:Whole G n|(Jacob (graze hp x)*FP (graze hp x))*TraceCost hp x= cost (submerge x.1)}) h
    change (Jacob (graze hp (0:Whole G n))*FP (graze hp (0:Whole G n)))* TraceCost hp (0:Whole G n)=cost (submerge (0:Dir G n)) at hv
    rw [graze_flat, jacobian_flat, FP_flat,one_mul,one_mul, submerge_flat] at hv; exact hv
 obtain ⟨e,hm⟩:= cost_iso _ (he.trans_ne one_ne_zero)
 refine ⟨e.trans (packing G hp),?_⟩
 apply ContinuousLinearMap.ext; intro p; change packing G hp (e p)= L p
 rw [show e p=(packing G hp).symm (L p) from DFunLike.congr_fun hm p, ContinuousLinearEquiv.apply_symm_apply]

end YM.SchemeRG11.Sway
