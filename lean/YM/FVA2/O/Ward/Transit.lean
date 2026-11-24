import YM.FVA2.O.Ward.Charge
/-! The combined differential (free and interaction tree). Adapted using Heat.Trees. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Ward
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat
variable {R A P : Type} [AddCommGroup P] [CommRing R][Fintype A]{p:Sector A}
variable {K:Flux A P R}{F H:Row A P R}(Z:Charge p P R){B:Raw A R}
lemma mutualJ [IsAddTorsionFree R] {V:Row A P R}(h:closed K p true)(hf:Symm (field p) F)(hh:Pure (field p) false F)(hv:Symm (field p) V)(ht:Pure (field p) false V)(hC:Conserved F)(hq:Conserved V) (hH:Symm (field p) H) : tree p K F (tree p K V H) + tree p K V (tree p K F H) + tree p K (tree p K F V) H=0:= by
    ext l
    let s:=atTop (α:= Finset P); have hr (F H V:Row A P R) (K L:Flux A P R): ∀ᶠ i in s, tree p (trim i K) F (tree p (trim i L) H V) l=tree p K F (tree p L H V) l∧ tree p (trim i K) (tree p (trim i L) F H) V l=tree p K (tree p L F H) V l:= by
        exact (event_tree (p:=p) (f:=fun _=>F) (g:=fun i=>tree p (trim i L) H V) (s:=s) (fun _=>by simp) (roll_tree p H V L) (fun a b i=> trims i a b) l).and (event_tree (p:=p) (g:=fun _=>V) (f:=fun i=>tree p (trim i L) F H) (fun _=>roll_tree ..) (fun _=>by simp) (fun a b i=>trims i a b) l)
    obtain ⟨i,h1,h2⟩:= ((hr F V H K K).and (hr V F H K K)).exists
    have hm := ((cl_trim i h).balanced i).mix_j hh ht hf hv hH; simp_rw [← is_loop, ← stickT h i hC, ←stickT h i hq,← stickT h i (conserved_tree _ _ hq F)] at hm;
    simp only [Pi.add_apply]; rw [←h1.1,←h2.1,←h1.2]; exact congr_fun hm l
lemma crossSelf [IsAddTorsionFree R]{V:Row A P R}(h:closed K p true)(hf:Symm (field p) F)(hh:Pure (field p) false F)(hv:Symm (field p) V)(ht:Pure (field p) false V)(hH:Symm (field p) H) : tree p K F (tree p K V H) + tree p K V (tree p K F H) + tree p K (tree p K F V) H=0:= by
   have hm:= mutualJ h (sym_trans hf) (pure_trans hh) (sym_trans hv) (pure_trans ht) (trans_off F) (trans_off V) hH
   rw [tree_agrees K p _ _ H (treesa K F V)] at hm; simpa only [tree_trans] using hm
-- signs coming from action on first slot
lemma sameCharge {A R:Type}[CommRing R]{p:Sector A}{f g:Raw A R}{K:Op A R} (T:Shift R p true)(he:∀ g,T.Q (K g)= - K (T.Q g))(hf:Pure p false f)(hp:Pure p true (K f)):
    T.Q (link K true p f g)= -(link K true p f (T.Q g)) - link K true p (T.Q f) g:= by
    have hv:=he (product p f g); rw [link_even K hf (b:=true),T.product_rule] at hv -- arg
    have hq: Pure p true (T.Q f):= T.pure hf
    simp only [map_add,T.product_rule,hf.signs,hp.signs,cross_false',cross_true,neg_smul,one_smul] at hv
    rw [link_apply K (T.Q f) g (b:=true),hq.signs,link_even K hf (b:=true),he,he] at hv
    simp only [cross_true,neg_smul, one_smul,map_neg,LinearMap.neg_apply] at hv; linear_combination (norm:=abel) hv
-- work without requiring a zero of the FLUX-level symbol (`change`).
-- There is enough if trc-operation on each momentum anticommutes; no regroup or symmetric assumption needed below.
lemma trim_Z {s:Finset P}(t:P)(h:∀ (q:P) (F:Row A P R), Z.raise (trc K q F) = - trc K q (Z.raise F)):
    Z.raise (trc (trim s K) t F) = - trc (trim s K) t (Z.raise F) := by
   by_cases hw:t∈s
   · have h1: trc (trim s K) t=trc K t:= by unfold trim trc; simp_rw [ if_pos hw ] -- lint
     rw [h1,h]
   have h1:trc (trim s K) t=0:= by unfold trim trc; simp only [if_neg hw, zero_smul,Finset.sum_const_zero]
   simp [h1]
lemma slab_Z (s:Finset P)(h:∀ (q:P) (F:Row A P R), Z.raise (trc K q F) = - trc K q (Z.raise F)):
    Z.raise (slab (trim s K) s F) = - slab (trim s K) s (Z.raise F) := by
    simp only [slab,map_sum,LinearMap.sum_apply]; simp_rw [trim_Z Z _ h,Finset.sum_neg_distrib]; -- fail_if_unchanged
lemma stick_Z (hc:Conserved F)(hf:Pure (field p) false F)(hp:closed K p true)(h:∀ (q:P) (F:Row A P R), Z.raise (trc K q F) = - trc K q (Z.raise F)) : Z.raise (tree p K F H) = - tree p K F (Z.raise H) - tree p K (Z.raise F) H := by
    ext l
    obtain ⟨s,hs,hL,hR⟩:= ((eventQ (Z:=Z) (roll_tree p F H K) l).and ((roll_tree p F (Z.raise H) K l).and (roll_tree p (Z.raise F) H K l))).exists
    simp only [Pi.sub_apply,Pi.neg_apply]; rw [←hs,←hL,←hR, stickT hp s hc,stickT hp s hc,stickT hp s (Z.conserve F hc)]; exact congr_fun (sameCharge Z.move (fun _=> slab_Z Z s h) hf ( (cl_trim s hp).pure s hf )) l
lemma slide_Z (hf:Pure (field p) false F)(hp:closed K p true)(h:∀ (q:P) (F:Row A P R), Z.raise (trc K q F) = - trc K q (Z.raise F)) : Z.raise (tree p K F H) = - tree p K F (Z.raise H) - tree p K (Z.raise F) H := by
    have hm := stick_Z Z (H:=H) (trans_off F) (pure_trans hf) hp h; rw [tree_trans,tree_trans,tree_agrees K p _ _ H (q_trans (F:=F))] at hm; exact hm
lemma pass_Z {K:Flux A P ℂ}{F:Row A P ℂ}[MeasurableSpace P] (Z:Charge p P ℂ)
    (h:∀ (q:P) (F:Row A P ℂ), Z.raise (trc K q F) = - trc K q (Z.raise F)) (μ:Measure P)(hp:Pass K F μ): Z.raise (Ccy K F μ) = - Ccy K (Z.raise F) μ := by
   ext l; rw [(cycle_map μ _ (sense_Q Z) l hp).2]; simp only [Pi.neg_apply, Ccy]; simp_rw [h]; exact integral_neg _ -- pi
end YM.FVA2.O.Ward
