import YM.Contacts.Sentry.Particle
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Sensor
open Function Set Filter MeasureTheory Extraction Lattice Cells Word Wilson Costar Bid Next.Phase
open Analysis Table Org Spec
open scoped Topology BigOperators ContDiff
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{V:Table C.book}(X:Final C F V)(hp:Grill C F)(v:Viewer X)
variable {b k l t q N p:ℕ} {ι J:Type}[Fintype ι][DecidableEq ι]
  (u:ι)(w:ι→ C.book.Token)(y:ι→ Cover)(x:ι→ E4)(B:ι→ℝ)
def extras (u:ι):= Finset.univ.erase u
structure Blanket (b l:ℝ):Prop where
    side : ∀ i,i≠u→ b< ‖x i-x u‖
    cost : ∀ i j,i≠ j → l< ‖x i-x j‖
-- definition binder x order? included u via side only

variable (hb:b≤k)(hl:k≤l)(ht:l≤t)(hh: 8*C.S.a k < C.S.a b)
  (hL: (6* ↑(extras u).card :ℝ)*C.S.a t < C.S.a l)
  (hB0:∀ i,0≤B i)(hB:F.late (Single C (w u) (B u) k)) (hs:∀ i,i≠u→ F.late (Single C (w i) (B i) t))
include hp hb hl ht hh hL hB hB0 hs
lemma budget_grid (hz:b≤q)(hy:y u=0)(hx:clear ι (C.S.gridPoint q∘y))(hf: Blanket u (C.S.gridPoint q∘y) (2*C.S.a b) (2*C.S.a l)) : ‖sample (watches X v) (C.S.gridPoint q∘y) w‖ ≤ ∏ i,B i:= by
   let I := extras u
   let p i (x:i∈extras u):= (⟨i,x⟩: I)
   let β : Ballot C q F.fuse := @Ballot.mk _ _ _ _ ι _ y (MatchToken.stays ∘ w) hx 1
   let E (_:Fin 1) := β
   have hq (i:I):i.val ≠ u:= Finset.ne_of_mem_erase i.property
   have he (i:I):2*C.S.a b<‖C.S.gridPoint q (y i)‖:=by have h:=hf.side _ (hq i); simp_rw [comp_apply,hy,zero_grid,sub_zero] at h; exact h
   let K':= watches X v; let a i:= w ((i:I):ι)
   have hR : ‖∑ i,(E i).observe K'‖ ≤ (B u)*∏ i:I,B i.val:= by
       refine stands (J:=I) E le_rfl X hp v hz (hb.trans hl) ht a (fun i=> y i.val) (fun i=> B i.val) (hB0 _) (fun _=> hB0 _) he (fun i j h=>hf.cost i.val j.val (Subtype.val_injective.ne h)) (fun i=>hs _ (hq i)) ?_
       filter_upwards [ (show ∀ᶠ c in F.fuse,Single C (w u) _ k c.1 c.2 from hB), Next.UVStress.large_mesh F q, Next.UVStress.large_mesh F t] with c hQ he hh'
       let f i:= C.seen (N:=c.1) (p:=c.2) -- arg spaces!
         (w i) (location C.S q c.1 c.2 (y i)); let g (i:I):= location C.S q c.1 c.2 (y i.val); let j:= Fintype.equivFin ↥I
       have hK : (6*(Fintype.card I):ℝ)*C.S.a t < C.S.a l:= by simpa only [I,Fintype.card_coe] using hL
       obtain ⟨o,hD,hZ⟩:= allocates C hb hl ht hh' (g ∘ j.symm) hh hK
       have hv' : k≤c.1:= (hl.trans ht).trans hh'; let T:= (center C.S c.2 (hb.trans hv') 0).newly o
       have he' : f u=C.seen (w u) (0:Site (C.side c.1 c.2)):= by unfold f; rw [hy,location_zero]
       obtain ⟨Z,hY,hI,hP⟩:= Lease.alive (T:=T) X.room.cutoff (0:Fin 1) 0 (show Around.imageBudget (fun _:Fin 1=>w u) (B u) k c.1 c.2 from hQ) hv' (Around.inherits (C:=C) hb hv') (z:=0) hD
       rw [show T.copy 0 Z=Z from (funext fun U=> T.copy_zero Z U)] at hY
       have hY:f u= Z:= he'.trans hY.symm
       refine ⟨o,Z,he,hh',hD.1,hI,hP,fun i=> ?_,?_⟩
       · specialize hZ (j i); simp_rw [comp_apply,j.symm_apply_apply] at hZ; exact hZ
       rw [Fin.sum_univ_one]; ext1 U; unfold E Ballot.vote; dsimp only [β,Ballot.u, Ballot.s, Ballot.weight, Function.comp_apply]; rw [one_mul]; change (∏ i,f i U)= Z U* ∏ i:I, f i U
       rw [← hY,← Finset.prod_subtype I (p:=fun i=> i∈I) (fun _=> Iff.rfl) (fun i=>f i U)]; exact (Finset.mul_prod_erase _ _ (Finset.mem_univ u)).symm -- order
   rw [Fin.sum_univ_one] at hR; unfold E Ballot.observe at hR; dsimp only [β] at hR; rw [one_mul] at hR
   apply hR.trans_eq; rw [← Finset.prod_subtype I (p:=(·∈I)) (fun _=> Iff.rfl) B]
   exact Finset.mul_prod_erase Finset.univ B (Finset.mem_univ u) -- need mem

omit hp hb hl ht hh hL hB hB0 hs in
lemma Blanket.reveal (hf:Blanket u x (2*C.S.a b) (2*C.S.a l)): Injective x:=by
   intro i j h; by_contra H; have h':=hf.cost _ _ H; rw [h,sub_self,norm_zero] at h'; nlinarith [C.S.a_pos l]
omit [DecidableEq ι] hp hb hl ht hh hL hB hB0 hs in
lemma watch_dense {k:ℕ} : ∃ᶠ y in 𝓝 x, ∃ (m:ℕ),k ≤ m ∧ ∃ z:ι→ Cover, y=C.S.gridPoint m ∘ z ∧ clear ι y:= by
   classical
   let f:= Fintype.equivFin ι; let X:= points (x ∘ f.symm)
   let p(y:Points (Fintype.card ι))(i:ι):= y (f i)
   have hp : Continuous p:= continuous_pi (fun i=> by dsimp only [p]; fun_prop)
   have he : p X=x:= funext (fun i=> congrArg x (f.symm_apply_apply i))
   have ht : Tendsto p (𝓝 X) (𝓝 x):= he ▸ hp.continuousAt
   apply ht.frequently -- check Type (freq application?)
   refine (Next.UVStress.meets_grid C X).mono ?_
   rintro y ⟨hY,j,v,rfl⟩
   refine ⟨max k j, le_max_left ..,Next.UVStress.pushSite C.S (le_max_right k j)∘ v ∘ f,?_,?_⟩
   · ext1 i; exact (Next.UVStress.finer C.S (le_max_right k j) (v (f i))).symm
   exact clear_maps (x:=WithLp.ofLp (Extraction.Order.grid C j v)) hY f.injective
omit [DecidableEq ι] hp hb hl ht hh hL hB hB0 hs in
lemma cont_sample (S:Table C.book)(h:S.Smooth)(hx:Injective x): ContDiffAt ℝ ∞ (fun y=> sample S y w) x:=by
   classical
   let f:= (Fintype.equivFin ι).symm; 
   let W : (ι→ E4)→ₗ[ℝ] Points (Fintype.card ι) := { toFun:=fun x=> points (x ∘ f), map_add':=fun _ _=> rfl, map_smul':=fun _ _=>rfl}
   have hC : Continuous (fun x:ι→ E4=> points (x ∘ f)):= by
       let L:= PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin (Fintype.card ι)=> E4); apply L.symm.continuous.comp (continuous_pi fun i=>?_); exact continuous_apply _
   let U : (ι→ E4) →L[ℝ] Points (Fintype.card ι):= { W with cont:= hC }; have hY: U x ∈ conf _:= hx.comp f.injective
   exact (((S.smooth_read h (w ∘ f)) _ hY).contDiffAt ((conf_open _).mem_nhds hY)).comp (f:=U) x U.contDiff.contDiffAt
omit hp hb hl ht hh hL hB hB0 hs in
lemma Blanket.near {b l:ℝ}(h: Blanket u x b l): ∀ᶠ y in 𝓝 x, Blanket u y b l:=by
   have he i j (a:ℝ)(h:a<‖x i-x j‖): ∀ᶠ (y:ι→ E4) in 𝓝 x, a<‖y i-y j‖:= (show Continuous (fun y:ι→ E4=> ‖y i-y j‖) by fun_prop).continuousAt.eventually (lt_mem_nhds h)
   filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr fun hE=> he i u b (h.side i hE), eventually_all.mpr fun i=> eventually_all.mpr fun j=> eventually_all.mpr fun hE=> he i j l (h.cost i j hE)] with i hi he
   exact ⟨hi,he⟩
lemma budget (hx: Blanket u x (2*C.S.a b) (2*C.S.a l)): ‖sample (watches X v) x w‖ ≤ ∏ i,B i:= by
   let Z:= watches X v; let H:= watched_kernel X v; apply le_of_tendsto_of_frequently (x:=𝓝 x) ((cont_sample w x Z H.smooth (Blanket.reveal u x hx)).continuousAt.norm)
   apply (((watch_dense (C:=C) (k:=b) x).and_eventually (Blanket.near u x hx)).mono); rintro _ ⟨⟨q,hZ,y,rfl,hC⟩,hy⟩
   let z i:= y i-y u; let g:= C.S.gridPoint q; let p i:= g (z i); let f i:=g (y i); have he i : p i=f i-g (y u):= by ext; simp [p,f,g,z,Schedule.gridPoint,mul_sub]
   have htop:p=fun i=> f i+ (-g (y u)):= funext fun i=> by rw [he,sub_eq_add_neg]
   have hb':p u=0:=by rw [he]; exact sub_self _
   have hs' i j:p i-p j=f i-f j:= by rw [he,he]; abel
   have hi:clear ι p:= by intro a i j hx; simp_rw [he i,he j,PiLp.sub_apply] at hx; exact hC a (sub_left_inj.mp hx)
   -- curr Main bound
   have hw:Blanket u p (2*C.S.a b) (2*C.S.a l):= by refine ⟨fun i h=>by rw [hs']; exact hy.side _ h,fun i j h=>by rw [hs']; exact hy.cost _ _ h⟩
   have hV : ‖sample Z p w‖ ≤ ∏ i,B i:= budget_grid X hp v u w z B hb hl ht -- shadow
        hh hL hB0 hB hs hZ (sub_self _) hi hw
   rw [htop,shifts Z f w (clear_inj f hC) H.translations] at hV; exact hV
end YM.Contacts.Sensor
